module gsau_control_unit #(
    parameter VEGGIEREGS = 256,
    parameter FIFOSIZE = 32*3*8
) (
    input logic CLK, nRST,
    gsau_if.gsau gsau_port
);

// --- queue configuration: 8-bit entries (vdst indexes are 8-bit in your IF)
  localparam int QUEUE_WIDTH = 8;
  localparam int QUEUE_DEPTH = (FIFOSIZE / QUEUE_WIDTH); // e.g. 768/8 = 96 entries
  localparam int PTR_W = $clog2(QUEUE_DEPTH);

  // --- internal queue signals
  logic [QUEUE_WIDTH-1:0] queue_mem [0:QUEUE_DEPTH-1];
  logic [PTR_W-1:0]       q_wptr, q_rptr;
  logic [PTR_W:0]         q_count; // one extra bit to detect full
  logic                   q_wr_en, q_rd_en;
  logic [QUEUE_WIDTH-1:0] q_din;
  logic [QUEUE_WIDTH-1:0] q_dout;
  logic                   q_empty, q_full;

  // --- one-cycle strobes (internal)
  logic veg_accept_strobe;   // veggie data accepted and forwarded to SA
  logic sa_send_weight;      // latched weight flag for the accepted veggie
  logic wb_issue_strobe;     // we issued writeback to WB buffer
  logic sa_stall;            // for systolic array to stall

  // --- registers to hold outputs to WB when SA produces an output
  logic [511:0] wb_psum_r;
  logic [7:0]   wb_wbdst_r;
  logic         wb_valid_r;

  // -------------------------------------------------------------------------
  // simple synchronous FIFO (vdst indices)
  // - enqueue on q_wr_en
  // - dequeue on q_rd_en
  // -------------------------------------------------------------------------
  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      q_wptr <= '0;
      q_rptr <= '0;
      q_count <= '0;
    end else begin
      // write
      if (q_wr_en && !q_full) begin
        queue_mem[q_wptr] <= q_din;
        q_wptr <= q_wptr + 1;
      end
      // read
      if (q_rd_en && !q_empty) begin
        q_rptr <= q_rptr + 1;
      end

      // count update (synchronous)
      case ({q_wr_en && !q_full, q_rd_en && !q_empty})
        2'b10: q_count <= q_count + 1;
        2'b01: q_count <= q_count - 1;
        default: q_count <= q_count;
      endcase
    end
  end

  // read data output always (combinational read of memory at rptr)
  // Note: synthesizable read depends on inferred memory; keep combinational read for clarity.
  always_comb begin
    q_dout = queue_mem[q_rptr];
  end

  assign q_empty = (q_count == 0);
  assign q_full  = (q_count == QUEUE_DEPTH);

  // -------------------------------------------------------------------------
  // Scoreboard handshake: accept next-dest when queue not full.
  // scoreboard signals (from interface):
  //   input  sb_nready, sb_nvdst, sb_nvalid, sb_weight    <-- these are inputs into GSAU modport
  // GSAU should drive sb_ready when it can accept next dest
  // -------------------------------------------------------------------------
  // sb_ready: assert whenever queue has space
  always_comb begin
    // allow scoreboard to send next-dest if we have space
    gsau_port.sb_ready = ~q_full;
  end

  // capture scoreboard next-dest into q_din on valid+ready (one-cycle)
  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      q_din <= '0;
      q_wr_en <= 1'b0;
      sa_send_weight <= 1'b0;
    end else begin
      q_wr_en <= 1'b0; // default
      sa_send_weight <= 1'b0;
      if (gsau_port.sb_nvalid && gsau_port.sb_ready) begin
        q_din <= gsau_port.sb_nvdst;    // enqueue next dest
        q_wr_en <= 1'b1;
        sa_send_weight <= gsau_port.sb_weight; // latch weight indicator if user needs to use it when sending to SA
      end
    end
  end

  // -------------------------------------------------------------------------
  // Veggie -> Systolic Array forwarding logic (decoupled)
  // When veggie provides vector data (veg_valid), we accept if SA has FIFO space.
  // On accept: assert veg_ready (so veggie pushes next vector), drive sa_array_in and sa_input_en.
  // sa_weight_en is asserted according to latched sb_weight for that instruction (simple model).
  // -------------------------------------------------------------------------
  // Drive veg_ready combinationally when ready to accept
  always_comb begin
    // we accept veggie data if SA has room and we aren't currently holding a transfer
    // note: we assume the sa_fifo_has_space indicates SA can take activations
    gsau_port.veg_ready = gsau_port.sa_fifo_has_space;
  end

  // Transfer veggie data into SA control signals (registered)
  // We'll use a one-cycle accept strobe: accept when veg_valid && veg_ready.
  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      veg_accept_strobe <= 1'b0;
      gsau_port.sa_array_in <= '0;
      gsau_port.sa_input_en <= 1'b0;
      gsau_port.sa_weight_en <= 1'b0;
      gsau_port.sa_array_in_partials <= '0;
      gsau_port.sa_partial_en <= 1'b0;
    end else begin
      // default deassert strobes
      veg_accept_strobe <= 1'b0;
      gsau_port.sa_input_en <= 1'b0;
      gsau_port.sa_weight_en <= 1'b0;
      gsau_port.sa_partial_en <= 1'b0;

      if (gsau_port.veg_valid && gsau_port.veg_ready) begin
        // capture vector data into SA inputs (forward directly)
        gsau_port.sa_array_in <= gsau_port.veg_vdata;
        gsau_port.sa_input_en <= 1'b1;
        // if the scoreboard indicated this was a weight load, assert weight_en for this transfer
        if (sa_send_weight) begin
          gsau_port.sa_weight_en <= 1'b1;
        end else begin
          gsau_port.sa_weight_en <= 1'b0;
        end
        // for now, no partial sum load on normal veggie transfers; user can refine later
        gsau_port.sa_partial_en <= 1'b0;

        veg_accept_strobe <= 1'b1;
      end else begin
        // drive data lines to 0 when not sending (avoids X)
        gsau_port.sa_array_in <= '0;
      end
    end
  end

  assign sa_stall = !gsau_port.wb_output_ready || !gsau_port.sa_fifo_has_space;

  // -------------------------------------------------------------------------
  // Systolic Array -> WB handshake: when SA asserts sa_out_en + data,
  // pop one vdst from queue and send writeback to WB buffer when it's ready.
  // If WB buffer isn't ready, hold the writeback until it becomes ready (backpressure).
  // -------------------------------------------------------------------------
  // We'll implement a small state to hold SA output until WB can accept it.
  typedef enum logic [1:0] {WB_IDLE=2'b00, WB_WAIT=2'b01, WB_HOLD=2'b10} wb_state_t;
  wb_state_t wb_state;

  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      wb_state <= WB_IDLE;
      q_rd_en <= 1'b0;
      wb_valid_r <= 1'b0;
      wb_psum_r <= '0;
      wb_wbdst_r <= '0;
    end else begin
      // default
      q_rd_en <= 1'b0;
      wb_issue_strobe <= 1'b0;
      wb_valid_r <= 1'b0;

      case (wb_state)
        WB_IDLE: begin
          // If SA output is valid and we have something in queue -> prepare writeback
          if (gsau_port.sa_out_en && !q_empty) begin
            // latch psum and prepare to pop vdst
            wb_psum_r <= gsau_port.sa_array_output;
            wb_wbdst_r <= q_dout;
            // we will pop the queue and attempt to send to WB buffer
            // but only actually pop when WB buffer accepts (so we don't lose vdst)
            if (gsau_port.wb_output_ready) begin
              // can both pop and send this cycle
              q_rd_en <= 1'b1;
              wb_valid_r <= 1'b1;
              wb_issue_strobe <= 1'b1;
              wb_state <= WB_IDLE; // remain idle ready for next
            end else begin
              // cannot send yet, wait until WB buffer ready
              wb_state <= WB_WAIT;
            end
          end
        end

        WB_WAIT: begin
          // waiting for WB buffer to become ready; when it does, pop queue and assert wb_valid
          if (gsau_port.wb_output_ready) begin
            q_rd_en <= 1'b1;
            wb_valid_r <= 1'b1;
            wb_issue_strobe <= 1'b1;
            wb_state <= WB_IDLE;
          end else begin
            wb_state <= WB_WAIT;
          end
        end

        default: wb_state <= WB_IDLE;
      endcase
    end
  end

  // drive outputs to WB buffer (registered)
  always_comb begin
    gsau_port.wb_psum   = wb_psum_r;
    gsau_port.wb_wbdst  = wb_wbdst_r;
    gsau_port.wb_valid  = wb_valid_r;
  end
    
endmodule