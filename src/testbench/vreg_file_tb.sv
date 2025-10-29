`include "vector_if.vh"
`include "vector_types.vh"

module vreg_file_tb;
  import vector_pkg::*;

  // Clocking
  localparam int CLK_PERIOD = 10; // 100 MHz

  // 1) Interface
  vector_if vif();

  // 2) DUT: vreg_file (uses the vregfile modport)
  vreg_file dut (
    .vif(vif)
  );

  // 3) Clock gen
  always #(CLK_PERIOD/2) vif.CLK = ~vif.CLK;

  // ---------------------------
  // Utility tasks (same API as your veggie_tb)
  // ---------------------------
  task reset_dut();
    begin
      vif.CLK      = 1'b0;
      vif.nRST     = 1'b0;          // assert reset
      vif.iready   = 1'b1;          // allow buffer to pass through by default
      vif.veggie_in = '{default:'0}; // quiet inputs during reset
      repeat (5) @(posedge vif.CLK);
      vif.nRST = 1'b1;              // deassert reset
      @(posedge vif.CLK);
    end
  endtask

  task automatic veggie_set_reads(
      input vsel_t vs_by_port   [READ_PORTS],
      input bit    ren_by_port  [READ_PORTS] = '{default:1'b1}
  );
    foreach (vs_by_port[i]) begin
      vif.veggie_in.vs [i] = vs_by_port[i];
      vif.veggie_in.REN[i] = ren_by_port[i];
    end
  endtask

  task automatic veggie_set_writes(
      input vsel_t vd_by_port     [WRITE_PORTS],
      input vreg_t vdata_by_port  [WRITE_PORTS],
      input bit    wen_by_port    [WRITE_PORTS]
  );
    foreach (vd_by_port[i]) begin
      vif.veggie_in.vd   [i] = vd_by_port[i];
      vif.veggie_in.vdata[i] = vdata_by_port[i];
      vif.veggie_in.WEN  [i] = wen_by_port[i];
    end
  endtask

  task automatic veggie_set_mask_reads(
      input mask_sel_t vms_by_port [MASK_BANK_COUNT],
      input bit        mren_by_port[MASK_BANK_COUNT] = '{default:1'b1}
  );
    foreach (vms_by_port[i]) begin
      vif.veggie_in.vms [i]  = vms_by_port[i];
      vif.veggie_in.MREN[i]  = mren_by_port[i];
    end
  endtask

  task automatic veggie_set_mask_writes(
      input mask_sel_t        vmd_by_port   [MASK_BANK_COUNT],
      input logic [VLMAX-1:0] mvdata_by_port[MASK_BANK_COUNT],
      input bit               mwen_by_port  [MASK_BANK_COUNT] = '{default:1'b0}
  );
    foreach (vmd_by_port[i]) begin
      vif.veggie_in.vmd   [i] = vmd_by_port[i];
      vif.veggie_in.mvdata[i] = mvdata_by_port[i];
      vif.veggie_in.MWEN  [i] = mwen_by_port[i];
    end
  endtask

  // ---------------------------
  // Stimulus
  // ---------------------------
  initial begin
    string testname;

    $display("=====================================================");
    $display("vreg_file Testbench Starting...");
    $display("=====================================================");

    // Reset
    testname = "Reset";
    reset_dut();

    // -------------------------------------------------
    // TEST 0: Writes w/ no conflicts + mask writes
    // -------------------------------------------------
    testname = "Writing with no Conflict";
    veggie_set_writes('{ 8'h08, 8'h09, 8'h0A, 8'h0B }, '{ '1, '0, '1, '0 }, '{ 1, 1, 1, 1 });
    veggie_set_mask_writes('{ 4'h0, 4'h1 }, '{ 32'hFFFF_FFFF, 32'h0000_0000 }, '{ 1, 1 });
    #(50);

    // -------------------------------------------------
    // TEST 1: Simple reads (and mask reads)
    // -------------------------------------------------
    testname = "Read Testing";
    vif.veggie_in.WEN  = '{default:1'b0};
    vif.veggie_in.MWEN = '{default:1'b0};

    veggie_set_reads('{ 8'h08, 8'h09, 8'h0A, 8'h0B }, '{ 1, 1, 1, 1 });
    veggie_set_mask_reads('{ 4'h0, 4'h1 }, '{ 1, 1 });
    #(30);

    // Optional: peek post-buffer outputs (use opbuff_out)
    $display("[READ] dvalid=%b mvalid=%b",
             vif.opbuff_out.ivalid, /* note: ivalid per mask pair */
             /* mvalid is internal to veggie_out; opbuff_out only carries ivalid + data */
             '0);

    // Re-reset
    testname = "Reset";
    reset_dut();

    // -------------------------------------------------
    // TEST 2: Writes that create conflicts
    // -------------------------------------------------
    testname = "Writing with Conflicts";
    veggie_set_writes('{ 8'h00, 8'h04, 8'h08, 8'h0C }, '{ '1, '1, '0, '1 }, '{ 1, 1, 1, 1 });
    veggie_set_mask_writes('{ 4'h2, 4'h4 }, '{ 32'hCAFE_BABE, 32'hCAFE_F00D }, '{ 1, 1 });
    #(40);
    vif.veggie_in.WEN  = '{default:1'b0};
    vif.veggie_in.MWEN = '{default:1'b0};

    // -------------------------------------------------
    // TEST 3: Reads that create conflicts
    // -------------------------------------------------
    testname = "Reading with Conflicts";
    veggie_set_reads('{ 8'h00, 8'h04, 8'h08, 8'h0C }, '{ 1, 1, 1, 1 });
    veggie_set_mask_reads('{ 4'h2, 4'h4 }, '{ 1, 1 });
    #(120);

    // Example: simple check that some data returned (post-buffer)
    // (Tight correctness checks depend on your bank scheduling latency/ordering.)
    if (^vif.opbuff_out.vreg[0] === 1'bx) begin
      $display("[INFO] Output on vreg[0] is X (may be fine depending on timing).");
    end

        // -------------------------------------------------
    // TEST 4: Half Write - No Conflict
    //   Use two data write ports + one mask write, choose rows that map to different data banks
    // -------------------------------------------------
    testname = "Half Write - No Conflict";
    // data: ports 0..1 active, 2..3 idle
    veggie_set_writes('{ 8'h01, 8'h02, 8'h00, 8'h00 }, '{ '1, '0, '0, '0 }, '{ 1, 1, 0, 0 });
    // mask: write only bank 0 side (index even -> bank 0 when MASK_BANK_IDX=1)
    veggie_set_mask_writes('{ 4'h0, 4'h0 }, '{ 32'hA5A5_A5A5, '0 }, '{ 1, 0 });
    #(30);
    // clear ops
    vif.veggie_in.WEN  = '{default:1'b0};
    vif.veggie_in.MWEN = '{default:1'b0};

    // -------------------------------------------------
    // TEST 5: Half Read - No Conflict
    //   Read back the two rows + one mask
    // -------------------------------------------------
    testname = "Half Read - No Conflict";
    // data: ports 0..1 active, 2..3 idle
    veggie_set_reads('{ 8'h01, 8'h02, 8'h00, 8'h00 }, '{ 1, 1, 0, 0 });
    // mask: read only bank 0 side
    veggie_set_mask_reads('{ 4'h0, 4'h0 }, '{ 1, 0 });
    #(50);
    $display("[T5] ivalid=%b (expect 1 group valid when lane-pair & mask align)", vif.opbuff_out.ivalid);
    // clear ops
    vif.veggie_in.REN  = '{default:1'b0};
    vif.veggie_in.MREN = '{default:1'b0};

    // -------------------------------------------------
    // TEST 6: Half Write - Conflict
    //   Two writes targeting the same data bank (e.g., 0x00 & 0x04 -> both bank 0 when BANK_IDX=2)
    //   One mask write also into the same mask bank (even index -> bank 0)
    // -------------------------------------------------
    testname = "Half Write - Conflict";
    veggie_set_writes('{ 8'h00, 8'h04, 8'h00, 8'h00 }, '{ '1, '0, '0, '0 }, '{ 1, 1, 0, 0 });
    // two mask indices that both map to bank 0 (even LSB -> bank 0)
    veggie_set_mask_writes('{ 4'h2, 4'h6 }, '{ 32'hDEAD_BEEF, '0 }, '{ 1, 0 });
    #(60);
    // clear ops
    vif.veggie_in.WEN  = '{default:1'b0};
    vif.veggie_in.MWEN = '{default:1'b0};

    // -------------------------------------------------
    // TEST 7: Half Read - Conflict
    //   Read back the conflicted rows + mask; expect serialized service
    // -------------------------------------------------
    testname = "Half Read - Conflict";
    veggie_set_reads('{ 8'h00, 8'h04, 8'h00, 8'h00 }, '{ 1, 1, 0, 0 });
    veggie_set_mask_reads('{ 4'h2, 4'h6 }, '{ 1, 0 });
    #(120);
    $display("[T7] ivalid=%b (expect serialized valid for the conflicted group)", vif.opbuff_out.ivalid);
    // clear ops
    vif.veggie_in.REN  = '{default:1'b0};
    vif.veggie_in.MREN = '{default:1'b0};

    // -------------------------------------------------
    // TEST 8: Max Bit Coverage
    //   Sweep writes/reads over many rows on a single port to touch indices broadly
    //   (keeps conflicts low; good smoke for address slicing & bank mapping)
    // -------------------------------------------------
    testname = "Max Bit Coverage - Writes";
    for (int row = 0; row < 32; row++) begin
      // single-port write on port 0
      veggie_set_writes('{ row[VIDX_W-1:0], '0, '0, '0 }, '{ (row[0]) ? '1 : '0, '0, '0, '0 }, '{ 1, 0, 0, 0 });
      #(10);
      vif.veggie_in.WEN  = '{default:1'b0};
    end

    testname = "Max Bit Coverage - Reads";
    for (int row = 0; row < 32; row++) begin
      // single-port read on port 0
      veggie_set_reads('{ row[VIDX_W-1:0], '0, '0, '0 }, '{ 1, 0, 0, 0 });
      #(20);
      $display("[T8][row %0d] ivalid=%b vreg0[15:0]=%h",
               row, vif.opbuff_out.ivalid, vif.opbuff_out.vreg[0][0]);
      vif.veggie_in.REN  = '{default:1'b0};
    end


    $display("\n=====================================================");
    $display("TB complete.");
    $display("=====================================================");
    $stop;
  end

endmodule
