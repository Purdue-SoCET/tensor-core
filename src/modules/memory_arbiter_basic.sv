`include "caches_pkg.vh"

module memory_arbiter_basic(
  input logic CLK, nRST,
  arbiter_caches_if.cc acif,
  scratchpad_if.arbiter spif
);

  import caches_pkg::*;

  logic [31:0] global_stride = 32'd8;
  logic [1:0] load_count, next_load_count;
  logic [1:0] store_count, next_store_count;
  logic [2:0] sLoad_row_reg, next_sLoad_row_reg;
  logic sp_wait;

  typedef enum logic [3:0] {
      IDLE      = 4'b0000,
      SP_LOAD1  = 4'b0001,
      SP_LOAD2  = 4'b0010,
      SP_STORE1 = 4'b0011,
      SP_STORE2 = 4'b0100,
      DCACHE    = 4'b0101,
      ICACHE    = 4'b0110
  } arbiter_states;

  arbiter_states arbiter_state, next_arbiter_state;

  always_ff @ (posedge CLK, negedge nRST) begin
    if (!nRST) begin
      arbiter_state <= IDLE;
      load_count <= '0;
      store_count <= '0;
      sLoad_row_reg <= 3'd0;
    end
    else begin
      arbiter_state <= next_arbiter_state;
      load_count <= next_load_count;
      store_count <= next_store_count;
      sLoad_row_reg <= next_sLoad_row_reg;
    end
  end

  always_comb begin
    next_arbiter_state = arbiter_state;
    next_load_count = load_count;
    next_store_count = store_count;
    next_sLoad_row_reg = sLoad_row_reg;
    case (arbiter_state)
      IDLE: begin
        if (spif.sLoad) begin
          next_arbiter_state = SP_LOAD1;
          next_load_count = '0;
          next_sLoad_row_reg = 3'd0;
        end
        else if (spif.sStore) begin
          next_arbiter_state = SP_STORE1;
          next_store_count = '0;
        end
        else if (acif.dREN || acif.dWEN) begin
          next_arbiter_state = DCACHE;
        end
        else if (acif.iREN) begin
          next_arbiter_state = ICACHE;
        end
      end
      SP_LOAD1: begin
        if (!spif.sLoad) begin
          next_arbiter_state = IDLE;
        end
        else if (!sp_wait) begin
          next_arbiter_state = SP_LOAD2;
        end
      end
      SP_LOAD2: begin
        if (!spif.sLoad) begin
          next_arbiter_state = IDLE;
        end
        else if (!sp_wait) begin
          next_sLoad_row_reg = load_count;
          if (load_count < 2'd3) begin
            next_arbiter_state = SP_LOAD1;
            next_load_count = load_count + 1;
          end
          else begin
            next_arbiter_state = IDLE;
            next_load_count = '0;
          end
        end
      end
      SP_STORE1: begin
        if (!spif.sStore) begin
          next_arbiter_state = IDLE;
        end
        else if (!sp_wait) begin
          next_arbiter_state = SP_STORE2;
        end
      end
      SP_STORE2: begin
        if (!spif.sStore) begin
          next_arbiter_state = IDLE;
        end
        else if (!sp_wait) begin
          if (store_count < 2'd3) begin
            next_arbiter_state = SP_STORE1;
            next_store_count = store_count + 1;
          end
          else begin
            next_arbiter_state = IDLE;
            next_store_count = '0;
          end
        end
      end
      DCACHE: begin
        // if (!(cif.dWEN || cif.dREN)) begin
        //   next_arbiter_state = IDLE;
        // end
        if (acif.dwait) next_arbiter_state = DCACHE;
        else next_arbiter_state = IDLE;
      end
      ICACHE: begin
        if (acif.iwait) next_arbiter_state = ICACHE;
        else next_arbiter_state = IDLE;
      end
    endcase
  end

  logic [63:0] load_data_reg;
  always_ff @(posedge CLK, negedge nRST) begin
    if (!nRST) begin
      load_data_reg <= '0;
    end
    else if (arbiter_state == SP_LOAD1 && !sp_wait) begin
      load_data_reg[31:0] <= acif.ramload;
    end
    else if (arbiter_state == SP_LOAD2 && !sp_wait) begin
      load_data_reg[63:32] <= acif.ramload;
    end
  end
  assign spif.load_data = load_data_reg;
  assign spif.sLoad_row = sLoad_row_reg;

  always_comb begin
    acif.ramstore = '0;
    acif.ramaddr = '0;
    acif.ramWEN = '0;
    acif.ramREN = '0;
    acif.dwait = '0;
    acif.dload = '0;
    acif.iwait = '0;
    acif.iload = '0;
    spif.sLoad_hit = '0;
    spif.sStore_hit = '0;
    sp_wait = 1'b0;

    case (arbiter_state)
      SP_LOAD1: begin
        sp_wait = acif.ramstate == BUSY;
        acif.ramaddr = spif.load_addr + (load_count * global_stride * 2);
        acif.ramREN = 1'b1;
      end
      SP_LOAD2: begin
        sp_wait = acif.ramstate == BUSY;
        acif.ramaddr = spif.load_addr + (load_count * global_stride * 2) + global_stride;
        acif.ramREN = 1'b1;
        if (!sp_wait) spif.sLoad_hit = 1'b1;
      end
      SP_STORE1: begin
        sp_wait = acif.ramstate == BUSY;
        acif.ramstore = spif.store_data[31:0];
        acif.ramaddr = spif.store_addr + (store_count * global_stride * 2);
        acif.ramWEN = 1'b1;
      end
      SP_STORE2: begin
        sp_wait = acif.ramstate == BUSY;
        acif.ramstore = spif.store_data[63:32];
        acif.ramaddr = spif.store_addr + (store_count * global_stride * 2) + global_stride;
        acif.ramWEN = 1'b1;
        if (!sp_wait) spif.sStore_hit = 1'b1;
      end
      DCACHE: begin
        acif.ramstore = acif.dstore;
        acif.ramaddr = acif.daddr;
        acif.ramWEN = acif.dWEN;
        acif.ramREN = !acif.dWEN && acif.dREN;
        acif.dwait = ((acif.dREN && acif.ramstate == ACCESS) || (acif.dWEN && acif.ramstate == ACCESS)) ? 1'b0 : 1'b1;
        acif.dload = acif.ramload;
      end
      ICACHE: begin
        acif.ramaddr = acif.iaddr;
        acif.iload = acif.ramload;
        acif.iwait = (acif.ramstate == BUSY || acif.dREN || acif.dWEN) ? 1'b1 : 1'b0;
      end
    endcase
  end
endmodule