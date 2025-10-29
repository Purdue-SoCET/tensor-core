`include "caches_pkg.vh"

module memory_arbiter_basic(
  input logic CLK, nRST,
  arbiter_caches_if.cc acif,
  scratchpad_if.arbiter spif
);

  import caches_pkg::*;

  // WAIT SIGNALS
  logic sp_wait;

  // State definitions
  typedef enum logic [2:0] {
      IDLE     = 3'b000,
      SP_LOAD  = 3'b001,
      SP_STORE = 3'b010,
      DCACHE   = 3'b011,
      ICACHE   = 3'b100
  } arbiter_states;

  arbiter_states arbiter_state, next_arbiter_state;

  always_ff @ (posedge CLK, negedge nRST) begin
    if(!nRST) begin
      arbiter_state <= IDLE;
    end
    else begin
      arbiter_state <= next_arbiter_state;
    end
  end

  //NEXT STATE LOGIC
  always_comb begin
    next_arbiter_state = arbiter_state;
    case(arbiter_state)
      IDLE: begin
        if(spif.sLoad) next_arbiter_state = SP_LOAD;
        else if(spif.sStore) next_arbiter_state = SP_STORE;
        else if(acif.dREN || acif.dWEN) next_arbiter_state = DCACHE;
        else if(acif.iREN) next_arbiter_state = ICACHE;
      end

      SP_LOAD: begin
        next_arbiter_state = IDLE;
      end

      SP_STORE: begin
        next_arbiter_state = IDLE;
      end

      DCACHE: begin
        if (acif.dwait) begin
          next_arbiter_state = DCACHE;
        end
        else begin
          next_arbiter_state = IDLE;
        end
      end

      ICACHE: begin
        if (acif.iwait) begin
          next_arbiter_state = ICACHE;
        end
        else begin
          next_arbiter_state = IDLE;
        end
      end
    endcase
  end

  //OUTPUT LOGIC
  always_comb begin
    acif.ramstore = '0;
    acif.ramaddr = '0;
    acif.ramWEN = '0;
    acif.ramREN = '0;
    acif.dwait = '0;
    acif.dload = '0;
    acif.iwait = '0;
    acif.iload = '0;
    spif.load_data = '0;
    spif.sLoad_hit = '0;
    spif.sStore_hit = '0;
    spif.sLoad_row = '0;
    case(arbiter_state)
      SP_LOAD: begin
        sp_wait = spif.sLoad;
        acif.ramaddr = spif.load_addr;
        acif.ramREN = spif.sLoad;
        spif.load_data = acif.ramload;
        spif.sLoad_hit = 1'b1;
      end

      SP_STORE: begin
        sp_wait = spif.sStore;
        acif.ramstore = spif.store_data;
        acif.ramaddr = spif.store_addr;
        acif.ramWEN = spif.sStore;
        spif.sStore_hit = 1'b1;
        spif.sLoad_row = spif.sLoad_row + 1;
        if(spif.sLoad_row == 3'd5)begin
          spif.sLoad_row = 3'd1;
        end
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
