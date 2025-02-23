module memory_arbiter_basic(
  input logic CLK, nRST
);

  //TODO: TURN ALL OF THIS INTO AN INTERFACE
  // Outputs to scratchpad
  logic[63:0] load_data, next_load_data;
  logic       sLoad_hit, sStore_hit, next_sLoad_hit, next_sStore_hit;
  logic[1:0]  sLoad_row, next_sLoad_row;
  
  // Inputs to arbiter from scratchpad
  logic[63:0] store_data, next_store_data;
  logic[31:0] load_addr, store_addr, next_load_addr, next_store_addr;
  logic       sLoad, sStore, next_sLoad, next_sStore;

  // Inputs to arbiter from scheduler
  logic       dreq, ireq;
  // Outputs to scheduler

  //Main Memory Inputs & Outputs
  logic       ramstore, ramaddr, ramWEN, ramREN;
  logic       iwait, dwait, swait, iload, dload, sload;

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
      // Reset values for all signals
      arbiter_state <= IDLE;
      load_data <= 64'b0;
      sLoad_hit <= 1'b0;
      sStore_hit <= 1'b0;
      sLoad_row <= 2'b00;
      store_data <= 64'b0;
      load_addr <= 32'b0;
      store_addr <= 32'b0;
      sLoad <= 1'b0;
      sStore <= 1'b0;
    end
    else begin
      // Update state and signals based on next_ values
      arbiter_state <= next_arbiter_state;
      load_data <= next_load_data;
      sLoad_hit <= next_sLoad_hit;
      sStore_hit <= next_sStore_hit;
      sLoad_row <= next_sLoad_row;
      store_data <= next_store_data;
      load_addr <= next_load_addr;
      store_addr <= next_store_addr;
      sLoad <= next_sLoad;
      sStore <= next_sStore;
    end
  end



  //NEXT STATE LOGIC
  always_comb begin
    case(arbiter_state)
      IDLE: begin
        if(sLoad) begin
          next_arbiter_state = SP_LOAD;
        end
        else if(sStore) begin
          next_arbiter_state = SP_STORE;
        end
        else if(dreq) begin
          next_arbiter_state = DCACHE;
        end
        else if(ireq) begin
          next_arbiter_state = ICACHE;
        end
      end

      SP_LOAD: begin
        if(swait) begin
          next_arbiter_state = SP_LOAD;
        end
        else begin
          next_arbiter_state = IDLE;
        end
      end

      SP_STORE: begin
        if(swait) begin
          next_arbiter_state = SP_STORE;
        end
        else begin
          next_arbiter_state = IDLE;
        end
      end

      DCACHE: begin
        if(dwait) begin
          next_arbiter_state = DCACHE;
        end
        else begin
          next_arbiter_state = IDLE;
        end
      end

      ICACHE: begin
        if(iwait) begin
          next_arbiter_state = ICACHE;
        end
        else begin
          next_arbiter_state = IDLE;
        end
      end
    endcase
  end



  //TODO: COMMUNICATION WITH OTHER MODULES
  //OUTPUT LOGIC
  always_comb begin
    next_load_data = '0;
    next_sLoad_hit = '0;
    next_sStore_hit = '0;
    next_sLoad_row = '0;
    next_store_data = '0;
    next_load_addr = '0;
    next_store_addr = '0;
    next_sLoad = '0;
    next_sStore = '0;
    case(arbiter_state)
      IDLE: begin
        if(sLoad) begin
          next_load_addr = load_addr;
        end
        else if(sStore) begin
          next_arbiter_state = SP_STORE;
        end
        else if(dreq) begin
          next_arbiter_state = DCACHE;
        end
        else if(ireq) begin
          next_arbiter_state = ICACHE;
        end
      end

      SP_LOAD: begin
        load_data = ramload; //TODO
        next_sLoad_row = next_sLoad_row + 1;
        
      end

      SP_STORE: begin
      
      end

      DCACHE: begin
      
      end

      ICACHE: begin
      
      end
    endcase
  end

endmodule
