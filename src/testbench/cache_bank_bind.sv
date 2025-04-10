`include "cache_types_pkg.svh"

module confirm_replacement_mshr (
    input logic CLK,
    input logic nRST,
    input logic [3:0] curr_state, 
    input logic [BLOCK_OFF_BIT_LEN-1:0] count_FSM,
    input logic [BLOCK_OFF_BIT_LEN-1:0] next_count_FSM,
    input logic [BLOCK_INDEX_BIT_LEN-1:0] latched_victim_set_index,
    input logic [WAYS_LEN-1:0] latched_victim_way_index,
    input cache_set [NUM_SETS_PER_BANK-1:0] bank, 
    input cache_frame latched_block_pull_buffer,
    input mshr_reg mshr_entry
);

  property block_pull_replacement;
    @(posedge CLK) disable iff (!nRST)
    ((curr_state == VICTIM_EJECT) && (count_FSM == (BLOCK_SIZE - 1) && (next_count_FSM == 0))) |=> 
      ## 2 (bank[$past(latched_victim_set_index, 2)][$past(latched_victim_way_index, 2)] === $past(latched_block_pull_buffer, 2));
  endproperty

  assert property (block_pull_replacement)
      else $error("ASSERTIONERROR: Block not replaced properly, ");

endmodule

module confirm_replacement_singlecycle (
    input logic CLK,
    input logic nRST,
    input in_mem_instr mem_instr_in, 
    input logic scheduler_hit, 
    input logic [BLOCK_INDEX_BIT_LEN-1:0] set_index,
    input logic [WAYS_LEN-1:0] hit_way_index, 
    input cache_set [NUM_SETS_PER_BANK-1:0] bank
);

  property write_replacement;
    @(posedge CLK) disable iff (!nRST)
    (scheduler_hit && (mem_instr_in.rw_mode == 1)) |=> ( 
        bank[$past(set_index, 1)][$past(hit_way_index, 1)].block[$past(mem_instr_in.addr.block_offset, 1)] == $past(mem_instr_in.store_value, 1)
      );
  endproperty

  assert property (write_replacement)
    else $error("ASSERTIONERROR: Word not replaced properly within block");

endmodule 

module cache_bank_monitor (
  input logic CLK,
  input logic nRST,
  input cache_set [NUM_SETS_PER_BANK-1:0] bank, 
  input logic enable
);

  integer set, way;
  integer full_sets;
  integer dirty_sets;
  integer filled_ways;
  integer dirty_ways;

  always @(posedge CLK, negedge nRST) begin
    if (enable) begin
      full_sets = 0;
      dirty_sets = 0;
      for (set = 0; set < NUM_SETS_PER_BANK; set = set + 1) begin
        filled_ways = 0;
        dirty_ways = 0; 
        for (way = 0; way < NUM_WAYS; way = way + 1) begin
          if (bank[set][way].valid) filled_ways = filled_ways + 1;
          if (bank[set][way].dirty) dirty_ways = dirty_ways + 1;
        end
        
        $display("    Time %0t: Set %0d has (%0d filled ways) | (%0d dirty ways)", $time, set, filled_ways, dirty_ways);
        
        if (filled_ways == NUM_WAYS) begin 
          full_sets = full_sets + 1;
          dirty_sets = dirty_sets + 1;
        end
      end
      $display("Time %0t: (Total full sets: %0d) | (dirty sets: %0d) ", $time, full_sets, dirty_sets);
    end
  end

endmodule
