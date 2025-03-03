`include "cache_types_pkg.svh"

module confirm_lru_age (
    input logic CLK, 
    input lru_frame [NUM_SETS_PER_BANK-1:0] lru
);

  always @ (posedge CLK) begin 
    for (int set = 0; set < NUM_SETS_PER_BANK; set++) begin
      for (int j = 0; j < NUM_WAYS; j++) begin
        assert (lru[set].age[lru[set].lru_way] >= lru[set].age[j])
          else $error("LRU violation at set %0d: way %0d (age=%0d) is less than way %0d (age=%0d)",
                      set,  lru[set].lru_way, lru[set].age[lru[set].lru_way], j, lru[set].age[j]);
      end
    end
  end

endmodule

