`include "cache_types_pkg.svh"

module confirm_uuid (
    input logic CLK,
    input logic nRST,
    input logic miss, 
    input logic [UUID_SIZE-1:0] uuid_out,
    input logic [UUID_SIZE-1:0] uuid
);

  property proper_uuid_update;
    @(posedge CLK) disable iff (!nRST)
    miss |-> 
        (uuid_out == ($past(uuid) + 1));
  endproperty

  assert property (proper_uuid_update)
    else $error("ASSERTIONERROR: UUID sent out on miss was not incremented properly");

endmodule 