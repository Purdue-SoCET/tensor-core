`ifndef EDGE_DET_IF
`define EDGE_DET_IF
`include "dram_command_if.vh"
interface edge_det_if ();
    
    
    logic async_in, sync_out, edge_flag;

    modport edge_mod (
        input async_in,
        output sync_out, edge_flag
    );    

endinterface


`endif
