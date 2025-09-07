/*
    Chase Johnson
    Interface signals for add/sub vector module
*/

`ifndef VADDSUB_IF_VH
`define VADDSUB_IF_VH
`include "vector_types.vh"
`include "vector_if.vh"

interface vaddsub_if;
    import vector_pkg::*;

    //Inputs from Vector ALU
    logic[15:0] port_a, port_b, out; //16 bit inputs and outputs
    logic sub, enable, overflow; //control signal to determine add or subtract and enable signal

    
    modport vaddsub (
        input port_a, port_b, sub, enable,
        output out, overflow
    );

endinterface
`endif

