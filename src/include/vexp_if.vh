/*
    Chase Johnson
    Interface signals for add/sub vector module
*/

`ifndef VEXP_IF_VH
`define VEXP_IF_VH
`include "vector_types.vh"
`include "vector_if.vh"

interface vexp_if;
    import vector_pkg::*;

    //Inputs for Vector Exp Module
    logic[15:0] port_a, out;
    logic enable;

    
    modport vexp (
        input port_a, enable,
        output out //neg
    );

    modport tb (
        input out, //neg,
        output port_a, enable
    );

endinterface
`endif

