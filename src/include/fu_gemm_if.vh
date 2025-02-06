`ifndef FU_GEMM_IF_VH
`define FU_GEMM_IF_VH
`include "isa_types.vh"
`include "datapath_types.vh"

interface fu_gemm_if;
    import isa_pkg::*;
    import datapath_pkg::*;

    //Inputs from fetch
    logic [31:0] fetch_p; //from fetch instruction
    
    //These would be outputs from the GEMM function
    matbits_t rs1, rs2, rs3, rd; //tells the systolic array which values to multiply together
    matbits_t weight1, weight2, weight3, weightd;

    //Inputs to latch
    logic flush, freeze;
    
    modport GEMM (
        input fetch_p, flush, freeze, weight1, weight2, weigh3, weightd,
        output rs1, rs2, rs3, rd
    );

    modport tb (
        input rs1, rs2, rs3, rd,
        output fetch_p, flush, freeze, weight1, weight2, weigh3, weightd
    );

endinterface
`endif
