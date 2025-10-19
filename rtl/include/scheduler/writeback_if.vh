/*
    Interface signals for the Writeback Module
*/

`ifndef WRITEBACK_IF_VH
`define WRITEBACK_IF_VH
`include "datapath_types.vh"
`include "isa_types.vh"

interface writeback_if;
    import datapath_pkg::*;
    import isa_pkg::*;

    // Inputs from Functional Units
    // ALU_out, alu_done
    // Scalar_load, L/S done
    word_t alu_out, dmemload;
    logic load_ready, alu_ready;
    regbits_t reg_sel_alu, reg_sel_load;

    // Possible other done flags? 
    // Outputs of stage
    wb_t wb_out;
    
    modport wb (
        input alu_out, dmemload, load_ready, alu_ready, reg_sel_alu, reg_sel_load,
        output wb_out
    );

endinterface
`endif

