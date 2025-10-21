/*
  Saandiya, Myles, Nikhil
  mohan76@purdue.edu, mquerimi@purdue.edu, nvaidyan@purdue.edu

  GSAU Interface V1
*/

`ifndef GSAU_CONTROL_UNIT_IF_VH
`define GSAU_CONTROL_UNIT_IF_VH

`include "sys_arr_pkg.vh"
`include "vector_pkg.vh"

interface gsau_control_unit_if;
  import vector_pkg::*;   // reuse basic typedefs (data, addr, etc.)
  import sys_arr_pkg::*;  // systolic-specific typedefs

  ////////////////////////////////////////////////////////////////////////////
  ////////////////////////////// Types ///////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////////


  ////////////////////////////////////////////////////////////////////////////
  /////////////////////////////// Signals ////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////////

    // VEGGIE FILE
    // From Veggie File to GSAU
    vreg_t        veg_vdata1;         // [512 bits] vector data vs1
    vreg_t        veg_vdata2;         // [512 bits] vector data vs2
    logic         veg_valid;         // indicates vdata valid

    // From GSAU to Veggie File
    logic         veg_ready;        // indicates ready for value

    // SCOREBOARD 
    // From GSAU to Scoreboard
    logic         sb_ready;         // ready to accept next instruction
  
    // From Scoreboard to GSAU
    logic [7:0]   sb_vdst;         // next destination reg
    logic         sb_valid;       // next scoreboard valid
    logic         sb_weight;        // 1 bit signal for weight indication

    // WB BUFFER
    // From GSAU to WB Buffer
    vreg_t        wb_psum;          // partial sum output
    logic [7:0]   wb_wbdst;         // destination vector register for writeback
    logic         wb_valid;      // valid signal for psum output

    // From WB Buffer to GSAU
    logic         wb_output_ready;  // WB buffer ready to accept data

    // SYSTOLIC ARRAY 
    // To Systolic Array
    logic [511:0] sa_array_in;          // input data to systolic array
    logic [511:0] sa_array_in_partials; // partial sum inputs
    logic         sa_input_en;          // enable data input
    logic         sa_weight_en;         // enable weight load
    logic         sa_partial_en;        // enable partial sum load
    logic         sa_output_ready;       // ready to accept output data

    // From Systolic Array
    logic [511:0] sa_array_output;      // output data
    logic         sa_out_valid;            // output valid flag
    logic         sa_fifo_has_space;    // to send activations

  ////////////////////////////////////////////////////////////////////////////
  ////////////////////////////// Modports ////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////////

    //GSAU 
    modport gsau (
        // From Veggie File
        input  veg_vdata1, veg_vdata2, veg_valid,
        output veg_ready,

        // Scoreboard handshake (inputs from scoreboard)
        input  sb_vdst, sb_valid, sb_weight,

        // From WB buffer
        input  wb_output_ready,

        // From Systolic Array
        input  sa_array_output, sa_out_valid, sa_fifo_has_space,

        // Outputs from GSAU
        output wb_psum, wb_wbdst, wb_valid,
        output sb_ready, 
        output sa_array_in, sa_array_in_partials, sa_input_en, sa_weight_en, sa_partial_en, sa_output_ready
    );

    //Veggie File
    modport veggie (
        output veg_vdata1, veg_vdata2, veg_valid,
        input  veg_ready
    );

    //Scoreboard
    modport scoreboard (
        input  sb_ready,
        output sb_vdst, sb_valid, sb_weight
    );

    //WB Buffer
    modport wb_buffer (
        input  wb_psum, wb_wbdst, wb_valid,
        output wb_output_ready
    );

    //Systolic Array
    modport systolic_array (
        input  sa_array_in, sa_array_in_partials, sa_input_en, sa_weight_en, sa_partial_en, sa_output_ready,
        output sa_array_output, sa_out_valid, sa_fifo_has_space
    );
  
endinterface
`endif