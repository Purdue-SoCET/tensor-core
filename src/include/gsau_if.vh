/*
  Saandiya, Myles, Nikhil
  mohan76@purdue.edu, mquerimi@purdue.edu, nvaidyan@purdue.edu

  GSAU Interface V1
*/

`ifndef GSAU_IF_VH
`define GSAU_IF_VH

interface gsau_if;
  import vector_pkg::*;   // reuse basic typedefs (data, addr, etc.)
  import sys_arr_pkg::*;  // systolic-specific typedefs
  import types_pkg::*;

  ////////////////////////////////////////////////////////////////////////////
  ////////////////////////////// Types ///////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////////


  ////////////////////////////////////////////////////////////////////////////
  /////////////////////////////// Signals ////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////////

    // VEGGIE FILE
    // From Veggie File to GSAU
    vreg_t        vdata;         // [512 bits] vector data
    logic         valid;         // indicates vdata valid

    // From GSAU to Veggie File
    logic         ready;        // indicates ready for value

    // SCOREBOARD 
    // From GSAU to Scoreboard
    logic         ready;         // ready to accept next instruction
    logic [7:0]   vdst;          // destination vector register index
    logic         svalid;        // scoreboard valid

    // From Scoreboard to GSAU
    logic         nready;        // scoreboard ready
    logic [7:0]   nvdst;         // next destination reg
    logic         nsvalid;       // next scoreboard valid
    logic         weight;        // 1 bit signal for weight indication

    // WB BUFFER
    // From GSAU to WB Buffer
    vreg_t        psum;          // partial sum output
    logic [7:0]   wbdst;         // destination vector register for writeback
    logic         wb_valid;      // valid signal for psum output

    // From WB Buffer to GSAU
    logic         output_ready;  // WB buffer ready to accept data

    // SYSTOLIC ARRAY 
    // To Systolic Array
    logic [511:0] array_in;          // input data to systolic array
    logic [511:0] array_in_partials; // partial sum inputs
    logic         input_en;          // enable data input
    logic         weight_en;         // enable weight load
    logic         partial_en;        // enable partial sum load

    // From Systolic Array
    logic [511:0] array_output;      // output data
    logic         out_en;            // output enable flag
    logic         fifo_has_space     // to send activations

  ////////////////////////////////////////////////////////////////////////////
  ////////////////////////////// Modports ////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////////

    //GSAU 
    modport gsau (
        // Inputs
        input vdata, valid,
            nvdst, nsvalid,
            output_ready,
            array_output, out_en,
        // Outputs
        output psum, wbdst, wb_valid,
            ready, vdst, svalid,
            array_in, array_in_partials,
            input_en, weight_en, partial_en
    );

    //Veggie File
    modport veggie (
        output vdata, valid,
        input  nvdata, nvalid
    );

    //Scoreboard
    modport scoreboard (
        input  ready, vdst, svalid,
        output nready, nvdst, nsvalid
    );

    //WB Buffer
    modport wb_buffer (
        input  psum, wbdst, wb_valid,
        output output_ready
    );

    //Systolic Array
    modport systolic_array (
        input array_in, array_in_partials, input_en, weight_en, partial_en,
        output array_output, out_en, fifo_has_space
    );
  
endinterface
`endif