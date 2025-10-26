`timescale 1ps/1ps

`include "scpad_if.sv"
import scpad_pkg::*;

// // Scheduler <=> Backend
//     modport backend_sched (
//         input clk, n_rst, sched_req,
//         output sched_res
//     );

//     // Backend <=> Body
//     modport backend_body (
//         input clk, n_rst, 
//         input  be_stall, be_res, 
//         output be_req
//     );

//     // Backend <=> DRAM
//     modport backend_dram (
//         input clk, n_rst, 
//         output be_dram_req, be_dram_stall,
//         input dram_be_res
//     );

module backend_tb;

    localparam CLK_PERIOD = 10; 
    
    logic clk, n_rst;

    always #(CLK_PERIOD/2) clk = ~clk;

    scpad_if bif(clk, n_rst);

    // module backend #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (
    // scpad_if.backend_sched bsbif, 
    // scpad_if.backend_body bscif, 
    // scpad_if.backend_dram bdrif
    // );
    
    backend #(.IDX(0)) DUT (bif);

    initial begin
        n_rst = 0;
        repeat (5) @(posedge clk);
        n_rst = 1;
    end

    string fname, wavepath; 
    getenv("WAVEPATH", wavepath);
    $sformat(fname, "%s/backend_tb.vcd", wavepath); 

    // initial begin 
    //     $dumpfile(fname);
    //     $dumpvars(0);
    // end 

    test PROG (.bif(bif)); 

    initial begin
        #(10_000 * CLK_PERIOD) $fatal(1, "[TB] Timeout");
    end

endmodule

program test (scpad_if.backend_tb bif);

    task reset(); 
        bif.n_rst = 0;
        repeat (2) @(posedge bif.clk);
        bif.n_rst = 1;
        repeat (2) @(posedge bif.clk);
    endtask


    initial begin

        bif = 0;

        reset();
        #(20 * 2); // hard coded for now just want to get this up and running

    end 

endprogram