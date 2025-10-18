`timescale 1ps/1ps

`include "scpad_if.sv"
import scpad_pkg::*;

module head_tb;

    localparam CLK_PERIOD = 10; 
    
    logic clk, n_rst;

    always #(CLK_PERIOD/2) clk = ~clk;

    scpad_if hif(clk, n_rst);
    
    head #(.IDX(0)) DUT (hif);

    initial begin
        n_rst = 0;
        repeat (5) @(posedge clk);
        n_rst = 1;
    end

    string fname, wavepath; 
    getenv("WAVEPATH", wavepath);
    $sformat(fname, "%s/head_tb.vcd", wavepath); 

    // initial begin 
    //     $dumpfile(fname);
    //     $dumpvars(0);
    // end 

    test PROG (.hif(hif)); 

    initial begin
        #(10_000 * CLK_PERIOD) $fatal(1, "[TB] Timeout");
    end

endmodule

// We only want to confirm that BE has priority over FE, and grants are alloted properly. 
// We provide a random addr to ensure that the addr is being latched properly.
// We toggle the valid signals to simulate requests.
program test (scpad_if.spad_head_tb hif);

    task reset(); 
        hif.n_rst = 0;
        repeat (2) @(posedge hif.clk);
        hif.n_rst = 1;
        repeat (2) @(posedge hif.clk);
    endtask


    task fe_toggle();
        hif.fe_req.valid[0] = ~hif.fe_req.valid[0];
    endtask

    task be_toggle();
        hif.be_req.valid[0] = ~hif.be_req.valid[0];
    endtask

    task sweep_fe_be(); 
        logic fe_write = hif.fe_req.write[0];
        logic be_write = hif.be_req.write[0];
        $display("---- SWEEP: FE_WRITE: %b, BE_WRITE: %b ----", fe_write, be_write);

        fe_toggle();
        be_toggle();
        @(posedge hif.clk); // 11 
        // need to have a check function here

        be_toggle();
        @(posedge hif.clk); // 10
        // need to have a check function here

        fe_toggle();
        be_toggle();
        @(posedge hif.clk); // 01
        // need to have a check function here

        be_toggle();
        @(posedge hif.clk); // 00
        // need to have a check function here
    endtask 

    initial begin 

        reset();

        hif.fe_req.addr[0] = SCPAD_ADDR_WIDTH'(69);
        hif.be_req.addr[0] = SCPAD_ADDR_WIDTH'(96);
        @(posedge hif.clk);

        hif.fe_req.write[0] = 1'b1;
        hif.be_req.write[0] = 1'b1;
        sweep_fe_be(); 

        hif.fe_req.write[0] = 1'b0;
        hif.be_req.write[0] = 1'b1;
        sweep_fe_be(); 

        hif.fe_req.write[0] = 1'b1;
        hif.be_req.write[0] = 1'b0;
        sweep_fe_be(); 

        hif.fe_req.write[0] = 1'b0;
        hif.be_req.write[0] = 1'b0;
        sweep_fe_be(); 

        $display("[TB] Head TB PASSED");
        $finish(0);

    end 

endprogram