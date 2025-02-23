`timescale 1ns / 10ps
`include "execute_if.vh"

module execute_tb;

    parameter PERIOD = 10;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    execute_if exif ();

    test PROG (CLK,  nRST, exif);

    dispatch DUT (.CLK(CLK), .nRST(nRST), .diif(diif));

endmodule

program test (
    input logic CLK, 
    output logic nRST,
    dispatch_if.tb dis_if
);

    task reset_dut;
        begin
            nRST = 1'b0;

            @(posedge CLK);
            @(posedge CLK);

            @(negedge CLK);
            nRST = 1'b1;

            @(negedge CLK);
            @(negedge CLK);
        end
    endtask

    task reset_in;
        begin
            dis_if.fetch = '0; 
            dis_if.flush = '0;
            dis_if.freeze = '0;
            dis_if.fust_s = '0;
            dis_if.fust_m = '0; 
            dis_if.fust_g = '0;
            dis_if.wb = '0;
            dis_if.ihit = '0;

            @(posedge CLK);
        end
    endtask


    initial begin

        reset_in();
        reset_dut();

        @(posedge CLK);

        // test case 1 - write after write hazard

        dis_if.fetch.imemload = 32'b010101010101_00111_000_10101_0010011;

        @(posedge CLK);
        @(posedge CLK);
        @(posedge CLK);

        dis_if.fetch.imemload = 32'b010000010101_00111_000_10101_0010011;

        @(posedge CLK);
        @(posedge CLK);
        @(posedge CLK);

        // test case 2 - freeze 

        reset_in();
        reset_dut();

        dis_if.fetch.imemload = 32'b010000010101_00111_000_10101_0010011;

        @(posedge CLK);

        dis_if.freeze = '1;

        @(posedge CLK);
        @(posedge CLK);
        @(posedge CLK);

        // test case 3 - flush 

        reset_in();
        reset_dut();

        dis_if.fetch.imemload = 32'b010000010101_00111_000_10101_0010011;

        @(posedge CLK);

        dis_if.flush = '1;

        @(posedge CLK);
        @(posedge CLK);
        @(posedge CLK);

        // test case 4 - need to add cases for -> busy bits in FUST_S and FUST_M prevent writes to FUST (the enable bit should not get set n_fust_s/m/g_en)
        // the RSTs all get correctly written to with the correct tags and busy bits for the correct FU, and writeback writes to RSTs correctly clear the busy and tag bits 

        reset_in();
        reset_dut();

        $finish;
    end


endprogram