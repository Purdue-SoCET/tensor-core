`timescale 1ns / 10ps
`include "scoreboard_if.vh"

module scoreboard_tb;

    parameter PERIOD = 10;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    scoreboard_if sbif ();

    test PROG (.CLK(CLK), .nRST(nRST), .sbif(sbif));

    scoreboard DUT (.CLK(CLK), .nRST(nRST), .sbif(sbif));

endmodule

program test (
    input logic CLK, 
    output logic nRST,
    scoreboard.tb sbif
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
            scoreboard.flush = '0;
            scoreboard.freeze = '0;
            scoreboard.wb = '0;

            @(posedge CLK);
        end
    endtask


    initial begin

        reset_in();
        reset_dut();

        $finish;
    end


endprogram