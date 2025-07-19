//By            : Joe Nasti
//Last Updated  : 7.16.18
//
//Module Summary:
//    adds two signed 13 bit fraction values
//
//Inputs:
//    frac1/2 - signed 13 bit values with decimal point fixed after second bit
//Outputs:
//    sum     - output of sum operation regardless of overflow
//    ovf     - high if an overflow has occured

`timescale 1ns/1ps

module adder_13b (
    input      [13:0] frac1,
    input      [13:0] frac2,
    output reg [13:0] sum,
    output reg        ovf
);

    always_comb begin

        sum = frac1 + frac2;
        ovf = 0;

        if (frac1[13] == 1 && frac2[13] == 1 && sum[13] == 0) begin
            ovf = 1;
            sum[13] = 1;
        end

        if (frac1[13] == 0 && frac2[13] == 0 && sum[13] == 1) begin
            ovf = 1;
            sum[13] = 0;
        end

    end
endmodule
