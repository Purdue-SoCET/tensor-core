//By            : Joe Nasti
//Last Updated  : 11/17/2024 - convert to FP16 for systolic array MAC unit
//
//Module Summary:
//    Converts a one bit sign and 13 bit magnitude to a 14 bit signed value
//
//Inputs:
//    sign          - one bit value to represent the sign (0 -> +, 1 -> -)
//    frac_unsigned - 13 bit unsigned magnitude
//Outputs:
//    frac_signed   - 14 bit signed result of conversion

`timescale 1ns/1ps

module u_to_s (
    input             sign,
    input      [12:0] frac_unsigned,
    output reg [13:0] frac_signed
);

    always_comb begin
        frac_signed = {1'b0, frac_unsigned};
        if (sign == 1) begin
            frac_signed = -frac_signed;
        end
    end
endmodule
