//By            : Joe Nasti
//Last Updated  : 11/17/2024    Convert to FP16 for systolic array
//
//Module Summary:
//    converts a signed 14 bit value to a 13 bit magnitude and a one bit sign
//
//Inputs:
//    frac_signed   - 14 bit signed value
//Outputs:
//    sign          - 1 bit sign 'frac_unsigned'
//    frac_unsigned - 13 bit magnitude of 'frac_signed'

/* verilator lint_off UNUSEDSIGNAL */

`timescale 1ns/1ps

module s_to_u (
    input      [13:0] frac_signed,
    output reg        sign,
    output     [12:0] frac_unsigned
);

    reg [13:0] rfrac_signed;

    assign frac_unsigned = rfrac_signed[12:0];

    always_comb begin
        sign = 0;
        rfrac_signed = frac_signed;
        if (frac_signed[13] == 1) begin
            rfrac_signed = -frac_signed;
            sign         = 1;
        end
    end
endmodule
