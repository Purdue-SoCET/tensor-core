`include "types_pkg.vh"
`include "scratchpad_if.vh"
`include "scratchpad_bank_if.vh"

module scratchpad (
    input logic CLK, nRST,
    scratchpad_if.sp spif
);

    scratchpad_bank_if spbif1();
    scratchpad_bank_if spbif2();
    scratchpad_bank_if spbif3();
    scratchpad_bank_if spbif4();

    scratchpad_bank spb1(CLK, nRST, spbif1);
    scratchpad_bank spb2(CLK, nRST, spbif2);
    scratchpad_bank spb3(CLK, nRST, spbif3);
    scratchpad_bank spb4(CLK, nRST, spbif4);
    
    socetlib_fifo inFIFO1(.CLK(CLK), .nRST(nRST), .WEN(), .REN(), .clear(), .wdata(), .full(), .empty(), .underrun(), .overrun(), .count(), .rdata());
endmodule