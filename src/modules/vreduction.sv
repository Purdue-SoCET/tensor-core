`include "vector_types.vh"
`include "vreduction_if.vh"

module vreduction
#(parameter int WIDTH  = 16)
(
    input logic CLK,
    input logic nRST,
    vreduction_if.vruif vruif
);

localparam fp16_t POSINFIN = 16'b0111110000000000;
localparam fp16_t NEGINFIN = 16'b1111110000000000;

localparam int LEVELS = $clog2(WIDTH);
//vector types
import vector_pkg::*;





endmodule