module butterfly_unit #(
    parameter DATA_WIDTH = 32
)(
    input logic [DATA_WIDTH-1:0] in0,
    input logic [DATA_WIDTH-1:0] in1,
    input logic control, 
    output logic [DATA_WIDTH-1:0] out0,
    output logic [DATA_WIDTH-1:0] out1
);
    assign {out0, out1} = control ? {in1, in0} : {in0, in1};
endmodule
