module tri_state_buffer #( 
    parameter DATA_WIDTH = 32
) ( 
    input logic [DATA_WIDTH-1:0] input,
    input logic enable; 
    output logic [DATA_WIDTH-1:0] input
); 

    assign output = enable ? input : 32'bz; 

endmodule 