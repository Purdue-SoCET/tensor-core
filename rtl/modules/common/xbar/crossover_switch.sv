module crossover_switch #( 
    parameter int SIZE = 32
) ( 
    input var logic [SIZE-1:0] din [2], 
    input logic cntrl, 
    output var logic [SIZE-1:0] dout [2]
); 

    assign dout = (cntrl) ? {din[1], din[0]} : din;  

endmodule