`include "crossover_switch.sv"

module compare_switch #( 
    parameter int SIZE = 32
) ( 
    input var logic [SIZE-1:0] din [2], 
    input var logic [SIZE-1:0] tin [2], 
    input cntrl,
    output logic [SIZE-1:0] dout [2], 
    output logic [SIZE-1:0] tout [2]
); 

    crossover_switch #(.SIZE(SIZE)) (.din(din), .dout(dout), .cntrl(cntrl)); 
    crossover_switch #(.SIZE(SIZE)) (.din(tin), .dout(tout), .cntrl(cntrl)); 

endmodule