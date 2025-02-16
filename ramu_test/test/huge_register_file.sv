 `include "register_file_if.vh"

module register_file
(
    input logic CLK,
    input logic nRST,
    register_file_if.rf rfif
);
    paramater size = 256 * 1024;
    [31:0] [size - 1 : 0] registerfile, nxt_registerfile;

    always_ff @( posedge CLK, negedge nRST ) begin
        if(~nRST) begin
            registerfile <= '0;
        end
        else begin 
            registerfile <= nxt_registerfile;
        end
    end

    always_comb begin
        nxt_registerfile = registerfile;
        if(rfif.WEN && rfif.wsel != '0) begin
            nxt_registerfile [rfif.wsel] = rfif.wdat; 
        end
        nxt_registerfile[0] = '0;
    end


     assign rfif.rdat1 = registerfile[rfif.rsel1];
     assign rfif.rdat2 = registerfile[rfif.rsel2];


    
endmodule