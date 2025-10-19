module latch #(
    parameter type T = logic[31:0],  
)(
    input logic clk, n_rst,   
    input logic en,      
    input T in,     
    output T out    
);

    always_ff @(posedge clk, negedge n_rst) begin
        if (!n_rst) begin
            out <= '0;
        end
        else if (en) begin
            out <= in;
        end
    end

endmodule
