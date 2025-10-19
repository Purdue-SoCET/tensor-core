module mux #(
    parameter int IN  = 4,
    parameter int OUT = 1,
    parameter type TYPE_T = logic[31:0]  
) (
    input TYPE_T in [IN],                
    input logic[$clog2(IN)-1:0] sel_idx,               
    output TYPE_T out [OUT]             
);
    always_comb begin
        for (int p = 0; p < OUT; p++) begin
            out[p] = in[sel_idx];           
        end
    end
endmodule
