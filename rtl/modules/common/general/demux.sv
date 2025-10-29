module demux #(
    parameter int IN = 1,                  
    parameter int OUT = 4,                 
    parameter type TYPE_T = logic[31:0]
) (
    input TYPE_T  in [IN],   
    input logic[$clog2(OUT)-1:0] sel_idx,   
    output TYPE_T out [OUT]   
);
    always_comb begin
        for (int o = 0; o < OUT; o++) begin
            out[o] = '0;
        end
        for (int i = 0; i < IN; i++) begin
            out[sel_idx] = in[i];
        end
    end
endmodule
