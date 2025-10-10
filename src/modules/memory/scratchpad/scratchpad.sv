`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module scratchpad (
    input logic clk, n_rst,
    scpad_if.top sif
); 
    import scpad_types_pkg::*;

    genvar ti;
    generate
        for (ti = 0; ti < NUM_SCPADS; ti++) begin : g_scpad
            frontend #(.IDX(IDX)) u_frontend (.clk(clk), .n_rst(n_rst), .fcif(sif));
            backend #(.IDX(IDX)) u_backend (.clk(clk), .n_rst(n_rst), .bif(sif));
            body #(.IDX(IDX)) u_body (.clk(clk), .n_rst(n_rst), .bif(sif));
        end
    endgenerate

endmodule