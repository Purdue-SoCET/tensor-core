import scpad_pkg::*;

module scratchpad (scpad_if.top sif); 

    genvar ti;
    generate
        for (ti = 0; ti < NUM_SCPADS; ti++) begin : g_scpad
            frontend #(.IDX(ti)) u_frontend (.fcif(sif));
            backend #(.IDX(ti)) u_backend (.bif(sif));
            body #(.IDX(ti)) u_body (.bif(sif));
        end
    endgenerate

endmodule
