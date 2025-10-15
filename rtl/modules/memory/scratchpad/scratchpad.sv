import scpad_pkg::*;

module scratchpad (scpad_if.top sif); 

    genvar ti;
    generate
        for (ti = 0; ti < NUM_SCPADS; ti++) begin : g_scpad
            frontend #(.IDX(ti)) frontend (.fcif(sif));
            backend #(.IDX(ti)) backend (.bif(sif));
            body #(.IDX(ti)) body (.bif(sif));
        end
    endgenerate

endmodule
