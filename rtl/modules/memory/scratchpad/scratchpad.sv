import scpad_pkg::*;

module scratchpad (scpad_if.top sif); 

    generate
        if ((NUM_COLS & (NUM_COLS - 1)) != 0) initial $fatal(1, "NUM_COLS (%0d) must be a power of 2!", NUM_COLS);
        if ((SRAM_VERT_FOLD_FACTOR & (SRAM_VERT_FOLD_FACTOR - 1)) != 0) initial $fatal(1, "SRAM_VERT_FOLD_FACTOR (%0d) must be a power of 2!", SRAM_VERT_FOLD_FACTOR);
        if ((ELEM_BITS & (ELEM_BITS - 1)) != 0) initial $fatal(1, "ELEM_BITS (%0d) must be a power of 2!", ELEM_BITS);
    endgenerate

    genvar ti;
    generate
        for (ti = 0; ti < NUM_SCPADS; ti++) begin : g_scpad
            frontend #(.IDX(ti)) frontend (.fcif(sif));
            backend #(.IDX(ti)) backend (.bif(sif));
            body #(.IDX(ti)) body (.bif(sif));
        end
    endgenerate

endmodule
