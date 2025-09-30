`include "datapath_cache_if.vh"
`include "caches_if.vh"
`include "arbiter_caches_if.vh"
`include "scratchpad_if.vh"

module memory_subsystem (
    input logic CLK, nRST,
    datapath_cache_if dcif,
    caches_if cif,
    arbiter_caches_if acif,
    scratchpad_if spif
    // scratchpad_if.sp spif
);

    // Internal interface for scratchpad

    // Arbiter
    memory_arbiter_basic ARB (
        .CLK(CLK),
        .nRST(nRST),
        .acif(acif),
        .spif(spif)
    );

    // Instruction cache
    icache ICACHE (
        .CLK(CLK),
        .nRST(nRST),
        .cif(cif),
        .dcif(dcif)
    );

    // Data cache
    dcache DCACHE (
        .CLK(CLK),
        .nRST(nRST),
        .cif(cif),
        .dcif(dcif),
        .acif(acif)
    );

    // Scratchpad
    scratchpad SP (
        .CLK(CLK),
        .nRST(nRST),
        .spif(spif)
    );

endmodule