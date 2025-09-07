`include "datapath_cache_if.vh"
`include "caches_if.vh"
`include "arbiter_caches_if.vh"
`include "scratchpad_if.vh"
`include "main_mem_if.vh"
`include "system_if.vh"

module memory_subsystem (
    input logic CLK, nRST,
    datapath_cache_if dcif,
    caches_if cif,
    arbiter_caches_if acif,
    scratchpad_if spif, 
    main_mem_if mmif,
    system_if syif
    // scratchpad_if.sp spif
);

    // Internal interface for scratchpad
    
    main_mem MM (
        .clk(CLK),
        .nrst(nRST),
        .mmif(mmif)
    );
    
    assign mmif.write_en = (syif.tbCTRL) ? {4{syif.WEN}} : {4{acif.ramWEN}};
    assign mmif.addr     = (syif.tbCTRL) ? syif.addr : acif.ramaddr;
    assign mmif.data_in  = (syif.tbCTRL) ? syif.store : acif.ramstore;
    assign mmif.enable   = '1;
    assign acif.ramload  = mmif.data_out;
    assign acif.ramBUSY  = mmif.busy;
    assign syif.load     = mmif.data_out;

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