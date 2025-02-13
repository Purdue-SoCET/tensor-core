// MICRON TECHNOLOGY, INC. - CONFIDENTIAL AND PROPRIETARY INFORMATION
`ifdef DDR4_X16
    parameter int MAX_DIMM_DQ_BITS = 0;
    parameter int MAX_DIMM_DQ_BITS = 0;
    parameter int MAX_MEM_CHIPS = 0;
    parameter int MAX_DIMM_DQS_BITS = 0;
    parameter int MAX_DIMM_DM_BITS = 0;
`endif
`ifdef ECC
parameter int MAX_DIMM_DQ_BITS = 72;
`else
parameter int MAX_DIMM_DQ_BITS = 64;
`endif
`ifdef DUAL_RANK
    `ifdef DDR4_X8
        `ifdef ECC
            parameter int MAX_MEM_CHIPS = 18;
            parameter int MAX_DIMM_DQS_BITS = 9;
            parameter int MAX_DIMM_DM_BITS = 9;
        `else
            parameter int MAX_MEM_CHIPS = 16;
            parameter int MAX_DIMM_DQS_BITS = 8;
            parameter int MAX_DIMM_DM_BITS = 8;
        `endif
    `endif
    `ifdef DDR4_X4
        `ifdef ECC
            parameter int MAX_MEM_CHIPS = 36;
            parameter int MAX_DIMM_DQS_BITS = 18;
            parameter int MAX_DIMM_DM_BITS = 18;
        `else
            parameter int MAX_MEM_CHIPS = 32;
            parameter int MAX_DIMM_DQS_BITS = 16;
            parameter int MAX_DIMM_DM_BITS = 16;
        `endif
    `endif
    parameter MAX_DIMM_CS_BITS = 2;
`else
    `ifdef DDR4_X8
        `ifdef ECC
            parameter int MAX_MEM_CHIPS = 9;
            parameter int MAX_DIMM_DQS_BITS = 9;
            parameter int MAX_DIMM_DM_BITS = 9;
        `else
            parameter int MAX_MEM_CHIPS = 8;
            parameter int MAX_DIMM_DQS_BITS = 8;
            parameter int MAX_DIMM_DM_BITS = 8;
        `endif
    `endif
    `ifdef DDR4_X4
        `ifdef ECC
            parameter int MAX_MEM_CHIPS = 18;
            parameter int MAX_DIMM_DQS_BITS = 18;
            parameter int MAX_DIMM_DM_BITS = 18;
        `else
            parameter int MAX_MEM_CHIPS = 16;
            parameter int MAX_DIMM_DQS_BITS = 16;
            parameter int MAX_DIMM_DM_BITS = 16;
        `endif
    `endif
    parameter MAX_DIMM_CS_BITS = 1;
`endif