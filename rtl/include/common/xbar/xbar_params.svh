`ifndef XBAR_PARAMS_SVH
`define XBAR_PARAMS_SVH

    parameter int unsigned NAIVE_LATENCY = 1;
    parameter int unsigned BENES_LATENCY = 3;
    parameter int unsigned BATCHER_LATENCY = 4;
    
    `ifndef BATCHER_SIZE
        `define BATCHER_SIZE 32
    `endif
    `ifndef BATCHER_DWIDTH
        `define BATCHER_DWIDTH 16
    `endif
    `ifndef BATCHER_REGISTER_MASK
        `define BATCHER_REGISTER_MASK 14'b11111111111111
    `endif
    
`endif
