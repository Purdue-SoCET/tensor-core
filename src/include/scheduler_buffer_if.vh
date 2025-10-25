`ifndef SCHEDULER_BUFFER_IF
`define SCHEDULER_BUFFER_IF
`include "dram_command_if.vh"


interface scheduler_buffer_if();
    import dram_pack::*;

    parameter WORD_W = 32;
    logic dREN, dWEN, request_done; 
    logic [WORD_W - 1:0] ramaddr, memstore;
    logic [WORD_W - 1:0] ramaddr_rq, ramstore_rq, ramaddr_rq_ft, ramstore_rq_ft;
    logic [WORD_W - 1 : 0] memaddr_callback;


    

    logic iwait, dwait;
    logic ramREN_curr, ramREN_ftrt, ramWEN_curr, ramWEN_ftrt;

    modport scheduler (
        input dREN, dWEN, ramaddr, memstore,request_done,
        output ramaddr_rq, ramstore_rq, ramaddr_rq_ft, ramstore_rq_ft, memaddr_callback, ramREN_curr, ramREN_ftrt, ramWEN_curr, ramWEN_ftrt
    );



endinterface

`endif