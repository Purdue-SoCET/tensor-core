`timescale 1ns/1ps

//include modules file
`include "command_FSM_if.vh"
`include "init_state_if.vh"
`include "address_mapper_if.vh"
`include "row_open_if.vh"


module dram_top (
    input logic CLK,
    input logic nRST,
    dram_top_if.csm_debug mycsm,
    dram_top_if.dut mytop
);
    import dram_pkg::*;

    command_FSM_if mycmd();
    init_state_if myinit();
    address_mapper_if myaddr();
    row_open_if myrow();

    addr_mapper u0 (.amif(myaddr));
    row_open u1(.CLK(CLK), .nRST(nRST), .pol_if(myrow));
    init_state u2(.CLK(CLK), .nRST(nRST), .it(myinit));
    command_FSM u3 (.CLK(CLK), .nRST(nRST), .mycmd(mycmd));

    //Interface for timing 
    assign mycmd.tACT_done = mycsm.tACT_done;
    assign mycmd.tWR_done =  mycsm.tWR_done;
    assign mycmd.tPRE_done = mycsm.tPRE_done;
    assign mycmd.rf_req =    mycsm.rf_req;
    assign mycmd.tRD_done =  mycsm.tRD_done;
    assign mycmd.tREF_done = mycsm.tREF_done;
    

    //Request interface between memory arbiter and command FSM
    assign mycmd.dREN = mytop.dREN;
    assign mycmd.dWEN = mytop.dWEN;
    assign mytop.ram_wait = mycmd.ram_wait;

    //Interface between init and command FSM
    assign myinit.init = mycmd.init_req;
    assign mycmd.init_done = myinit.init_valid;


    assign myaddr.address = mytop.ram_addr;
    assign myaddr.configs = x8;
    assign myrow.bank_group = myaddr.BG;
    assign myrow.bank = myaddr.bank;
    assign myrow.row = myaddr.row;
    assign myrow.req_en = mytop.dWEN || mytop.dREN;
    assign myrow.row_resolve = mycmd.row_resolve;
    assign myrow.refresh = mycsm.tREF_done;
    assign mycmd.row_stat = myrow.row_stat;

    






endmodule