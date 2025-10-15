`timescale 1ns/1ps

//include modules file
`include "control_unit_if.vh"
`include "command_FSM_if.vh"
`include "init_state_if.vh"
`include "address_mapper_if.vh"
`include "row_open_if.vh"
`include "timing_signal_if.vh"


module control_unit(
    input logic CLK,
    input logic nRST,
    control_unit_if.arb mytop,
    control_unit_if.dram_sig mysig

);
    import dram_pkg::*;

    logic init_done_l;


    always_ff @(posedge CLK, negedge nRST) begin
        if(!nRST) begin
            init_done_l <= 0;
        end else begin
            init_done_l <= myinit.init_done;

        end
    end

    command_FSM_if mycmd();
    init_state_if myinit();
    address_mapper_if myaddr();
    row_open_if myrow();
    timing_signal_if mytime();

    addr_mapper u0 (.amif(myaddr));
    row_open u1(.CLK(CLK), .nRST(nRST), .pol_if(myrow));
    init_state u2(.CLK(CLK), .nRST(nRST), .it(myinit));
    command_FSM u3 (.CLK(CLK), .nRST(nRST), .mycmd(mycmd));
    timing_signal u4 (.CLK(CLK), .nRST(nRST), .timif(mytime), .cfsmif(mycmd));

    //Interface for command_FSM and timing module
    assign mycmd.tACT_done = mytime.tACT_done;
    assign mycmd.tWR_done =  mytime.tWR_done;
    assign mycmd.tPRE_done = mytime.tPRE_done;
    assign mycmd.rf_req =    mytime.rf_req;
    assign mycmd.tRD_done =  mytime.tRD_done;
    assign mycmd.tREF_done = mytime.tREF_done;
    assign myrow.tACT_done = mytime.tACT_done;
    

    //Request interface between memory arbiter and command FSM
    assign mycmd.dREN = mytop.dREN;
    assign mycmd.dWEN = mytop.dWEN;
    assign mytop.ram_wait = mycmd.ram_wait;

    //Interface between init and command FSM
    assign myinit.init = mycmd.init_req;
    assign mycmd.init_done = myinit.init_done;
    assign mytime.init_done =  myinit.init_done;

    //Address mapper
    assign myaddr.address = mytop.ram_addr;
    assign myaddr.configs = x8;

    //Row policy connection
    assign myrow.bank_group = myaddr.BG;
    assign myrow.bank = myaddr.bank;
    assign myrow.row = myaddr.row;
    assign myrow.req_en = mytop.dWEN || mytop.dREN;
    assign myrow.row_resolve = mycmd.row_resolve;
    assign myrow.refresh = mytime.tREF_done;
    assign mycmd.row_stat = myrow.row_stat;
    assign mycmd.all_row_closed = myrow.all_row_closed;

    //Interface between control unit and data transfer
    assign mytop.wr_en = mytime.wr_en;
    assign mytop.rd_en = mytime.rd_en;
    assign mytop.clear = mytime.clear;
    assign mytop.offset = myaddr.offset;

    
    //Logic for state, nstate with mux
    always_comb begin
        if (!init_done_l) begin
            mysig.state = myinit.init_state;
            mysig.nstate = myinit.ninit_state;
        end else begin
            mysig.state = mycmd.cmd_state;
            mysig.nstate = mycmd.ncmd_state;
        end
    end

    //Logic for handling the row conflict
    always_comb begin
        mysig.rank = myaddr.rank;
        mysig.BG   = myaddr.BG;
        mysig.bank = myaddr.bank;
        mysig.col  = {myaddr.col, myaddr.offset};
        mysig.rf_req = mytime.rf_req;
        //If we have the row conflicton
        if (myrow.row_stat == 2'b11) begin
            mysig.row = myrow.row_conflict; 
        end else begin
            mysig.row = myaddr.row;
        end
    end





endmodule