`timescale 1ns/1ps
`include "command_FSM_if.vh"

module command_FSM_tb ();
    import dram_pack::*;
    logic CLK, nRST;
    localparam CLK_PERIOD = 1.5;    
    string test_case;
    command_FSM_if mycmd();

    always begin
        CLK = 1'b0;
        #(CLK_PERIOD / 2.0);
        CLK = 1'b1;
        #(CLK_PERIOD / 2.0);
    end

    command_FSM DUT (
        .CLK (CLK),
        .nRST (nRST),
        .mycmd (mycmd)
    );
    //Property assert
    //
    property POWER_UP_check;
        @(posedge CLK)
            $rose(nRST) |-> (mycmd.cmd_state == POWER_UP);
    endproperty

    Power_up_assert: assert property (POWER_UP_check)
            else $fatal(1, "Power_up_assert failed");

    property ACTIVATE_check;
        @(posedge CLK) disable iff (!nRST)
            ((mycmd.cmd_state == IDLE) && (mycmd.dREN || mycmd.dWEN)) |=> (mycmd.cmd_state == ACTIVATE);
    endproperty

    Activate_assert: assert property (ACTIVATE_check)
        else $fatal(1, "Activate failed");



    task reset_cmd;
        nRST = 1'b0;
        mycmd.dREN       = 0;
        mycmd.dWEN = 0;
        mycmd.init_done = 0;
        mycmd.tACT_done = 0;
        mycmd.tWR_done = 0;
        mycmd.tRD_done = 0;
        mycmd.tPRE_done = 0;
        mycmd.tREF_done = 0;
        mycmd.rf_req = 0;
        mycmd.row_stat = 0;
        
        @(posedge CLK);
        @(posedge CLK);
        nRST = 1'b1;
        @(posedge CLK);
        @(posedge CLK);
    endtask

    //Initialize
    task initialize ();
        //Immediate request
        assert (mycmd.init_req == 1)
            else $error ("init_req not 1");
        mycmd.init_done = 1;
        @(posedge CLK);
        mycmd.init_done = 0;
        @(posedge CLK);
    endtask
    //Activation
    task request(
        input string req,
        input string row_stat
    );
        if (req == "read") begin
            mycmd.dREN = 1'b1;
        end else if (req == "write") begin
            mycmd.dWEN = 1'b1;
        end else begin
            $fatal("Either read or write");
        end

        case(row_stat)
            "hit": begin
                mycmd.row_stat = 2'b01;
            end

            "conflict": begin
                mycmd.row_stat = 2'b11;
            end

            "miss": begin
                mycmd.row_stat = 2'b10;
            end

            default: begin
                $fatal("Wrong row stat value");
            end
        endcase
        @(posedge CLK);
    endtask

    task request_off ();
        mycmd.row_stat = 2'b00;
        {mycmd.dREN, mycmd.dWEN} = 0;
        @(posedge CLK);
    endtask

    task activate_row ();
        request("write", "miss");
        request_off();
    endtask


    initial begin
        test_case = "reset";
        reset_cmd();
        test_case = "intialize";
        initialize();
        test_case = "activate";
        activate_row();
        repeat (5) @(posedge CLK);
        $finish;
    end

endmodule