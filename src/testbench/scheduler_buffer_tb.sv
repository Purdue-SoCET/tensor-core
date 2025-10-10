`timescale 1ns / 1ps
`include "scheduler_buffer_if.vh"


//Giving this
//You should try to debug yourself
module scheduler_buffer_tb();

parameter int CLK_PERIOD = 1.5;

logic CLK;
logic nRST = 0;

//Creating the interface
scheduler_buffer_if myif();

//Instantiate the module
scheduler_buffer u0 (.CLK(CLK), .nRST(nRST), .mysche(myif));

class coverage_test;
    //Creating the coverage group
    // Step 1: Create a handle for the virtual interface in the class.
        virtual scheduler_buffer_if vif;
    covergroup sch_group @(posedge CLK);
        //You can do this
        request_sign: coverpoint {vif.dREN, vif.dWEN} {
            // wildcard bins all_request = {2'b??};
            bins s00 = {2'b00};
            bins s01 = {2'b01};
            bins s10 = {2'b10};
            bins s11 = {2'b11};
        }
    endgroup

    //Creating rand address
    rand logic [1:0] request_toggle;
    rand logic [31:0] ramaddr;
    rand logic [31:0] memstore;

    constraint request_non {
        request_toggle != 2'b11;
    }

    constraint ram_addr_limm {
        ramaddr inside {[100:200], [500:600]};
    }

    function new(virtual scheduler_buffer_if vif);
        this.vif = vif;
        sch_group = new();
    endfunction

    //Helper function printing
    function print();
        $display("Here is the addr 0x%h, request 0x%b", ramaddr, request_toggle);
    endfunction

endclass

//Generate the static array

class pkg;
    //declaring this standing for static array
    rand logic [31:0] arr [7];

    constraint arr_val {
        foreach (arr[i]) {
            arr[i] inside {[40:60], [20:55]};
        }
    }

    function new ();

    endfunction

endclass

//Generate the dynamic array
class pkg1;
    //declaring this standing for static array
    rand logic [31:0] arr1 [];

    constraint arr_size {
        (arr1.size() < 30 && arr1.size() > 0);
    }
    constraint arr_val {
        foreach (arr1[i]) {
            arr1[i] inside {[40:60], [20:55]};
        }
    }

    function new ();

    endfunction

endclass

//Generate the dynamic array
class pkg2;
    //declaring this standing for static array
    rand logic [31:0] arr1 [$];

    constraint arr_size {
        (arr1.size() < 30 && arr1.size() > 0);
    }
    constraint arr_val {
        foreach (arr1[i]) {
            arr1[i] inside {[40:60], [20:55]};
        }
    }

    function new ();

    endfunction

endclass

//Example of creating immediate assertion
initial begin
    assert (condition)
        $display("Passed");
    else
        $error("This is not what I liked");
end

//Example of creating concurrent assertion

property check_assert();
    @(posedge CLK) disable diff (nRST);

    (!B && A) |-> ##4 (C==D); 

endproperty

assert property(check_assert)
else
    $error("This is not what I look for");

//Example of creating a class with coverage group

class base_class;
    rand logic [23:0] a;
    rand logic [24:0] b;
    rand logic [1:0] req;
    covergroup cv_group @(posedge CLK);
        request_sign: coverpoint {req} {
            bins s00 = {2'b00};
            bins s01 = {2'b01};
            bins s10 = {2'b10};
            bins s11 = {2'b11};
        }

        data_cover:coverpoint {a} {
            bins max_data = {32'h0};
            bins min_data = {32'h1};
        }
    endgroup

    constraint c_basic {
        a inside {[1:50]};
        req != 0;
    }

    function new();
        cv_group = new();
    endfunction

    function virtual void display();
        $display("This is base_class");
    endfunction
endclass

class child_class extends base_class;

    function new();

    endfunction

    function virtual void display();
        $display("This is child class");
    endfunction


endclass

always begin
    CLK = 0;
    #(CLK_PERIOD /2);
    CLK = 1;
    #(CLK_PERIOD /2);
end



task reset_case;
    myif.dREN = 0;
    myif.dWEN = 0;
    myif.ramaddr = 0;
    myif.memstore = 0;

    nRST = 0;
    @(posedge CLK);
    @(posedge CLK);
    nRST = 1;
    @(posedge CLK);
endtask

initial begin
    coverage_test the_class = new(myif);
    reset_case();
    
    for (int i = 0; i < 20; i=i+1) begin
        the_class.randomize();
        {myif.dREN, myif.dWEN} = the_class.request_toggle;
        myif.ramaddr = the_class.ramaddr;
        myif.memstore = i;
        the_class.print();
        @(posedge CLK);
    end 


    $finish;
end


endmodule
