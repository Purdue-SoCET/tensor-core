`timescale 1ps/1ps
`include "xbar_if.sv"

program automatic test; 

    extern function void driver(xbar_if.xbar_tb xif); 

endprogram

function void driver (xbar_if.xbar_tb xif);

    task reset(); 
        xif.n_rst = 0;
        repeat (2) @(posedge xif.clk);
        xif.n_rst = 1;
        repeat (2) @(posedge xif.clk);
    endtask

    initial begin 

        reset();

    end 

endfunction 
