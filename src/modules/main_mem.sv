`timescale 1ns / 1ps
`include "main_mem_if.vh"


module main_mem(
        input logic clk, nrst,
        main_mem_if.mem mmif
    );
    
//    bram_ram ram1 (
//      .clka(clk),            // input wire clka
//      .rsta(1'd0),            // input wire rsta
//      .ena(mmif.enable),              // input wire ena
//      .wea(mmif.write_en),              // input wire [3 : 0] wea
//      .addra(mmif.addr),          // input wire [31 : 0] addra
//      .dina(mmif.data_in),            // input wire [31 : 0] dina
//      .douta(mmif.data_out),          // output wire [31 : 0] douta
//      .rsta_busy(mmif.busy)  // output wire rsta_busy
//    );

    logic [31:0] addr;

    assign mmif.busy = '0;
    // assign mmif.data_out = '1;

//    logic [299:0][31:0] instr;
    (* ram_style = "block" *)
    reg [31:0] instr [0:65535];
    
    assign addr = (mmif.addr >> 2);

    initial begin
        $readmemh("/home/asicfab/a/rrbathin/socet/amp/tensor-core/src/meminit.mem", instr); 
    end

    always_ff @(posedge clk) begin
        if (mmif.write_en == '1) begin
            instr[addr] <= mmif.data_in;
        end
        else begin
            mmif.data_out <= instr[addr];
        end
    end
    
endmodule
