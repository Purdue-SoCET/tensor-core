`include "scratchpad_bank_if.vh"
`include "types_pkg.vh"
`timescale 1ns / 10ps

module scratchpad_bank_tb();
import types_pkg::*;

localparam CLK_PERIOD = 10;
logic tb_clk;
logic tb_nrst;

// Clock generation
always begin
    tb_clk = 1'b0;
    #(CLK_PERIOD / 2.0);
    tb_clk = 1'b1;
    #(CLK_PERIOD / 2.0);
end

scratchpad_bank_if spif();
scratchpad_bank DUT (.CLK(tb_clk), .nRST(tb_nrst), .spif(spif));

string tb_test_case;
integer tb_test_num = 0;

// Pack wFIFO data
function logic [68:0] make_wfifo_data(
    input logic gemm_complete,
    input logic [1:0] mat_sel,
    input logic [1:0] row_sel,
    input logic [63:0] data
);
    return {gemm_complete, mat_sel, row_sel, data};
endfunction

// Pack rFIFO data
function logic [36:0] make_rfifo_data(
    input logic [31:0] address,
    input logic [1:0] req_type,
    input logic [1:0] mat_sel,
    input logic [1:0] row_sel
);
    return {address, req_type, mat_sel, row_sel};
endfunction

initial begin
    tb_nrst = 1'b1;
    spif.wFIFO_WEN = 1'b0;
    spif.wFIFO_wdata = '0;
    spif.rFIFO_WEN = 1'b0;
    spif.rFIFO_wdata = '0;
    spif.dramFIFO_REN = 1'b0;
    spif.gemmFIFO_REN = 1'b0;

    // Reset
    tb_test_case = "Reset";
    tb_nrst = 1'b0;
    #(CLK_PERIOD * 2);
    tb_nrst = 1'b1;
    #(CLK_PERIOD * 2);
    if (spif.wFIFO_full !== 1'b0 || spif.rFIFO_full !== 1'b0 ||
        spif.gemm_complete !== 1'b0 || spif.load_complete !== 1'b0 ||
        spif.dramFIFO_empty !== 1'b1 || spif.gemmFIFO_empty !== 1'b1) 
        $error("Reset failed");
    #(CLK_PERIOD);

    // Write and Verify Data Storage
    tb_test_case = "Data Storage";
    tb_test_num++;
    // Write to mat 1, row 2
    spif.wFIFO_WEN = 1'b1;
    spif.wFIFO_wdata = make_wfifo_data(0, 2'b01, 2'b10, 64'hDEADCAFE_DEADCAFE);
    #(CLK_PERIOD);
    spif.wFIFO_WEN = 1'b0;
    
    // Read back through rFIFO
    #(CLK_PERIOD * 2);
    spif.rFIFO_WEN = 1'b1;
    spif.rFIFO_wdata = make_rfifo_data(32'h1000_0000, 2'b00, 2'b01, 2'b10);
    #(CLK_PERIOD);
    spif.rFIFO_WEN = 1'b0;
    
    #(CLK_PERIOD * 2);
    if (spif.dramFIFO_rdata !== {32'h1000_0000, 2'b01, 2'b10, 64'hDEADCAFE_DEADCAFE})
        $error("Data storage verification failed");

    // Load Complete Signal
    tb_test_case = "Load Complete";
    tb_test_num++;
    spif.wFIFO_WEN = 1'b1;
    spif.wFIFO_wdata = make_wfifo_data(0, 2'b11, 2'b11, 64'hDEADBEEF_DEADBEEF);
    #(CLK_PERIOD);
    spif.wFIFO_WEN = 1'b0;
    #(CLK_PERIOD * 2);
    if (spif.load_complete !== 1'b1) $error("Load complete not asserted");

    // GEMM Complete Signal
    tb_test_case = "GEMM Complete";
    tb_test_num++;
    spif.wFIFO_WEN = 1'b1;
    spif.wFIFO_wdata = make_wfifo_data(1, 2'b00, 2'b00, 64'h0);
    #(CLK_PERIOD);
    spif.wFIFO_WEN = 1'b0;
    #(CLK_PERIOD * 2);
    if (spif.gemm_complete !== 1'b1) $error("GEMM complete not asserted");

    // Test Case 4: rFIFO Type Routing
    tb_test_case = "rFIFO Routing";
    tb_test_num++;

    // Type 00 -> dramFIFO
    spif.rFIFO_WEN = 1'b1;
    spif.rFIFO_wdata = make_rfifo_data(32'hA000_0000, 2'b00, 2'b01, 2'b10);
    #(CLK_PERIOD);

    // Type 01 -> gemmFIFO
    spif.rFIFO_wdata = make_rfifo_data(32'hB000_0000, 2'b01, 2'b10, 2'b11);
    #(CLK_PERIOD);

    // Type 10 -> gemmFIFO
    spif.rFIFO_wdata = make_rfifo_data(32'hC000_0000, 2'b10, 2'b11, 2'b00);
    #(CLK_PERIOD);

    // Type 11 -> gemmFIFO
    spif.rFIFO_wdata = make_rfifo_data(32'hD000_0000, 2'b11, 2'b00, 2'b01);
    #(CLK_PERIOD);
    spif.rFIFO_WEN = 1'b0;

    // Verify outputs
    #(CLK_PERIOD * 4);

    if (spif.dramFIFO_rdata !== {32'hA000_0000, 2'b01, 2'b10, 64'hDEADCAFE_DEADCAFE} ||
        spif.gemmFIFO_rdata !== {2'b01, 2'b10, 2'b11, 64'h0} ||
        spif.gemmFIFO_rdata !== {2'b10, 2'b11, 2'b00, 64'h0} ||
        spif.gemmFIFO_rdata !== {2'b11, 2'b00, 2'b01, 64'h0})
        $error("rFIFO type routing failed");

    // Test Case 5: FIFO Full Conditions
    tb_test_case = "FIFO Full";
    tb_test_num++;

    // Fill wFIFO
    spif.wFIFO_WEN = 1'b1;
    for (int i = 0; i < 8; i++) begin
        spif.wFIFO_wdata = make_wfifo_data(0, 2'b00, 2'b00, 64'hAABBCCDD + i);
        #(CLK_PERIOD);
    end

    spif.wFIFO_WEN = 1'b0;
    #(CLK_PERIOD);
    if (spif.wFIFO_full !== 1'b1) $error("wFIFO full not asserted");

    $finish;
end

endmodule

// `include "scratchpad_bank_if.vh"
// // `include "socetlib_fifo_if.vh"

// `timescale 1ns / 10ps

// module scratchpad_bank_tb();

// localparam CLK_PERIOD = 10;

// logic tb_clk;
// logic tb_nrst;

// always
// begin
//     tb_clk = 1'b0;
//     #(CLK_PERIOD);
//     tb_clk = 1'b1;
//     #(CLK_PERIOD);
// end

// scratchpad_bank_if spif ();
// scratchpad_bank DUT (.CLK(tb_clk), .nRST(tb_nrst), .spif(spif));

// string tb_test_case = "INIT";
// integer tb_test_num = 0;

// initial begin
//     tb_nrst = 1'b1;
//     spif.wFIFO_WEN = 1'b0;
//     spif.wFIFO_wdata = '0;
//     spif.rFIFO_WEN = 1'b0;
//     spif.rFIFO_wdata = '0;
//     spif.dramFIFO_REN = 1'b0;
//     spif.gemmFIFO_REN = 1'b0;

//     tb_test_case = "Reset DUT";
//     #(CLK_PERIOD);
//     tb_nrst = 1'b0;
//     #(CLK_PERIOD);
//     tb_nrst = 1'b1;
//     #(CLK_PERIOD);

//     if (spif.wFIFO_full != 1'b0 || spif.rFIFO_full != 1'b0 ||
//         spif.load_complete != 1'b0 || spif.gemm_complete != 1'b0 ||
//         spif.dramFIFO_empty != 1'b1 || spif.gemmFIFO_empty != 1'b1) $error("Reset DUT failed");

//     #(CLK_PERIOD);

//     // Write and Load Complete
//     tb_test_case = "Write and Load Complete";
//     tb_test_num++;

//     // Mat 0 Row 3
//     spif.wFIFO_WEN = 1'b1;
//     spif.wFIFO_wdata = {1'b0, 2'b00, 2'b11, 64'hDEADBEEFDEADBEEF};
//     #(CLK_PERIOD);
//     spif.wFIFO_WEN = 1'b0;
//     #(CLK_PERIOD * 4);
//     if (spif.load_complete != 1'b1) $error("Test Case 1 failed");

//     #(CLK_PERIOD);

//     // GEMM Complete
//     tb_test_case = "GEMM Complete";
//     tb_test_num++;

//     spif.wFIFO_WEN = 1'b1;
//     spif.wFIFO_wdata = {1'b1, 2'b00, 2'b00, 64'hBEEFCAFEBEEFCAFE};
//     #(CLK_PERIOD);
//     spif.wFIFO_WEN = 1'b0;
//     #(CLK_PERIOD * 4);
//     if (spif.gemm_complete != 1'b1) $error("Test Case 2 failed");

//     #(CLK_PERIOD);

//     // Read
//     tb_test_case = "DRAM FIFO Read";
//     tb_test_num++;

//     spif.rFIFO_WEN = 1'b1;
//     spif.rFIFO_wdata = {32'h10000000, 2'b00, 2'b01, 2'b10}; // Mat 1, Row 2
//     #(CLK_PERIOD);
//     spif.rFIFO_WEN = 1'b0;
//     #(CLK_PERIOD * 4);

//     // Read
//     tb_test_case = "GEMM FIFO Read";
//     tb_test_num++;

//     spif.rFIFO_WEN = 1'b1;
//     spif.rFIFO_wdata = {32'h20000000, 2'b01, 2'b10, 2'b11}; // Mat 2, Row 3
//     #(CLK_PERIOD);

//     $finish;
// end

// endmodule