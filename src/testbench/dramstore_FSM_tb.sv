`include "dramstore_FSM_if.vh"

`timescale 1ns / 10ps

module dramstore_FSM_tb();

localparam CLK_PERIOD = 10;

logic tb_clk;
logic tb_nrst;

// Clock generation
always
begin
    tb_clk = 1'b0;
    #(CLK_PERIOD / 2.0);
    tb_clk = 1'b1;
    #(CLK_PERIOD / 2.0);
end

dramstore_FSM_if spif ();
dramstore_FSM DUT (.CLK(tb_clk), .nRST(tb_nrst), .spif(spif));

string tb_test_case = "INIT";
integer tb_test_num = 0;

initial begin
    // Reset
    tb_test_case = "RESET";
    tb_nrst = 1'b0;

    #(CLK_PERIOD * 2);
    tb_nrst = 1'b1;
    #(CLK_PERIOD * 2);

    #10;

    tb_test_case = "Empty FIFOs and sStore_hit LOW";
    tb_test_num = tb_test_num + 1;
    $display("Empty FIFOs and sStore_hit LOW");
    spif.dramFIFO0_empty = 1'b1;
    spif.dramFIFO1_empty = 1'b1;
    spif.dramFIFO2_empty = 1'b1;
    spif.dramFIFO3_empty = 1'b1;
    spif.dramFIFO0_rdata = {32'h00000010, 2'b00, 64'hDEADBEEFDEADBEEF};
    spif.sStore_hit = 1'b0;
    spif.dramFIFO0_rdata = '0;
    spif.dramFIFO1_rdata = '0;
    spif.dramFIFO2_rdata = '0;
    spif.dramFIFO3_rdata = '0;
    $display("sStore = %b, store_addr = %h, store_data = %h", spif.sStore, spif.store_addr, spif.store_data);
    #10;

    tb_test_case = "FIFO0 Not Empty and sStore_hit HIGH";
    tb_test_num = tb_test_num + 1;
    $display("FIFO0 Not Empty and sStore_hit HIGH");
    spif.dramFIFO0_empty = 1'b0;
    spif.sStore_hit = 1'b1;
    spif.dramFIFO0_rdata = {32'h00000010, 2'b00, 64'hDEADBEEFDEADBEEF};
    #10;
    $display("sStore = %b, store_addr = %h, store_data = %h", spif.sStore, spif.store_addr, spif.store_data);

    tb_test_case = "FIFO1 Not Empty and sStore_hit HIGH";
    tb_test_num = tb_test_num + 1;
    $display("FIFO1 Not Empty and sStore_hit HIGH");
    spif.dramFIFO0_empty = 1'b1;
    spif.dramFIFO1_empty = 1'b0;
    spif.sStore_hit = 1'b1;
    spif.dramFIFO1_rdata = {32'h00000020, 2'b01, 64'hBEEFDEADBEEFDEAD};
    #10;
    $display("sStore = %b, store_addr = %h, store_data = %h", spif.sStore, spif.store_addr, spif.store_data);

    tb_test_case = "FIFO2 Not Empty and sStore_hit HIGH";
    tb_test_num = tb_test_num + 1;
    $display("FIFO2 Not Empty and sStore_hit HIGH");
    spif.dramFIFO0_empty = 1'b1;
    spif.dramFIFO1_empty = 1'b1;
    spif.dramFIFO2_empty = 1'b0;
    spif.sStore_hit = 1'b1;
    spif.dramFIFO2_rdata = {32'h00000030, 2'b10, 64'hDEADDEADBEEFBEEF};
    #10;
    $display("sStore = %b, store_addr = %h, store_data = %h", spif.sStore, spif.store_addr, spif.store_data);

    tb_test_case = "FIFO3 Not Empty and sStore_hit HIGH";
    tb_test_num = tb_test_num + 1;
    $display("FIFO3 Not Empty and sStore_hit HIGH");
    spif.dramFIFO0_empty = 1'b1;
    spif.dramFIFO1_empty = 1'b1;
    spif.dramFIFO2_empty = 1'b1;
    spif.dramFIFO3_empty = 1'b0;
    spif.sStore_hit = 1'b1;
    spif.dramFIFO3_rdata = {32'h00000040, 2'b11, 64'hBEEFBEEFDEADDEAD};
    #10;
    $display("sStore = %b, store_addr = %h, store_data = %h", spif.sStore, spif.store_addr, spif.store_data);

    #10;

    $finish;
end

endmodule