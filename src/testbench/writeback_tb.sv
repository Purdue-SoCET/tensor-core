`include "writeback_if.vh"
`include "cpu_types.vh"
`include "types_pkg.vh"

`timescale 1 ns / 1 ns

module writeback_tb;
  string tb_test_case = "INIT";
  logic CLK = 0;
  parameter PERIOD = 10;

  always #(PERIOD/2) CLK++;

  writeback_if wbif ();
  writeback DUT(.wbif(wbif));

  task check_outputs;
    input string test_name;
    input logic [31:0] expected_wbdata;
  begin
    if (expected_wbdata == wbif.wb_data) begin
      $display("%s PASSED", test_name);
    end else begin
      $display("%s FAILED. Expected: %h", test_name, expected_wbdata);
    end
  end
  endtask

  initial begin
    tb_test_case = "ALU Writeback";
    wbif.wb_select = '0;
    wbif.alu_out = 32'hDEADBEEF;
    wbif.store_out = 32'h00000100;
    #(PERIOD);
    check_outputs(tb_test_case, 32'hDEADBEEF);
    #(PERIOD*10);
    
    tb_test_case = "L/S Writeback";
    wbif.wb_select = '1;
    wbif.alu_out = 32'hDEADBEEF;
    wbif.store_out = 32'h00000100;
    #(PERIOD);
    check_outputs(tb_test_case, 32'h00000100);
    #(PERIOD*10);

    $stop;
  end
endmodule