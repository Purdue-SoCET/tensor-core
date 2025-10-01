`include "vector_if.vh"
`include "vector_types.vh"

`timescale 1 ns / 1 ns

module masku_tb;
  import vector_pkg::*;

  parameter PERIOD = 10ns;
  // Interface + DUT
  vector_if vif();
  masku     dut(.vif(vif)); // masku (vector_if.masku vif)

  // Small helper: drive inputs, compute expected, and check
  task automatic do_test(string name,
                         logic vm, int unsigned vl, int unsigned imm,
                         logic [NUM_ELEMENTS*ESZ-1:0] vmask_bits);
    logic [NUM_ELEMENTS-1:0] exp;
    exp = '0;

    // Drive
    vif.masku_in.vm    = vm;
    vif.masku_in.vl    = vl;
    vif.masku_in.imm   = imm;
    vif.masku_in.vmask = vmask_bits;
    #1;

    // Expectation (matches spec)
    if (vm == 1'b0) begin
      exp = '1;
    end else begin
      for (int i = 0; i < NUM_ELEMENTS; i++) begin
        if (vl <= i) exp[i] = 1'b0;
        else         exp[i] = vmask_bits[i*ESZ + imm];
      end
    end

    // Check
    if (vif.masku_out.mask !== exp)
      $error("[%s] MISMATCH exp=0x%0h got=0x%0h", name, exp, vif.masku_out.mask);
    else
      $display("[%s] PASS mask=0x%0h", name, exp);
  endtask

  initial begin
    string test_case = "";
    // VM low case
    test_case = "VM low";
    vif.masku_in.vm    = 1'b0;
    vif.masku_in.vl    = 32;
    vif.masku_in.imm   = 4'd16;
    vif.masku_in.vmask = '1; //{32{16'b100}};
    #(PERIOD);

    // parsing mask case
    test_case = "Parsing mask";
    vif.masku_in.vm    = 1'b1;
    vif.masku_in.vl    = '1;
    vif.masku_in.imm   = 4'd0;
    vif.masku_in.vmask = {32{16'b1}};
    #(PERIOD);
    $stop;
  end
endmodule
 