`timescale 1ns/1ps
`include "memory/scratchpad/scpad_types_pkg.vh"
`include "memory/scratchpad/scratchpad_if.vh"

module r_fsm_tb;

logic clk;
logic n_rst;

// Instantiate the interface
scpad_if sif();

// DUT hooked up to generic vc_frontend modport
r_fsm #(.VC_ID(0)) dut (
    .clk(clk),
    .n_rst(n_rst),
    .sif(sif.vc_frontend)
);

// Clock generation
initial clk = 0;
always #5 clk = ~clk; // 100 MHz

// Reset task
task reset_dut();
begin
    n_rst = 0;
    sif.frontend_req        = '0;
    sif.sram_busy           = 0;
    sif.frontend_sram_read_res = '0;
    sif.frontend_sram_write_res = '0;
    sif.read_complete       = 0;
    #20;
    n_rst = 1;
end
endtask

initial begin
    $display("[%0t] Starting r_fsm_tb...", $time);
    reset_dut();

    // === Test 1: issue one request ===
    @(posedge clk);
    sif.frontend_req.valid    <= 1;
    sif.frontend_req.scpad_id <= 4'h1;
    @(posedge clk);
    sif.frontend_req.valid    <= 0;

    wait(sif.frontend_sram_read_req.valid);
    $display("[%0t] Req issued: scpad_id=%0d", $time, sif.frontend_sram_read_req.scpad_id);

    repeat (3) @(posedge clk);
    sif.frontend_sram_read_res.valid <= 1;
    sif.frontend_sram_read_res.rdata <= 32'hDEADBEEF;
    @(posedge clk);
    sif.frontend_sram_read_res.valid <= 0;

    repeat (2) @(posedge clk);
    sif.read_complete <= 1;
    @(posedge clk);
    sif.read_complete <= 0;

    wait(sif.frontend_res.valid);
    $display("[%0t] FSM responded with rdata=%h", $time, sif.frontend_res.rdata);

    // === Test 2: back-to-back requests ===
    repeat (2) begin
        @(posedge clk);
        sif.frontend_req.valid    <= 1;
        sif.frontend_req.scpad_id <= $urandom_range(0,15);
        @(posedge clk);
        sif.frontend_req.valid    <= 0;

        wait(sif.frontend_sram_read_req.valid);

        repeat (2) @(posedge clk);
        sif.frontend_sram_read_res.valid <= 1;
        sif.frontend_sram_read_res.rdata <= $random;
        @(posedge clk);
        sif.frontend_sram_read_res.valid <= 0;

        repeat (2) @(posedge clk);
        sif.read_complete <= 1;
        @(posedge clk);
        sif.read_complete <= 0;

        wait(sif.frontend_res.valid);
        $display("[%0t] FSM response: rdata=%h", $time, sif.frontend_res.rdata);
    end

    $display("[%0t] All tests completed!", $time);
    $finish;
end


endmodule
