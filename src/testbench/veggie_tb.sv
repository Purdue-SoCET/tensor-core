`include "vector_if.vh"
`include "vector_types.vh"

module veggie_tb;

    // Testbench Parameters
    localparam CLK_PERIOD = 10; // 10ns clock period -> 100MHz

    // 1. Instantiate the Interface
    vector_if vif();

    // 2. Instantiate the DUT (Device Under Test)
    veggie #(
        .BANK_COUNT      (4),
        .MASK_BANK_COUNT (2),
        .DREAD_PORTS     (4),
        .DWRITE_PORTS    (4),
        .MREAD_PORTS     (2),
        .MWRITE_PORTS    (2)
    ) dut (
        .CLK(vif.CLK),
        .nRST(vif.nRST),
        .vif(vif.veggie) // Connect to the veggie modport of the interface
    );

    // 3. Clock Generator
    always #(CLK_PERIOD/2) vif.CLK = ~vif.CLK;

    // 4. Main Test Sequence
    initial begin
        $display("=====================================================");
        $display("Veggie Testbench Starting...");
        $display("=====================================================");

        // --- Reset Sequence ---
        vif.CLK = 0;
        vif.nRST = 0; // Assert reset
        vif.veggie_in = '{default:'0}; // Keep inputs quiet during reset
        repeat (5) @(posedge vif.CLK);
        vif.nRST = 1; // De-assert reset
        @(posedge vif.CLK);
        
        //-------------------------------------------------
        // TEST 1: Simple Write, then Read
        //-------------------------------------------------
        // Simple write pattern: all-ones vector
        vif.veggie_in.WEN[0]   = 1'b1;
        vif.veggie_in.vd[0]    = 5;       // row index
        vif.veggie_in.vdata[0] = '1;      // write 1's across the whole vreg

        @(posedge vif.CLK);
        vif.veggie_in = '{default:'0};
        @(posedge vif.CLK);

        // Read back on port 0 from same row
        vif.veggie_in.REN[0] = 1'b1;
        vif.veggie_in.vs[0]  = 5;

        @(posedge vif.CLK);
        vif.veggie_in = '{default:'0};
        @(posedge vif.CLK);

        // Check result on read port 0
        assert (vif.veggie_out.vreg[0] == '1)
        else $fatal(1, "[TEST 1] FAILED: Read data mismatch.");
        $display("[TEST 1] PASSED: Successfully read back the written value.");

        // --- End of Simulation ---
        $display("\n=====================================================");
        $display("All tests completed successfully!");
        $display("=====================================================");
        $finish;
    end

endmodule
