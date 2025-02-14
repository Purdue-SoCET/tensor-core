// Matrix LS unit testbench
// tahan

`timescale 1ns/1ps
`include "datapath_types.vh"
`include "isa_types.vh"
`include "fu_matrix_ls_if.vh"

module fu_matrix_ls_tb;

    // importing types
    import datapath_pkg::*;
    import isa_pkg::*;
    import isa_pkg::*;

    fu_matrix_ls_if.tb mlsif();

    fu_matrix_ls DUT (
        .mlsif(mlsif)
    );

    //-------------------------------------------------------------------------
    // Task: check_outputs
    // This task checks that the DUT's outputs match the expected values.
    // Parameters:
    //   expected_ls      : expected 2-bit ls_out (e.g., 2'b01 for LOAD, 2'b10 for STORE)
    //   expected_rd      : expected destination (or forwarded) register value (rd_out)
    //   expected_stride  : expected stride value (stride_out, of type word_t)
    //   expected_address : expected computed address
    //   expected_done    : expected value for done (should equal mhit)
    //-------------------------------------------------------------------------
    // task check_outputs(
    //     input [1:0]    expected_ls,
    //     input [4:0]    expected_rd,
    //     input word_t   expected_stride,
    //     input [10:0]   expected_address,
    //     input logic    expected_done
    // );
    // begin
    //      // Check ls_out
    //      assert(mlsif.fu_matls_out.ls_out == expected_ls)
    //         else $error("ERROR at time %0t: Expected ls_out = %b, got %b", 
    //                     $time, expected_ls, mlsif.fu_matls_out.ls_out);
    //      // Check rd_out
    //      assert(mlsif.fu_matls_out.rd_out == expected_rd)
    //         else $error("ERROR at time %0t: Expected rd_out = %0d, got %0d", 
    //                     $time, expected_rd, mlsif.fu_matls_out.rd_out);
    //      // Check stride_out
    //      assert(mlsif.fu_matls_out.stride_out == expected_stride)
    //         else $error("ERROR at time %0t: Expected stride_out = %0d, got %0d", 
    //                     $time, expected_stride, mlsif.fu_matls_out.stride_out);
    //      // Check address
    //      assert(mlsif.fu_matls_out.address == expected_address)
    //         else $error("ERROR at time %0t: Expected address = %0d, got %0d", 
    //                     $time, expected_address, mlsif.fu_matls_out.address);
    //      // Check done signal
    //      assert(mlsif.fu_matls_out.done == expected_done)
    //         else $error("ERROR at time %0t: Expected done = %b, got %b", 
    //                     $time, expected_done, mlsif.fu_matls_out.done);
    // end
    // endtask

    //-------------------------------------------------------------------------
    // Test Stimulus and Verification Block
    //-------------------------------------------------------------------------
    initial begin
        // --- Initialization ---
        // Set initial values for all input signals.
        mlsif.enable    = 0;         // Module disabled initially
        mlsif.ls_in     = 2'b00;     // No operation selected
        mlsif.rd_in     = 5'd0;      // Initialize destination register value
        mlsif.rs_in     = '0;        // Initialize source register (word_t)
        mlsif.stride_in = '0;        // Initialize stride (word_t)
        mlsif.imm_in    = 11'd0;     // Initialize immediate value
        mlsif.mhit      = 0;         // Scratchpad not ready initially
        #10;                        // Wait 10 ns for stabilization

        // --- Test Case 1: LOAD Operation ---
        // For LOAD:
        //   - ls_in should be set to 2'b01.
        //   - rd_out should equal rd_in.
        //   - Address is computed as rs_in + imm_in.
        //   - done should follow mhit.
        mlsif.enable    = 1;         // Enable the module
        mlsif.ls_in     = 2'b01;     // LOAD operation selected (bit0 high)
        mlsif.rd_in     = 5'd15;     // Example destination register value
        mlsif.rs_in     = 32'd100;   // Example source register value (assume word_t is 32-bit)
        mlsif.stride_in = 32'd5;     // Example stride value
        mlsif.imm_in    = 11'd20;    // Immediate value (address = rs_in + imm_in)
        mlsif.mhit      = 1;         // Scratchpad ready; done should be 1
        #20;                        // Allow time for combinational logic to settle

        // Check outputs for LOAD operation.
        // Expected:
        //   ls_out = 2'b01,
        //   rd_out = 15,
        //   stride_out = 5,
        //   address = 100 + 20 = 120,
        //   done = 1.
        // check_outputs(2'b01, 5'd15, 32'd5, 11'd120, 1);

        // --- Test Case 2: STORE Operation ---
        // For STORE:
        //   - ls_in should be set to 2'b10.
        //   - rd_out should now be driven by rs_in.
        //   - Address is computed as rd_in + imm_in.
        //   - done remains equal to mhit.
        mlsif.ls_in     = 2'b10;     // STORE operation selected (bit1 high)
        mlsif.rd_in     = 5'd25;     // Used for address calculation (address = rd_in + imm_in)
        mlsif.rs_in     = 32'd200;   // For STORE, rd_out should reflect rs_in
        mlsif.stride_in = 32'd3;     // Example stride value
        mlsif.imm_in    = 11'd30;    // Immediate value (address = 25 + 30 = 55)
        // mlsif.mhit remains 1; done should still be 1
        #20;                        // Wait for combinational logic to settle

        // Check outputs for STORE operation.
        // Expected:
        //   ls_out = 2'b10,
        //   rd_out = 200,
        //   stride_out = 3,
        //   address = 55,
        //   done = 1.
        // check_outputs(2'b10, 5'd200, 32'd3, 11'd55, 1);

        // --- Test Case 3: Disable Operation ---
        // Disable the module to verify that no operation is performed.
        mlsif.enable = 0;
        mlsif.ls_in  = 2'b00;
        #20;

        // End the simulation
        $finish;
    end

endmodule

