`include "vector_if.vh"
`include "vector_types.vh"

module veggie_tb;
    import vector_pkg::*;

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

    task reset_dut();
        begin
            vif.nRST = 0; // Assert reset
            vif.veggie_in = '{default:'0}; // Keep inputs quiet during reset
            repeat (5) @(posedge vif.CLK);
            vif.nRST = 1; // De-assert reset
            @(posedge vif.CLK);
        end
    endtask

    task automatic veggie_set_reads(
        input vsel_t vs_by_port   [READ_PORTS],
        input bit    ren_by_port  [READ_PORTS] = '{default:1'b1}
    );
    // ex usage:
    //   vsel_t vs_arr   [READ_PORTS] = '{ 'h12, 'h34, 'h56, 'h78 }; // example for READ_PORTS==4
    //   bit    ren_arr  [READ_PORTS] = '{ 1, 0, 1, 1 };
    //   veggie_set_reads(vs_arr, ren_arr);
    
    foreach (vs_by_port[i]) begin
        vif.veggie_in.vs [i] = vs_by_port[i];
        vif.veggie_in.REN[i] = ren_by_port[i];
    end
    endtask

    
    task automatic veggie_set_writes(
        input vsel_t vd_by_port     [WRITE_PORTS],
        input vreg_t vdata_by_port  [WRITE_PORTS],
        input bit    wen_by_port    [WRITE_PORTS]
    );
        foreach (vd_by_port[i]) begin
            vif.veggie_in.vd   [i] = vd_by_port[i];
            vif.veggie_in.vdata[i] = vdata_by_port[i];
            vif.veggie_in.WEN  [i] = wen_by_port[i];
        end
    endtask
    
    task automatic veggie_set_mask_reads(
        input mask_sel_t vms_by_port [MASK_BANK_COUNT],
        input bit        mren_by_port[MASK_BANK_COUNT] = '{default:1'b1}
    );
        foreach (vms_by_port[i]) begin
            vif.veggie_in.vms [i] = vms_by_port[i];
            vif.veggie_in.MREN[i] = mren_by_port[i];
        end
    endtask

    // Bulk-set all MASK WRITE ports
    task automatic veggie_set_mask_writes(
        input mask_sel_t            vmd_by_port   [MASK_BANK_COUNT],
        input logic [VLMAX-1:0]     mvdata_by_port[MASK_BANK_COUNT],
        input bit                   mwen_by_port  [MASK_BANK_COUNT] = '{default:1'b0}
    );
        foreach (vmd_by_port[i]) begin
            vif.veggie_in.vmd   [i] = vmd_by_port[i];
            vif.veggie_in.mvdata[i] = mvdata_by_port[i];
            vif.veggie_in.MWEN  [i] = mwen_by_port[i];
        end
    endtask
    
    initial begin
        string testname;

        vif.CLK  = 1'b0;

        $display("=====================================================");
        $display("Veggie Testbench Starting...");
        $display("=====================================================");

        // --- Reset Sequence ---
        testname = "Reset";
        reset_dut();    
        
        //-------------------------------------------------
        // TEST 0: Bank Addr Mapping
        //-------------------------------------------------
        $display("Veggie Testbench Starting...");
        testname = "Writing with no Conflict";
        //veggie_set_reads('{ 8'h04, 8'h05, 8'h06, 8'h07 }, '{ 1, 1, 1, 1 });  
        veggie_set_writes('{ 8'h08, 8'h09, 8'h0A, 8'h0B }, '{ '1, '0, '1, '0}, '{ 1, 1, 1, 1 }); 
        //veggie_set_mask_reads('{ 4'h0, 4'h1 }, '{ 1, 1 });
        veggie_set_mask_writes('{ 4'h0, 4'h1 }, '{ 32'hFFFF_FFFF, 32'h0000_0000 }, '{ 1, 1 }); 
        #(50);

        //-------------------------------------------------
        // TEST 1: Simple Write, then Read
        //-------------------------------------------------
        // Simple write pattern: all-ones vector
        
        testname = "Read Testing";
        
        vif.veggie_in.WEN = '{default:1'b0};
        vif.veggie_in.MWEN = '{default:1'b0};

        veggie_set_reads('{ 8'h08, 8'h09, 8'h0A, 8'h0B }, '{ 1, 1, 1, 1 });
        veggie_set_mask_reads('{ 4'h0, 4'h1 }, '{ 1, 1 });
        #(30);

        testname = "Reset";
        reset_dut();   
        //-------------------------------------------------
        // TEST 0: Bank Addr Mapping
        //-------------------------------------------------
        testname = "Writing with Conflicts";
        //veggie_set_reads('{ 8'h04, 8'h05, 8'h06, 8'h07 }, '{ 1, 1, 1, 1 });  
        veggie_set_writes('{ 8'h00, 8'h04, 8'h08, 8'h0C }, '{ '1, '1, '0, '1}, '{ 1, 1, 1, 1 }); 
        //veggie_set_mask_reads('{ 4'h0, 4'h1 }, '{ 1, 1 });
        veggie_set_mask_writes('{ 4'h2, 4'h4 }, '{ 32'hCAFE_BABE, 32'hCAFE_F00D }, '{ 1, 1 }); 
        #(40);
        vif.veggie_in.WEN = '{default:1'b0};
        vif.veggie_in.MWEN = '{default:1'b0};

        testname = "Reading with Conflicts";
        veggie_set_reads('{ 8'h00, 8'h04, 8'h08, 8'h0C }, '{ 1, 1, 1, 1 });  
        veggie_set_mask_reads('{ 4'h2, 4'h4 }, '{ 1, 1 });
        #(120);


        /*

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
        */
        $stop;
    end

endmodule
