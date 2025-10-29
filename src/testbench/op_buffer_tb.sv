
module op_buffer_tb;
    import vector_pkg::*;

    // Testbench Parameters
    localparam CLK_PERIOD = 10; // 10ns clock period -> 100MHz

    // 1. Instantiate the Interface
    vector_if vif();

    // 2. Instantiate the DUT (Device Under Test)
    op_buffer dut (
        .CLK(vif.CLK),
        .nRST(vif.nRST),
        .vif(vif.op_buffer)
    );

    // 3. Clock Generator
    always #(CLK_PERIOD/2) vif.CLK = ~vif.CLK;

    task reset_dut();
        begin
            vif.nRST = 0; // Assert reset
            vif.opbuff_in = '{default:'0}; // Keep inputs quiet during reset
            repeat (5) @(posedge vif.CLK);
            vif.nRST = 1; // De-assert reset
            @(posedge vif.CLK);
        end
    endtask

    initial begin
        string testname;

        vif.CLK  = 1'b0;


        reset_dut();

        // Test Case 1
        testname = "4 reads no conflict";
        
        vif.opbuff_in.vreg   = '{default: '{default: '{sign:1'b1, exp:'1, frac:'1}}}; 
        vif.opbuff_in.dvalid = '1;
        vif.opbuff_in.vmask  = '{default:'1};
        vif.opbuff_in.mvalid = '1;
        vif.opbuff_in.ready = 1'b1;
        
        #(CLK_PERIOD);
        
    end
endmodule