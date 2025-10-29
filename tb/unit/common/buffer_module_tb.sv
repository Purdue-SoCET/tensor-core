`timescale 1ns/1ps

module buffer_module_tb;

    // Set test parameters
    localparam TB_WIDTH = 32;
    localparam TB_DEPTH = 8; // Using a smaller depth for testing

    logic clk;
    logic nRST;
    logic write_en;
    logic read_en;
    logic [TB_WIDTH-1:0] din;
    logic [TB_WIDTH-1:0] dout;
    logic full;
    logic empty;

    // Instantiate the DUT and pass clk/nRST separately
    buffer_module #(TB_WIDTH, TB_DEPTH) dut (
        .CLK(clk),
        .nRST(nRST),
        .write_en(write_en),
        .read_en(read_en),
        .din(din),
        .dout(dout),
        .full(full),
        .empty(empty)
    );

    // Clock generation (10ns period)
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end


    initial begin

        /* Test Case 0: nRST*/
        nRST = 0;
        write_en = 0;
        read_en = 0;
        din = 0;
        #20;
        
        // Release reset
        nRST = 1;
        #10;

        $display("=== Starting Buffer Test ===");

        /* Test Case 1: Writing 5 Values to Buffer*/
        for (int i = 1; i <= 6; i++) begin
            din = i * 100;
            write_en = 1;
            #10;
            write_en = 0;
            #10;
        end

        /* Test Case 2: Reading 5 Values to Buffer*/
        for (int i = 1; i <= 6; i++) begin
            read_en = 1;
            #10;
            read_en = 0;
            #10;
        end

        /* Test Case 2: Writing to Buffer until Full Signal*/
        for (int i = 1; i <= TB_DEPTH; i++) begin
            din = i * 10;
            write_en = 1;
            #10;
            write_en = 0;
            #10;
        end

        /* Test Case 3: Writing to Buffer while FULL*/
        din = 9999;
        write_en = 1;
        #10;
        write_en = 0;
        #10;

        /* Test Case 4: Read All Values from Buffer to get EMPTY*/
        for (int i = 1; i <= TB_DEPTH; i++) begin
            read_en = 1;
            #10;
            read_en = 0;
            #10;
        end

        /* Test Case 5: Try and Read a Value while EMPTY*/
        read_en = 1;
        #10;
        read_en = 0;
        #10;
    
        /* Test Case 6: Simulatneous Reads and Writes*/
        write_en = 1;
        din = 40;
        #10;
        din = 80;
        read_en = 1;
        #10;
        din = 120;
        #10;
        din = 160;
        #10;
        read_en = 0;
        write_en = 0;
        #10;



        $display("=== Test Completed ===");
        $finish;
    end

endmodule