`timescale 1ns/1ps

module vbank_tb;

    // Parameters
    localparam INDEX_WIDTH = 5;
    localparam NUM_ELEMENTS = 32;
    localparam DATA_WIDTH = 16;
    localparam NUM_ROWS = 8;

    // DUT signals
    logic clk;
    logic ren, wen;
    logic [INDEX_WIDTH-1:0] raddr, waddr;
    logic [DATA_WIDTH*NUM_ELEMENTS-1:0] rdata, wdata;
    logic [NUM_ELEMENTS-1:0] wstrb;

    // DUT instantiation
    vbank #(
        .INDEX_WIDTH(INDEX_WIDTH),
        .NUM_ELEMENTS(NUM_ELEMENTS),
        .DATA_WIDTH(DATA_WIDTH),
        .NUM_ROWS(NUM_ROWS)
    ) dut (
        .clk(clk),
        .ren(ren),
        .raddr(raddr),
        .rdata(rdata),
        .wen(wen),
        .waddr(waddr),
        .wdata(wdata),
        .wstrb(wstrb)
    );

    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;

    // Test procedure
    initial begin
        // Initialize
        ren = 0;
        wen = 0;
        raddr = 0;
        waddr = 0;
        wdata = '0;
        wstrb = '0;

        // Wait for reset
        #10;

        // Write to row 3, all elements
        waddr = 5'd3;
        wdata = {NUM_ELEMENTS{16'hA5A5}}; // All elements = 0xA5A5
        wstrb = '1; // Write all elements
        wen = 1;
        #10;
        wen = 0;

        // Read from row 3
        raddr = 5'd3;
        ren = 1;
        #10;
        ren = 0;

        // Check read data
        if (rdata !== {NUM_ELEMENTS{16'hA5A5}})
            $error("Read data mismatch!");

        // Write to row 2, only element 0
        waddr = 5'd2;
        wdata = {NUM_ELEMENTS{16'h1234}};
        wstrb = '0;
        wstrb[0] = 1'b1; // Only first element
        wen = 1;
        #10;
        wen = 0;

        // Read from row 2
        raddr = 5'd2;
        ren = 1;
        #10;
        ren = 0;

        // Check only first element written
        if (rdata[0 +: DATA_WIDTH] !== 16'h1234)
            $error("Element 0 mismatch!");
        if (rdata[DATA_WIDTH +: DATA_WIDTH*(NUM_ELEMENTS-1)] !== {(NUM_ELEMENTS-1){16'h0000}})
            $error("Other elements mismatch!");

        $display("vbank_tb: All tests passed.");
        $finish;
    end

endmodule