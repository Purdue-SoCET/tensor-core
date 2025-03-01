module memory_testbench;
    import "DPI-C" function void mem_init();
    import "DPI-C" function void mem_read(input bit [31:0] address, output bit [31:0] data);
    import "DPI-C" function void mem_write(input bit [31:0] address, input bit [31:0] data);

    bit [31:0] read_data;

    initial begin
        mem_init();
        #10;
        mem_write(0, 32'hDEADBEEF);
        #10;
        mem_read(0, read_data);
        $display("Data at address 0: %h", read_data);
        #10;
        $finish;
    end
endmodule