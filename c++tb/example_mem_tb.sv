module memory_testbench;
    import "DPI-C" function void mem_init();
    import "DPI-C" function void mem_read(input bit [31:0] address, output bit [31:0] data);
    import "DPI-C" function void mem_write(input bit [31:0] address, input bit [31:0] data);
    import "DPI-C" function void mem_save();


    bit [31:0] read_data;

    initial begin
        mem_init();
        #10;
        mem_write(5, 32'hDEADBEEF);
        #10;
        mem_read(5, read_data);
        $display("Data at address 5: %h", read_data);
        #10;
        mem_save();
        #10;
        $finish;
    end
endmodule