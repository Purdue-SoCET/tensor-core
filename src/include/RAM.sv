class RAM;

    logic [31:0] ram_data [logic [31:0]];

    function new();
    endfunction

    function logic [31:0] read(logic [31:0] addr);
        if (ram_data.exists(addr)) begin
            return ram_data[addr];
        end else begin
            return 32'd0;
        end
    endfunction

    function void write(logic [31:0] addr, logic [31:0] data);
        ram_data[addr] = data;
    endfunction

endclass