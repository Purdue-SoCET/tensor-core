`include "ram_if.vh"
`include "ram_pkg.vh"

module ram #(
    parameter DATA_WIDTH = 32,   // Data bus width
    parameter ADDR_WIDTH = 10,   // Address bus width
    parameter INIT_FILE = "meminit.bin", // Memory initialization file
    parameter LAT = 6
)(
    input logic CLK, nRST,
    ram_if.ram ramif
);

    import ram_pkg::*;

    ramstate_t rstate;

    // Memory declaration (2^ADDR_WIDTH locations)
    reg [DATA_WIDTH-1:0] mem [0:(1<<ADDR_WIDTH)-1];

    logic [31:0] count;
    logic [2:0] next_count;
    logic [ADDR_WIDTH-1:0] last_addr;
    logic last_wen;
    logic last_ren;

    always_ff @ (posedge CLK) begin
        if (ramif.ramWEN && count == LAT) begin
            mem[ramif.ramaddr] <= ramif.ramstore;
        end

        if (count == LAT) begin
            ramif.ramload <= mem[ramif.ramaddr];
        end else begin
            ramif.ramload <= 32'hBADBAD;
        end
    end

    always_comb begin
        next_count = count;
        rstate = FREE;
        if (ramif.ramWEN || ramif.ramREN) rstate = ACCESS;
        if (last_addr != ramif.ramaddr || ramif.ramWEN != last_wen || ramif.ramREN != last_ren) begin
            next_count = 32'b0;
            rstate = BUSY;
        end else if (count < LAT && (ramif.ramWEN || ramif.ramREN)) begin
            next_count = count + 32'b1;
            rstate = BUSY;
        end
    end

    always_ff @ (posedge CLK, negedge nRST) begin
        if (~nRST) begin
            count <= '0;
            last_addr <= '0;
            last_wen <= '0;
            last_ren <= '0;
        end else begin
            count <= next_count;
            last_addr <= ramif.ramaddr;
            last_wen <= ramif.ramWEN;
            last_ren <= ramif.ramREN;
        end
    end

    // Load memory from file at startup
    initial begin
        $readmemb(INIT_FILE, mem);
    end

endmodule