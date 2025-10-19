// Credit: https://www.chipverify.com/verilog/synchronous-fifo
// https://www.chipverify.com/images/verilog/sync_fifo.svg

module sync_fifo #(
    parameter DEPTH = 8, 
    parameter DWIDTH = 16
) (
    input rstn, clk, wr_en, rd_en, 
    input [DWIDTH-1:0] din, 	
    output reg [DWIDTH-1:0] dout, 	
    output  empty,  full 			
);
    reg [$clog2(DEPTH)-1:0]   wptr;
    reg [$clog2(DEPTH)-1:0]   rptr;

    reg [DWIDTH-1 : 0]    fifo[DEPTH];

    always_ff @(posedge clk, negedge rstn) begin
        if (!rstn) begin
            wptr <= 0;
        end else begin
            if (wr_en & !full) begin
                fifo[wptr] <= din;
                wptr <= wptr + 1;
            end
        end
    end

    always_ff @(posedge clk, negedge rstn) begin
        if (!rstn) begin
            rptr <= 0;
        end else begin
            if (rd_en & !empty) begin
                dout <= fifo[rptr];
                rptr <= rptr + 1;
            end
        end
    end

    assign full  = (wptr + 1) == rptr;
    assign empty = wptr == rptr;
endmodule