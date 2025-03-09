module FIFO #(
    parameter N = 4, 
    parameter WIDTH = 16
)(
    input logic clk, nRST,
    systolic_array_fifo_if.FIFO fifo
);
    // Internal storage for FIFO
    logic [2 * WIDTH * N - 1 : 0] fifo_mem; //need space for two arrays 2 rows of matrix rows
    logic [2 * WIDTH * N - 1 : 0] fifo_mem_next;

    always_ff @(posedge clk or negedge nRST) begin
        if (!nRST) begin
            fifo_mem <= '0;     // Reset fifo mem to all zeros
        end else begin
            fifo_mem <= fifo_mem_next; 
        end
    end
    always_comb begin
        fifo_mem_next = fifo_mem;
        fifo.out = fifo_mem[WIDTH * N - 1 : 0]; // Output from the last row
        if (fifo.load) begin
            fifo_mem_next[2 * WIDTH * N - 1 : WIDTH * N - 1] = fifo.load_values;    // Load into first row
        end else if (fifo.shift)begin
            fifo_mem_next = fifo_mem >> WIDTH;    // Shift values forward 
        end
    end

endmodule