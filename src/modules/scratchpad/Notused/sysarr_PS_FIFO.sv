module PS_FIFO #(
    parameter N = 4, 
    parameter WIDTH = 16
)(
    input logic clk, nRST,
    systolic_array_ps_fifo_if.PS_FIFO ps_fifo
);
    // Internal storage for Partial sums FIFO
    logic [2 * WIDTH * N - 1 : 0] ps_fifo_mem; //need space for two arrays 2 rows of matrix rows
    logic [2 * WIDTH * N - 1 : 0] ps_fifo_mem_next;

    always_ff @(posedge clk or negedge nRST) begin
        if (!nRST) begin
            ps_fifo_mem <= '0;     // Reset fifo mem to all zeros
        end else begin
            ps_fifo_mem <= ps_fifo_mem_next; 
        end
    end
    always_comb begin
        ps_fifo_mem_next = ps_fifo_mem;
        ps_fifo.out = ps_fifo_mem[WIDTH - 1 : 0]; // Output from the last row
        if (ps_fifo.load) begin
            ps_fifo_mem_next[2 * WIDTH * N - 1 : WIDTH * N - 1] = ps_fifo.load_values;    // Load into first row
        end else if (ps_fifo.shift)begin
            ps_fifo_mem_next = ps_fifo_mem >> WIDTH;    // Shift values forward 
        end
    end

endmodule