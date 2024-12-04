module FIFO #(
    parameter array_dim = 4, 
    parameter data_w = 16
)(
    input logic clk, rst,
    input logic load, shift,
    input logic [data_w * array_dim - 1 : 0] load_values,
    output logic [data_w * array_dim - 1 : 0] out
);
    // Internal storage for FIFO
    logic [data_w * array_dim - 1 : 0] fifo_mem [array_dim-1:0];
    
    // Pointer for shifting data
    integer i;
    
    always_ff @(posedge clk or negedge rst) begin
        if (!rst) begin
            for (i = 0; i < array_dim; i++) begin
                fifo_mem[i] <= '0; // Reset fifo mem to all zeros
            end
        end else if (load) begin
            fifo_mem[0] <= load_values; // Load into first row
        end else if (shift) begin
            for (i = array_dim - 1; i >= 0; i--) begin
                fifo_mem[i] <= fifo_mem[i-1]; // Shift values forward 
            end
            fifo_mem[0] <= '0; // Shift in zeros to first row
        end
    end
    
    assign out = fifo_mem[array_dim-1]; // Output from the last row
    
endmodule