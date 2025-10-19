/*  Paramertized Circular Buffer Module 
    Nick Taha: tahan@purdue.edu
*/

module buffer_module #(
    parameter BUFFER_WIDTH = 32, // Size of Input
    parameter BUFFER_DEPTH = 32  // Depth of Buffer (How many values of data)
) (
    input logic CLK, nRST,
    input logic write_en,                   // Write Enable
    input logic read_en,                    // Read Enable
    input logic [BUFFER_WIDTH-1:0] din,     // "Data in" into buffer upon write enable
    output logic [BUFFER_WIDTH-1:0] dout,   // "Data out" out of buffer upon read enable
    output logic full,                      // Full signal indicating buffer is at capacity
    output logic empty                      // Empty signal indicating buffer has not data
);
    
    // Index values for read and write pointers
    integer read_idx, write_idx;
    integer next_read_idx, next_write_idx;

    // Count values for Empty and Full signals
    integer count, next_count;

    // Packed arrray holding the data per parameters
    logic [BUFFER_DEPTH - 1 : 0][BUFFER_WIDTH - 1: 0] shift_reg, next_shift_reg;

    // logic for outputting d_out?? Created to solve possible issues outputting two values during one period of read enable
    logic [BUFFER_WIDTH - 1 : 0] next_dout;

    always_ff @(posedge CLK, negedge nRST) begin : curr_reg

        if (!nRST) begin
            shift_reg   <= '0;    
            write_idx   <= 1;   // Write pointer indicates next write index
            read_idx    <= 0;   // Read pointer indicates current read index
            dout        <= '0;
            count       <= 0;
        end
        else begin
            shift_reg   <= next_shift_reg;
            write_idx   <= next_write_idx;
            read_idx    <= next_read_idx;
            dout        <= next_dout;
            count       <= next_count;
        end
    end

    always_comb begin : next_reg_logic
        next_shift_reg  = shift_reg;
        next_write_idx  = write_idx;
        next_read_idx   = read_idx;
        next_dout       = '0;

        if (write_en && !full) begin
            next_shift_reg[write_idx - 1] = din;
            next_write_idx = (write_idx == BUFFER_DEPTH) ? 1 : write_idx + 1;
        end

        if (read_en && !empty) begin
            next_dout = shift_reg[read_idx];
            next_shift_reg[read_idx] = '0;
            next_read_idx = ((read_idx + 1) == BUFFER_DEPTH) ? 0 : read_idx + 1;
        end
    end

    always_comb begin : count_logic
        next_count = count;
        if (read_en && !empty && !write_en) begin
            next_count = count - 1;
        end
        else if (write_en && !full && !read_en) begin
            next_count = count + 1;
        end
    end

    assign full = (count == BUFFER_DEPTH);
    assign empty = (count == 0);

endmodule