module fifo #(
    parameter DATA_WIDTH = 32,
    parameter FIFO_SIZE  = 2
) (
    input logic CLK, nRST,
    input logic [DATA_WIDTH-1:0] input,     
    input logic push,
    input logic pop,
    output logic [DATA_WIDTH-1:0] output,    
    output logic stall  
);

    localparam PTR_WIDTH = $clog2(FIFO_SIZE);

    logic [DATA_WIDTH-1:0][0:FIFO_SIZE-1] fifo, next_fifo;
    logic [PTR_WIDTH:0] occupancy, next_occupancy;
    logic [PTR_WIDTH-1:0] head, next_head;
    logic [PTR_WIDTH-1:0] tail, next_tail;

    assign stall = (occupancy == FIFO_SIZE);
    assign output = fifo[tail];

    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            fifo <= '0;
            occupancy <= 0;
            head <= 0;
            tail <= 0;
        end else begin
            fifo <= next_fifo;
            occupancy <= next_occupancy;
            head <= next_head;
            tail <= next_tail;
        end
    end

    always_comb begin
        next_fifo = fifo;
        next_occupancy = occupancy;
        next_head = head;
        next_tail = tail;

        if (push && pop && !stall) begin
            next_fifo[head] = input;
            next_head = (head == FIFO_SIZE - 1) ? 0 : head + 1;
            next_tail = (tail == FIFO_SIZE - 1) ? 0 : tail + 1;
        end
        else if (push && !pop && !stall) begin
            next_fifo[head] = input;
            next_occupancy = occupancy + 1;
            next_head = (head == FIFO_SIZE - 1) ? 0 : head + 1;
        end
        else if (!push && pop) begin
            next_occupancy = occupancy - 1;
            next_tail = (tail == FIFO_SIZE - 1) ? 0 : tail + 1;
        end
    end

endmodule
