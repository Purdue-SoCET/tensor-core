

module socetlib_fifo #(
    parameter type T = logic [7:0], // type of a FIFO entry
    parameter DEPTH = 8 // # of FIFO entries
)(
    input CLK,
    input nRST,
    input WEN,
    input REN,
    input clear,
    input T wdata,
    output logic full,
    output logic empty,
    output logic underrun, 
    output logic overrun,
    output logic [$clog2(DEPTH+1)-1:0] count,
    output T rdata
);

    // Parameter checking
    
    // Width can be any number of bits > 1, but depth must be a power-of-2 to accomodate addressing scheme
    // TODO: 
    generate
        if(DEPTH == 0 || (DEPTH & (DEPTH - 1)) != 0) begin
            $error("%m: DEPTH must be a power of 2 >= 1!");
        end
    endgenerate
    
    localparam int ADDR_BITS = $clog2(DEPTH);

    logic overrun_next, underrun_next;
    logic [ADDR_BITS-1:0] write_ptr, write_ptr_next, read_ptr, read_ptr_next;
    logic [$clog2(DEPTH+1)-1:0] count_next;
    T [DEPTH-1:0] fifo, fifo_next;

    always_ff @(posedge CLK, negedge nRST) begin
        if(!nRST) begin
            fifo <= '{default: '0};
            write_ptr <= '0;
            read_ptr <= '0;
            overrun <= 1'b0;
            underrun <= 1'b0;
            count <= '0;
        end else begin
            fifo <= fifo_next;
            write_ptr <= write_ptr_next;
            read_ptr <= read_ptr_next;
            overrun <= overrun_next;
            underrun <= underrun_next;
            count <= count_next;
        end
    end

    always_comb begin
        fifo_next = fifo;
        write_ptr_next = write_ptr;
        read_ptr_next = read_ptr;
        overrun_next = overrun;
        underrun_next = underrun;
        count_next = count;

        if(clear) begin
            // No need to actually reset FIFO data,
            // changing pointers/flags to "empty" state is OK
            write_ptr_next = '0;
            read_ptr_next = '0;
            overrun_next = 1'b0;
            underrun_next = 1'b0;
            count_next = '0;
        end else begin
            if(REN && !empty && !(full && WEN)) begin
                read_ptr_next = read_ptr + 1;
            end else if(REN && empty) begin
                underrun_next = 1'b1;
            end

            if(WEN && !full && !(empty && REN)) begin
                write_ptr_next = write_ptr + 1;
                fifo_next[write_ptr] = wdata;
            end else if(WEN && full) begin
                overrun_next = 1'b1;
            end

            if (count == DEPTH) begin
                count_next = count - REN + (REN && WEN);
            end else if (count == 0) begin
                count_next = count + WEN - (REN && WEN);
            end else begin
                count_next = count + WEN - REN;
            end
        end
    end

    assign full = count == DEPTH;
    assign empty = count == 0;
    assign rdata = fifo[read_ptr];
endmodule