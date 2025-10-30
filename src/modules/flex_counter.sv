module flex_counter #( parameter N=5 ) (
    input  logic  CLK, nRST,
    input  logic  enable,
    input  logic  [N-1:0] count_load,
    input  logic  clear, //Add by Tri for pressing into 0
    output logic  [N-1:0] count,
    output logic  count_done
);

logic [N-1:0] next_count;
logic prev_enable, en_rising_edge;

// ENABLE RISING EDGE DETECT
always_ff @(posedge CLK, negedge nRST) begin
    if (~nRST) begin
        prev_enable <= 1'b0;
    end
    else begin
        prev_enable <= enable;
    end
end

always_comb begin : ENABLE_EDGE_DET
    en_rising_edge = enable && (~prev_enable);
end

// COUNTER LOGIC
always_ff @(posedge CLK, negedge nRST) begin
    if (~nRST) begin
        //count <= count_load;
        count <= '0;
    end
    else if (clear) begin
        count <= 0;
    end
    else begin
        count <= next_count;
    end    
end

always_comb begin
    if (en_rising_edge == 1'b1) begin
        next_count = count_load - 1;        // -1 because 1 cycle taken to load the value
    end

    else begin
        next_count = count - 1;
        
        if (count == '0) begin
            next_count = '0;
        end
    end
end

assign count_done = (count == '0) ? 1'b1 : 1'b0;

endmodule