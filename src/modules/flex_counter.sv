module flex_counter #( parameter N=5 ) (
    input  logic  clk, nRST,
    input  logic  enable,
    input  logic  [N-1:0] count_load,
    output logic  [N-1:0] count,
    output logic  count_done
);

logic [N-1:0] next_count;

always_ff @(posedge clk, negedge nRST) begin
    if (~nRST) begin
        //count <= count_load;
        count <= '0;
    end
    
    else begin
        count <= next_count;
    end    
end

always_comb begin
    next_count = count;

    if (enable) begin
        next_count = count + 1;
    end

    if (count == count_load) begin
        next_count = '0;
    end
end

assign count_done = (count == count_load) ? 1'b1 : 1'b0;

endmodule