// `include "isa_types.vh"
// `include "datapath_types.vh"
// `include "fu_gemm_if.vh"

module fu_gemm(
    input logic CLK, 
    input logic nRST, 
    fu_gemm_if.GEMM fugif
);

logic [3:0] next_reg1, next_reg2, next_reg3, next_regd;
logic ready, next_ready;
logic [3:0] counter, next_counter;

//pipeline later with weights
always_ff @(posedge CLK, negedge nRST) begin
    if(nRST == 0) begin
        fugif.rs1 <= '0;
        fugif.rs2 <= '0;
        fugif.rs3 <= '0;
        fugif.rd <= '0;
        ready <= '0;
        weight1 <= '0;
        weight2 <= '0;
        weight3 <= '0;
        weightd <= '0;
        counter <= '0;
    end
    else begin
        fugif.rs1 <= next_reg1;
        fugif.rs2 <= next_reg2;
        fugif.rs3 <= next_reg3;
        fugif.rd <= next_regd;
        ready <= next_ready;
        weight1 <= next_weight1;
        weight2 <= next_weight2;
        weight3 <= next_weigth3;
        weightd <= next_weigth4;
        counter <= next_counter;
    end
end
always_comb begin
    if(counter == 4 && weight1 == next_weight1 && weight2 == next_weight2 && weight3 == next_weight3 && weightd == next_weightd) begin
        
end

always_comb begin
    next_reg1 = fugif.rs1;
    next_reg2 = fugif.rs2;
    next_reg3 = fugif.rs3;
    next_regd = fugif.rd;
    next_ready = ready;
    
    next_weight1 = weight1;
    next_weight2 = weight2;
    next_weight3 = weight3;
    next_weight4 = weightd;
    next_counter = counter;
    

    if(fugif.flush) begin
        next_reg1 = '0;
        next_reg2 = '0;
        next_reg3 = '0;
        next_regd = '0;
        next_ready = '0;

        next_counter = '0;
        next_weight1 = '0;
        next_weight2 = '0;
        next_weight3 = '0;
        next_weight4 = '0;
    end
    else if (fugif.freeze) begin
        next_ready = 0; //want to not assert a ready value in case there is a freeze
    end 
    else begin
        next_reg1 = fugif.fetch_p[10:7]; 
        next_reg2 = fugif.fetch_p[14:11];
        next_reg3 = fugif.fetch_p[18:15];
        next_regd = fugif.fetch_p[22:19];
        next_ready = 1;

        next_counter = counter + 1;
        next_weight1 = fugif.weight1;
        next_weight2 = fugif.weight2;
        next_weight3 = fugif.weight3;
        next_weight4 = fugif.weightd;
    end

end

endmodule