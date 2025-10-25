`include "vector_types.vh"
`include "vaddsub_if.vh"

module sqrt (
    input  logic        CLK,
    input  logic        nRST,
    input  logic        valid_data_in,
    input  logic [15:0] input_val,
    output logic [15:0] output_val,
    output logic        valid_data_out
);    
    localparam logic [15:0] normal_slopes [0:15] = '{
        16'h37FE, 16'h37AA, 16'h3773, 16'h373F,
        16'h3711, 16'h36E3, 16'h36BB, 16'h369B,
        16'h3679, 16'h3655, 16'h3634, 16'h3615,
        16'h35FD, 16'h35E5, 16'h35C9, 16'h35AD
    };
    
    localparam logic [15:0] normal_intercepts [0:15] = '{
        16'h3800, 16'h382C, 16'h384C, 16'h386B,
        16'h3887, 16'h38A5, 16'h38C1, 16'h38D8,
        16'h38F2, 16'h390E, 16'h3928, 16'h3943,
        16'h3958, 16'h396E, 16'h3988, 16'h39A3
    };

    localparam MULT_LATENCY = 2;

    // STAGE 1: INPUT DECOMPOSITION AND TABLE LOOKUP
    
    logic       sign, sign_n;
    logic [4:0] exponent, exponent_n, final_exp, final_exp_out;
    logic [9:0] mantissa, mantissa_n;
    
    logic [15:0] input_slope;
    logic [15:0] input_intercept;
    logic [15:0] normalized_mantissa;
    logic [3:0]  index;
    logic        is_subnormal, is_subnormal_output, is_odd, is_odd_output;
    logic        valid, valid_n;

    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            sign     <= '0;
            exponent <= '0;
            mantissa <= '0;
            valid <= '0;
        end else begin
            sign     <= sign_n;
            exponent <= exponent_n;
            mantissa <= mantissa_n;
            valid <= valid_n;
        end
    end

    always_comb begin

        sign_n     = input_val[15];
        exponent_n = input_val[14:10];
        mantissa_n = input_val[9:0];
        valid_n = valid_data_in;
        
        // Determine if input is subnormal (will output 0)
        is_subnormal = ~|exponent_n;
        index = mantissa_n[9:6];
        is_odd = exponent_n[0];
        
        // Use normal slopes and intercepts for all calculations
        normalized_mantissa = {1'b0, 5'd15, mantissa_n};
        input_slope         = normal_slopes[index];
        input_intercept     = normal_intercepts[index];

        // Calculate final exponent
        final_exp = exponent_n >> 1;
    end
    
    //final exponent pipe
    sqrt_pipe #(.DATA_WIDTH(5), .STAGES(2*MULT_LATENCY + 2)) exp_pipe (.CLK(CLK), .nRST(nRST), .enable(valid_n), .data_in(final_exp), .data_out(final_exp_out));
    //is odd pipe
    sqrt_pipe #(.DATA_WIDTH(1), .STAGES(MULT_LATENCY + 2)) odd_pipe (.CLK(CLK), .nRST(nRST), .enable(valid_n), .data_in(is_odd), .data_out(is_odd_output));
    //is subnormal pipe
    //intercept synchronization 
    logic [15:0] intercept_pipe_output;
    sqrt_pipe #(.DATA_WIDTH(16), .STAGES(MULT_LATENCY)) intercept_pipe (.CLK(CLK), .nRST(nRST), .enable(valid_n), .data_in(input_intercept), .data_out(intercept_pipe_output));

    //slope * normalized mantissa
    logic [15:0] mult1_product;
    logic mult1_done;
    mul_fp16 mult1 (.clk(CLK), .nRST(nRST), .start(valid_n), .a(normalized_mantissa), .b(input_slope), .done(mult1_done), .result(mult1_product));

    //adding the intercept
    vaddsub_if add1_if();
    vaddsub add1(CLK, nRST, add1_if);

    logic [15:0] sqrt_sum, sqrt_sum_comb;
    
    always_comb begin
        add1_if.port_a = mult1_product;
        add1_if.port_b = intercept_pipe_output;
        add1_if.sub    = 1'b0;
        add1_if.enable = 1'b1;
        sqrt_sum_comb       = add1_if.out;
    end
    logic mult2_start, mult1_done_delay;
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            sqrt_sum <= 16'h0000;
            mult1_done_delay <= 1'b0;
            mult2_start <= 1'b0;
        end
        else begin
            sqrt_sum <= sqrt_sum_comb;
            mult1_done_delay <= mult1_done;
            mult2_start <= mult1_done_delay;
        end
    end 

    //sqrt_sum * adjustment factor based on odd exponent
    logic [15:0] mult2_product, exp_adj;
    logic mult2_done;

    always_comb begin
        if (is_odd_output) begin
            exp_adj = 16'h3da8;  // sqrt(2)
        end
        else begin
            exp_adj = 16'h3C00;  // 1.0
        end
    end
    mul_fp16 mult2 (.clk(CLK), .nRST(nRST), .start(mult2_start), .a(sqrt_sum), .b(exp_adj), .done(mult2_done), .result(mult2_product));


    //recombination
    logic [15:0] final_value;
    always_comb begin
        // If input was subnormal, output 0, otherwise compute result
        if (is_subnormal_output) begin
            final_value = 16'h0000;
        end else begin
            final_value = {1'b0, final_exp_out + mult2_product[14:10], mult2_product[9:0]};
        end
    end

    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            output_val <= 'b0;
            valid_data_out <= 'b0;
        end
        else begin
            output_val <= final_value;
            valid_data_out <= mult2_done;
        end
    end
endmodule