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
    localparam logic [15:0][15:0] normal_slopes = '{
        16'h37FE, 16'h37AA, 16'h3773, 16'h373F,
        16'h3711, 16'h36E3, 16'h36BB, 16'h369B,
        16'h3679, 16'h3655, 16'h3634, 16'h3615,
        16'h35FD, 16'h35E5, 16'h35C9, 16'h35AD
    };
    
    localparam logic [15:0][15:0] normal_intercepts = '{
        16'h3800, 16'h382C, 16'h384C, 16'h386B,
        16'h3887, 16'h38A5, 16'h38C1, 16'h38D8,
        16'h38F2, 16'h390E, 16'h3928, 16'h3943,
        16'h3958, 16'h396E, 16'h3988, 16'h39A3
    };
    
    localparam logic [15:0][15:0] subnormal_slopes = '{
        16'h43D9, 16'h3EA9, 16'h3D19, 16'h3C4B,
        16'h3B90, 16'h3AD6, 16'h3A49, 16'h39D9,
        16'h397E, 16'h3932, 16'h38F1, 16'h38B9,
        16'h3887, 16'h385B, 16'h3834, 16'h3811
    };

    localparam logic [15:0][15:0] subnormal_intercepts = '{
        16'h29B7, 16'h30C2, 16'h3242, 16'h3371,
        16'h343A, 16'h34AE, 16'h3517, 16'h3578,
        16'h35D3, 16'h3628, 16'h367A, 16'h36C7,
        16'h3711, 16'h3758, 16'h379D, 16'h37DF
    };

    localparam MULT_LATENCY = 2;

    // STAGE 1: INPUT DECOMPOSITION AND TABLE LOOKUP
    
    logic       sign, sign_n;
    logic [4:0] exponent, exponent_n;
    logic [9:0] mantissa, mantissa_n;
    
    logic [15:0] input_slope;
    logic [15:0] input_intercept;
    logic [15:0] normalized_mantissa;
    logic [3:0]  index;
    logic        is_subnormal;
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
        
        // Determine if input is subnormal
        is_subnormal = ~|exponent;
        index = mantissa[9:6];
        
        // Select appropriate slope and intercept
        if (is_subnormal) begin
            normalized_mantissa = {1'b0, 5'd0, mantissa};
            input_slope         = subnormal_slopes[15 - index];
            input_intercept     = subnormal_intercepts[15 - index];
        end else begin
            normalized_mantissa = {1'b0, 5'd15, mantissa};
            input_slope         = normal_slopes[15 - index];
            input_intercept     = normal_intercepts[15 - index];
        end
    end

    // SPECIAL CASE HANDLING

    logic        special;
    logic [15:0] special_result;
    
    always_comb begin
        special        = 1'b1;
        special_result = 16'h0000;

        casez ({sign, exponent, mantissa})
            // Infinity or NaN
            {1'b?, 5'b11111, 10'b??????????}: begin
                if (mantissa != 10'b0) begin
                    special_result = 16'h7e00;  // NaN
                end else if (!sign) begin
                    special_result = 16'h7C00;  // +Inf
                end else begin
                    special_result = 16'h7e00;  // -Inf -> NaN
                end
            end
            
            // Positive zero
            {1'b0, 5'b00000, 10'b0000000000}: begin
                special_result = 16'h0000;
            end
            
            // Negative zero
            {1'b1, 5'b00000, 10'b0000000000}: begin
                special_result = 16'h8000;
            end
            
            // Any other negative number
            {1'b1, 5'b?????, 10'b??????????}: begin
                special_result = 16'h7e00;  // NaN
            end
            
            default: special = 1'b0;
        endcase
    end

    // MULTIPLIER 1: slope * normalized_mantissa
    
    logic [15:0] mult1_product;
    logic mult1_done;
    mul_fp16 mul1 (.clk(CLK), .nRST(nRST), .start(valid), .a(input_slope), .b(normalized_mantissa), .done(mult1_done), .result(mult1_product));

    // PIPELINE STAGE: Delay intercept and odd exponent flag
    
    logic [15:0] intercept_pipe [0:MULT_LATENCY-1];
    logic        odd_exp_pipe   [0:MULT_LATENCY-1];
    
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            intercept_pipe <= '{default:'0};
            odd_exp_pipe   <= '{default:'0};
        end else begin
            intercept_pipe[0] <= input_intercept;
            odd_exp_pipe[0]   <= exponent[0];
            
            for (int i = 1; i < MULT_LATENCY; i++) begin
                intercept_pipe[i] <= intercept_pipe[i-1];
                odd_exp_pipe[i]   <= odd_exp_pipe[i-1];
            end
        end
    end


    // ADDER: mult1_product + intercept
    
    vaddsub_if add1_if();
    vaddsub add1(CLK, nRST, add1_if);
    
    logic [15:0] sqrt_sum;
    
    always_comb begin
        add1_if.port_a = mult1_product;
        add1_if.port_b = intercept_pipe[MULT_LATENCY-1];
        add1_if.sub    = 1'b0;
        add1_if.enable = 1'b1;
        sqrt_sum       = add1_if.out;
    end

    // ODD EXPONENT ADJUSTMENT

    
    logic [15:0] odd_exp_adj;
    
    always_comb begin
        if (odd_exp_pipe[MULT_LATENCY-1]) begin
            odd_exp_adj = 16'h3DA8;  // sqrt(2)
        end else begin
            odd_exp_adj = 16'h3C00;  // 1.0
        end
    end
    

    // MULTIPLIER 2: sqrt_sum * odd_exp_adj

    
    logic [15:0] mult2_product;
    
    mul_fp16 mul2 (.clk(CLK), .nRST(nRST), .start(mult1_done), .a(sqrt_sum), .b(odd_exp_adj), .done(valid_data_out), .result(mult2_product));


    // EXPONENT PIPELINE

    
    logic [4:0] exponent_pipe [0:(2*MULT_LATENCY)-1];
    logic [4:0] final_exp;
    
    assign final_exp = is_subnormal ? 5'b0 : exponent >> 1;
    
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            exponent_pipe <= '{default:'0};
        end else begin
            exponent_pipe[0] = final_exp;
            
            for (int i = 1; i < 2 * MULT_LATENCY; i++) begin
                exponent_pipe[i] <= exponent_pipe[i-1];
            end
        end
    end


    // SPECIAL CASE PIPELINE

    
    logic [15:0] special_result_pipe [0:(2*MULT_LATENCY)-1];
    logic        special_flag_pipe   [0:(2*MULT_LATENCY)-1];
    
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            special_flag_pipe   <= '{default:'0};
            special_result_pipe <= '{default:'0};
        end else begin
            special_flag_pipe[0]   <= special;
            special_result_pipe[0] <= special_result;
            
            for (int i = 1; i < 2 * MULT_LATENCY; i++) begin
                special_flag_pipe[i]   <= special_flag_pipe[i-1];
                special_result_pipe[i] <= special_result_pipe[i-1];
            end
        end
    end
    

    // OUTPUT RECOMBINATION

    
    always_comb begin
        if (special_flag_pipe[(2*MULT_LATENCY)-1]) begin
            output_val = special_result_pipe[(2*MULT_LATENCY)-1];
        end else begin
            output_val = {
                1'b0,
                exponent_pipe[(2*MULT_LATENCY)-1] + mult2_product[14:10] - 5'd15,
                mult2_product[9:0]
            };
        end
    end


endmodule