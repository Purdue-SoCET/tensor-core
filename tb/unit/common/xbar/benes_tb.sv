// // `timescale 1ns / 1ns

// // module benes_tb;
// //     localparam int PERIOD = 10;
// //     localparam int SIZE = 32;
// //     localparam int DWIDTH = 16;
// //     localparam int TAGWIDTH = $clog2(SIZE);
// //     localparam int STAGES = (2 * TAGWIDTH) - 1;
// //     localparam int BITWIDTH = STAGES * (SIZE >> 1);

// //     logic clk, n_rst;
// //     logic [BITWIDTH-1:0] control_bit ;

// //     initial clk = 1'b0;
// //     always  #5 clk = ~clk;
    
// //     xbar_if #(.SIZE(SIZE), .DWIDTH(DWIDTH)) xif (.clk(clk), .n_rst(n_rst));
// //     benes #(.SIZE(SIZE), .DWIDTH(DWIDTH)) DUT (xif, control_bit);

// //     integer i;
// //     logic [15:0] val;
// //     logic [DWIDTH-1:0] exp_out [SIZE-1:0];

// //     // REQUIRED FOR TESTING WITH CBG

// //     // typedef logic [DWIDTH-1:0] vec_t [SIZE];
// //     // vec_t in, exp_out;

// //     // function automatic void make_vec(output logic [TAGW-1:0] exp_out [SIZE-1:0]);
// //     //     logic [DWIDTH-1:0] idx [SIZE-1:0];
// //     //     logic [DWIDTH-1:0] tmp;
// //     //     integer i, j, tmp;

// //     //     for (i = 0; i < 32; i++)
// //     //     idx[i] = i;

// //     //     for (i = 31; i > 0; i--) begin
// //     //         j = $urandom_range(0, i); // random index to swap
// //     //         tmp = idx[i];
// //     //         idx[i] = idx[j];
// //     //         idx[j] = tmp;
// //     //     end

// //     //     for (i = 0; i < 32; i++)
// //     //         exp_out[i] = idx[i];

// //     // endfunction

// // initial begin
// //     n_rst = 0;

// //     #(PERIOD);

// //     n_rst = 1;
// //     val = 16'd0;

// //     for (i = 0; i < 32; i = i + 1) begin
// //         xif.in[i] = val;
// //         val = val + 16'd1;
// //     end
// //     exp_out = {16'd27, 16'd24, 16'd2, 16'd29, 16'd4, 16'd7, 16'd20, 16'd10, 16'd1, 16'd0, 16'd8, 16'd9, 16'd3, 16'd13, 16'd16, 16'd26,
// //                     16'd12, 16'd31, 16'd17, 16'd19, 16'd28, 16'd18, 16'd23, 16'd30, 16'd5, 16'd15, 16'd6, 16'd21, 16'd11, 16'd25, 16'd22, 16'd14};
    
// //     control_bit = 144'b111000110101110001100100110011100111001110000000111100000001101100101011001100000000000000000000001000011001000001110110011110001011111001001100;  
    
// //     repeat (10) #(PERIOD);
    
// //     for (i = 0; i < 32; i = i + 1) begin
// //         if(xif.out[i] != exp_out[(SIZE-1 - i)]) begin
// //             $display("wrong output for %d", i);
// //         end
// //         // $display("output %d: %d", i, xif.out[i]);
// //     end
// //     $finish;
// // end

// // endmodule










`timescale 1ns/1ns
`include "xbar_params.svh"
`include "xbar_if.sv"

module benes_tb;
    localparam int SIZE = 32;
    localparam int DWIDTH = 16;
    localparam int TAGW = $clog2(SIZE); // 5
    localparam int STAGES = (2 * TAGW) - 1; // 9 benes stages
    localparam int BITWIDTH = STAGES * (SIZE >> 1); // 9 * 16 = 144 control bits

    localparam logic [7:0] REGISTER_MASK = 8'b11111111;  // pipeline taps
    localparam int REAL_LATENCY = $countones(REGISTER_MASK) + 1; // 9 cycles

    localparam int N_REQS = (REAL_LATENCY * 2);  
    localparam int VEC_PER_CASE = (REAL_LATENCY);
    localparam bit REVERSE_LANES = 0; 

    logic clk, n_rst;
    initial clk = 1'b0;
    always #5 clk = ~clk;

    logic [BITWIDTH-1:0] control_bit;
    xbar_if #(.SIZE(SIZE), .DWIDTH(DWIDTH)) xif (.clk(clk), .n_rst(n_rst));
    benes #(.SIZE(SIZE), .DWIDTH(DWIDTH), .REGISTER_MASK(REGISTER_MASK)) dut (.xif(xif.xbar), .control_bit(control_bit));

    typedef logic [DWIDTH-1:0] vec_t [SIZE];
    vec_t exp_q[$];  // expected vectors with scoreboard

    // 32 lane vector with random 16 bit value
    function automatic void make_vec(output vec_t v);
        for (int i = 0; i < SIZE; i++) v[i] = $urandom();
    endfunction

    task automatic drive_vec(input vec_t v);
        for (int i = 0; i < SIZE; i++) begin
            xif.in[i].din = v[i];
            xif.in[i].shift = TAGW'(i); // tag lanes
        end
    endtask

    // checking a fixed permutation
    task automatic drive_linear();
        for (int i = 0; i < SIZE; i++) begin
            xif.in[i].din = DWIDTH'(i);
            xif.in[i].shift = TAGW'(i);
        end
    endtask

    // copy all outputs into 32 lane vector in 1 shot
    task automatic sample_vec(output vec_t v);
        for (int i = 0; i < SIZE; i++) v[i] = xif.out[i];
    endtask

    task automatic build_expected(input vec_t in, output vec_t exp, input int map[SIZE]);
        for (int j = 0; j < SIZE; j++) exp[j] = in[map[j]];
    endtask

    // check current control bit implements the permutation map
    // in: permutation expect (out2in), out: counts output lanes don't match expected value
    task automatic check_linear_against_map(input int map[SIZE], output int mismatches);
        mismatches = 0;
        for (int c = 0; c < REAL_LATENCY + 2; c++) begin
            drive_linear();
            @(posedge clk);
        end
        for (int j = 0; j < SIZE; j++) begin
            logic [DWIDTH-1:0] want = DWIDTH'( map[j] );
            if (xif.out[j] !== want) begin
                $display("[CTRL][LINEAR][ERR] lane%0d: got=%0d exp=%0d", j, xif.out[j], want);
                mismatches++;
            end
        end
    endtask

    // streaming verification for general permutation
    task automatic stream_check_using_map(input int map[SIZE], input int num_vecs, inout int errors, output int retired_cnt);
        vec_t in_vec, exp_vec, got_vec;
        retired_cnt = 0;
        int launched_local = 0;
        for (int t = 0; t < num_vecs; t++) begin
            if (launched_local <= REAL_LATENCY) begin
                make_vec(in_vec);
                build_expected(in_vec, exp_vec, map);
                exp_q.push_back(exp_vec);
                launched_local++;
                drive_vec(in_vec);
            end
            @(posedge clk);
            if (launched_local >= REAL_LATENCY) begin
                exp_vec = exp_q.pop_front();
                sample_vec(got_vec);
                int mm = 0;
                for (int k = 0; k < SIZE; k++) begin
                    if (got_vec[k] !== exp_vec[k]) begin
                        mm++; errors++;
                        $display("[CTRL][STREAM][ERR] lane%0d: got=%0d exp=%0d", k, got_vec[k], exp_vec[k]);
                    end
                end
                if (mm == 0) begin 
                    $display("[CTRL][STREAM] retire=%0d OK", retired_cnt);
                end else begin
                    $display("[CTRL][STREAM] retire=%0d mismatches=%0d", retired_cnt, mm);
                end
                retired_cnt++;
            end
        end
    endtask

    int launched, retired, errors;

    initial begin : main
        vec_t in_vec, exp_vec, got_vec;
        int mismatches;

        n_rst = 1'b0;
        xif.en = 1'b0;
        control_bit = '0;  // identity
        for (int i = 0; i < SIZE; i++) begin
            xif.in[i].din = '0;
            xif.in[i].shift = TAGW'(i);
        end

        repeat (5) @(posedge clk);
        n_rst = 1'b1;
        @(posedge clk);
        xif.en = 1'b1;

        launched = 0;
        retired = 0;
        errors = 0;

        for (int t = 0; t < N_REQS; t++) begin
            if (launched <= REAL_LATENCY) begin
                make_vec(in_vec); // random in
                for (int i = 0; i < SIZE; i++) // expected = input 
                    exp_vec[i] = in_vec[i];
                exp_q.push_back(exp_vec); // save for later
                launched++;
                drive_vec(in_vec);
            end

            @(posedge clk);

            if (launched >= REAL_LATENCY) begin
                exp_vec = exp_q.pop_front();
                sample_vec(got_vec);
                mismatches = 0;
                for (int k = 0; k < SIZE; k++) begin
                    if (got_vec[k] !== exp_vec[k]) begin
                        mismatches++; errors++;
                        $display("[ID] lane%0d: got=%0d exp=%0d", k, got_vec[k], exp_vec[k]);
                    end
                end

                if (mismatches == 0)
                    $display("[ID][Complete] retire=%0d OK", retired);
                else
                    $display("[ID][Complete] retire=%0d mismatches=%0d", retired, mismatches);
                retired++;
            end
        end

        // Expected out->in mapping (index of input that should appear at each output)
        logic [DWIDTH-1:0] exp_map [SIZE] = '{
            16'd27, 16'd24, 16'd2,  16'd29, 16'd4,  16'd7,  16'd20, 16'd10,
            16'd1,  16'd0,  16'd8,  16'd9,  16'd3,  16'd13, 16'd16, 16'd26,
            16'd12, 16'd31, 16'd17, 16'd19, 16'd28, 16'd18, 16'd23, 16'd30,
            16'd5,  16'd15, 16'd6,  16'd21, 16'd11, 16'd25, 16'd22, 16'd14
        };

        // test case by hand
        control_bit = 144'b111000110101110001100100110011100111001110000000111100000001101100101011001100000000000000000000001000011001000001110110011110001011111001001100;
        $display("\n[SCENARIO 2] Single fixed control-bit case");
        $display("[CASE] control_bit = 0x%0h", control_bit);

        // Build int map (optionally reversed)
        int out2in[SIZE];
        for (int j = 0; j < SIZE; j++) begin
            int idx = REVERSE_LANES ? (SIZE-1-j) : j;
            out2in[j] = exp_map[idx];
        end

        int retired_case;
        int mism_lin;

        check_linear_against_map(out2in, mism_lin);
        if (mism_lin == 0) begin 
            $display("[CASE] linear check OK");
        end else begin 
            $display("[CASE] linear mismatches=%0d", mism_lin);
        end
        errors += mism_lin;

        // Streaming check
        stream_check_using_map(out2in, VEC_PER_CASE, errors, retired_case);
        $display("[CASE] stream retired=%0d", retired_case);

        xif.en = 1'b0;
        $display("\n[TB][Summary] total errors=%0d, latency=%0d", errors, REAL_LATENCY);
        $finish;
    end
endmodule
