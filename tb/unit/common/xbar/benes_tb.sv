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














// `timescale 1ns/1ns
// `include "xbar_params.svh"
// `include "xbar_if.sv"

// module benes_tb;
//     localparam int SIZE = 32;
//     localparam int DWIDTH = 16;
//     localparam int TAGW = $clog2(SIZE); // 5
//     localparam int STAGES = (2 * TAGW) - 1; // 9 benes stages
//     localparam int BITWIDTH = STAGES * (SIZE >> 1); // 9 * 16 = 144 control bits

//     localparam logic [7:0] REGISTER_MASK = 8'b11111111;  // pipeline taps
//     localparam int REAL_LATENCY = $countones(REGISTER_MASK) + 1; // 9 cycles

//     localparam int N_REQS  = (REAL_LATENCY * 2);   // 2x latency vectors for scenario 1 
//     localparam int VEC_PER_CASE = (REAL_LATENCY); // short stream per control-bit for scenario 2
//     localparam bit REVERSE_LANES = 0; // flip to 1 if your exp_map is reversed

//     logic clk, n_rst;
//     initial clk = 1'b0;
//     always #5 clk = ~clk;

//     logic [BITWIDTH-1:0] control_bit;
//     xbar_if #(.SIZE(SIZE), .DWIDTH(DWIDTH)) xif (.clk(clk), .n_rst(n_rst));
//     benes #(.SIZE(SIZE), .DWIDTH(DWIDTH), .REGISTER_MASK(REGISTER_MASK)) dut (.xif(xif.xbar), .control_bit(control_bit));

//     typedef logic [DWIDTH-1:0] vec_t [SIZE];
//     vec_t exp_q[$];  // expected vectors with scoreboard

//     // 32 lane vector with random 16 bit value
//     function automatic void make_vec(output vec_t v);
//         for (int i = 0; i < SIZE; i++) v[i] = $urandom();
//     endfunction

//     task automatic drive_vec(input vec_t v);
//         for (int i = 0; i < SIZE; i++) begin
//             xif.in[i].din = v[i];
//             xif.in[i].shift = TAGW'(i); // tag lanes
//         end
//     endtask

//     // checking a fixed permutation
//     task automatic drive_linear();
//         for (int i = 0; i < SIZE; i++) begin
//             xif.in[i].din = DWIDTH'(i);
//             xif.in[i].shift = TAGW'(i);
//         end
//     endtask

//     // copy all outputs into 32 lane vector in 1 shot
//     task automatic sample_vec(output vec_t v);
//         for (int i = 0; i < SIZE; i++) v[i] = xif.out[i];
//     endtask

//     task automatic build_expected(input vec_t in, output vec_t exp, input int map[SIZE]);
//         for (int j = 0; j < SIZE; j++) exp[j] = in[map[j]];
//     endtask

//     // automatic discover permutation realized by current control bit setting 
//     // out: fill in out2in 
//     task automatic learn_mapping(output int out2in[SIZE]);
//         vec_t tok, got;
//         function automatic logic [DWIDTH-1:0] token(int idx);
//             return 16'hCA00 | DWIDTH'(idx);
//         endfunction

//         for (int i = 0; i < SIZE; i++) begin
//             for (int k = 0; k < SIZE; k++) tok[k] = '0;
//             tok[i] = token(i);

//             for (int c = 0; c < REAL_LATENCY + 1; c++) begin
//                 drive_vec(tok);
//                 @(posedge clk);
//             end

//             sample_vec(got);
//             int found = -1;
//             for (int j = 0; j < SIZE; j++) if (got[j] === token(i)) found = j;
//             if (found < 0) begin
//                 $display("[LEARN][ERR] token from in%0d not observed", i);
//                 out2in[0] = 0;
//             end else begin
//                 out2in[found] = i;
//             end
//         end
//     endtask

//     // check current control bit implements the permuation map
//     // in: permutation expect (out2in), out: counts output lanes don't match expected value
//     task automatic check_linear_against_map(input int map[SIZE], output int mismatches);
//         mismatches = 0;
//         // drive linear inputs for L+2 cycles to settle
//         for (int c = 0; c < REAL_LATENCY + 2; c++) begin
//             drive_linear();
//             @(posedge clk);
//         end
//         for (int j = 0; j < SIZE; j++) begin
//             logic [DWIDTH-1:0] want = DWIDTH'( map[j] );
//             if (xif.out[j] !== want) begin
//                 $display("[CTRL][LINEAR][ERR] lane%0d: got=%0d exp=%0d", j, xif.out[j], want);
//                 mismatches++;
//             end
//         end
//     endtask

//     // streaming verification for general permutation (get randim vectos, compute expected by applying permutation,
//     // align pipeline latency by scoreboard, compare lane by lane)
//     // in: out2in, num_vec (number of vectors to try) , out: count numeber of vectors were compared 
//     task automatic stream_check_using_map(input int map[SIZE], input int num_vecs, inout int errors, output int retired_cnt);
//         vec_t in_vec, exp_vec, got_vec;
//         retired_cnt = 0;
//         int launched_local = 0;
//         for (int t = 0; t < num_vecs; t++) begin
//             if (launched_local <= REAL_LATENCY) begin
//                 make_vec(in_vec);
//                 build_expected(in_vec, exp_vec, map);
//                 exp_q.push_back(exp_vec);
//                 launched_local++;
//                 drive_vec(in_vec);
//             end
//             @(posedge clk);
//             if (launched_local >= REAL_LATENCY) begin
//                 exp_vec = exp_q.pop_front();
//                 sample_vec(got_vec);
//                 int mm = 0;
//                 for (int k = 0; k < SIZE; k++) begin
//                     if (got_vec[k] !== exp_vec[k]) begin
//                         mm++; errors++;
//                         $display("[CTRL][STREAM][ERR] lane%0d: got=%0d exp=%0d", k, got_vec[k], exp_vec[k]);
//                     end
//                 end
//                 if (mm == 0) $display("[CTRL][STREAM] retire=%0d OK", retired_cnt);
//                 else          $display("[CTRL][STREAM] retire=%0d mismatches=%0d", retired_cnt, mm);
//                 retired_cnt++;
//             end
//         end
//     endtask

//     int launched, retired, errors;

//     initial begin : main
//         vec_t in_vec, exp_vec, got_vec;
//         int mismatches;

//         n_rst = 1'b0;
//         xif.en = 1'b0;
//         control_bit = '0;  // identity
//         for (int i = 0; i < SIZE; i++) begin
//             xif.in[i].din = '0;
//             xif.in[i].shift = TAGW'(i);
//         end

//         repeat (5) @(posedge clk);
//         n_rst = 1'b1;
//         @(posedge clk);
//         xif.en = 1'b1;

//         launched = 0;
//         retired = 0;
//         errors = 0;

//         // Scenario 1: identity streaming
//         for (int t = 0; t < N_REQS; t++) begin
//             if (launched <= REAL_LATENCY) begin
//                 make_vec(in_vec); // random in
//                 for (int i = 0; i < SIZE; i++) // expected = input 
//                     exp_vec[i] = in_vec[i];
//                 exp_q.push_back(exp_vec); // save for later
//                 launched++;
//                 drive_vec(in_vec); // drive DUT
//             end

//             @(posedge clk);

//             if (launched >= REAL_LATENCY) begin
//                 exp_vec = exp_q.pop_front();
//                 sample_vec(got_vec);

//                 mismatches = 0;
//                 for (int k = 0; k < SIZE; k++) begin
//                     if (got_vec[k] !== exp_vec[k]) begin
//                         mismatches++; errors++;
//                         $display("[ID] lane%0d: got=%0d exp=%0d", k, got_vec[k], exp_vec[k]);
//                     end
//                 end

//                 if (mismatches == 0)
//                     $display("[ID][Complete] retire=%0d OK", retired);
//                 else
//                     $display("[ID][Complete] retire=%0d mismatches=%0d", retired, mismatches);
//                 retired++;
//             end
//         end

//         //  Scenario 2: multicontrol bit cases
//         localparam int NUM_CTRL_CASES = 2;  
//         logic [BITWIDTH-1:0] ctrl_cases [NUM_CTRL_CASES];
//         bit has_map [NUM_CTRL_CASES];
//         logic [DWIDTH-1:0] exp_maps [NUM_CTRL_CASES][SIZE];

//         // Case 0: identity (sanity)
//         ctrl_cases[0] = '0;
//         has_map[0]    = 1;
//         for (int i0 = 0; i0 < SIZE; i0++) exp_maps[0][i0] = DWIDTH'(i0);

//         // Case 1:  144-bit control word + expected mapping
//         ctrl_cases[1] = 144'b111000110101110001100100110011100111001110000000111100000001101100101011001100000000000000000000001000011001000001110110011110001011111001001100;
//         has_map[1] = 1;
//         exp_maps[1]   = '{
//             16'd27, 16'd24, 16'd2,  16'd29, 16'd4,  16'd7,  16'd20, 16'd10,
//             16'd1,  16'd0,  16'd8,  16'd9,  16'd3,  16'd13, 16'd16, 16'd26,
//             16'd12, 16'd31, 16'd17, 16'd19, 16'd28, 16'd18, 16'd23, 16'd30,
//             16'd5,  16'd15, 16'd6,  16'd21, 16'd11, 16'd25, 16'd22, 16'd14
//         };

//         $display("\n[SCENARIO 2] Testing %0d control-bit case(s)", NUM_CTRL_CASES);

//         for (int c = 0; c < NUM_CTRL_CASES; c++) begin
//             int out2in[SIZE];

//             control_bit = ctrl_cases[c];
//             $display("[CASE %0d] control_bit = 0x%0h", c, control_bit);

//             if (has_map[c]) begin
//                 for (int j = 0; j < SIZE; j++) begin
//                     int idx = REVERSE_LANES ? (SIZE-1-j) : j;
//                     out2in[j] = exp_maps[c][idx]; 
//                 end
//             end else begin
//                 learn_mapping(out2in);
//             end

//             int mism_lin;
//             check_linear_against_map(out2in, mism_lin);
//             if (mism_lin == 0) $display("[CASE %0d] linear check OK", c);
//             else $display("[CASE %0d] linear mismatches=%0d", c, mism_lin);
//             errors += mism_lin;

//             int retired_case;
//             stream_check_using_map(out2in, VEC_PER_CASE, errors, retired_case);
//             $display("[CASE %0d] stream retired=%0d", c, retired_case);
//         end

//         xif.en = 1'b0;
//         $display("\n[TB][Summary] total errors=%0d, latency=%0d", errors, REAL_LATENCY);
//         $finish;
//     end
// endmodule


// // control bit -> get out2in (call learn_mapping if don't have expected list) -> call check_linear_against_map (if mismatch > 0 
// // => control bit not consistent) -> call stream_check_using_map for stress check 