`include "vector_types.vh"
`include "vector_if.vh"
`include "vexp_if.vh"

module vexp (
    input logic CLK,
    input logic nRST,
    vexp_if.vexp vexpif
);

import vector_pkg::*;

vaddsub_if vaddsubif1(); //vector add/sub instantiation 1
vaddsub_if vaddsubif2(); //vector add/sub instatiation 2
vaddsub_if vaddsubif3(); //vector add/sub instatiation 3


vaddsub VADDSUB1 ( //connecting the module's appropriate signals
    .CLK(CLK),
    .nRST(nRST),
    .vaddsub(vaddsubif1)
);

vaddsub VADDSUB2 (
    .CLK(CLK),
    .nRST(nRST),
    .vaddsub(vaddsubif2)
);

vaddsub VADDSUB23 (
    .CLK(CLK),
    .nRST(nRST),
    .vaddsub(vaddsubif3)
);

fp16_t fp1; //declaring the fp16 type
logic [15:0] r2_init, r2_fin, r3_init, r3_fin, result1, result2;
logic [15:0] /*par_shift1, par_shift2, par_shift3, par_shift4, par_shift5,*/ onesixth, t_series_approx; //partial shifts for approximating dividing by 6 without a divider
logic [11:0] exp_val;
logic [4:0] exp; //5 bits for the exponent field

assign fp1 = vexpif.port_a;
assign exp = fp1.exp;

always_comb begin
    
    if (vexpif.enable == 1) begin
        onesixth = 16'b0011000101010101; //1/6 in fp16 format
        
        // vexpif.neg = fp1.sign ? 1 : 0; //setting the negative flag if the input is negative

    //Using Shifting to Get Power of Two Value
    assign exp_val = (12'b1 << (exp - 15)); //2^q value from exponent field

    //Calculate Taylor Series Approximation for e^r

    //Step 1: Calculate r^2 term
    // fp16 multiplier needed
        r2_init = fp1.mantissa * fp1.mantissa;
        r2_fin = r2_init >> 1; //divide by 2
        r2_fin[14:10] = r2_fin[14:10] + 1; //++ the exponent field to account for shift

    //Step 2: Calculate r^3 term
        
        r3_init = r2_fin * fp1.mantissa; //plug in the multiplier
        
        // //first solution: approximate dividing by 6 with shifts
        // par_shift1 = r3_init >> 3;
        // par_shift2 = r3_init >> 5;
        // par_shift3 = r3_init >> 7;
        // par_shift4 = r3_init >> 9;
        // par_shift5 = r3_init >> 11;

        // shift_sum = part_shift1 + par_shift2 + par_shift3 + par_shift4 + par_shift5; //using adder

        //second solution: use multiplier to multiply by 1/6
        
        r3_fin = r3_init * onesixth; //using multiplier to multiply by 1/6

        //first adder performs r^3 / 6 + r^2
        vaddsubif1.port_a = r3_fin;
        vaddsubif1.port_b = r2_fin;
        result1 = vaddsubif1.out;

        //second adder performs r + (r^3 / 6 + r^2)
        vaddsubif2.port_a = vexpif.port_a;
        vaddsubif2.port_b = result1;
        result2 = vaddsubif2.out;

        //third adder performs 1 + (r + r^2 + r^3 / 6)
        vaddsubif3.port_a = 16'b0011110000000000;
        vaddusbif3.port_b = result2;
        t_series_approx = vaddsubif3.out;

    //Step 3: Multiply 2^q and e^r
        vexpif.out = t_series_approx * exp_val;
    end

end


endmodule