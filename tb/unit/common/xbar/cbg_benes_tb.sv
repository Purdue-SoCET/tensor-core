// module cbg_benes_tb;
//     localparam int PERIOD = 10;
//     localparam int SIZE=32;
//     localparam int DWIDTH=16;
//     localparam int TAGWIDTH=$clog2(SIZE);
//     localparam int STAGES = (2 * TAGWIDTH) - 1;
//     localparam int BITWIDTH = STAGES * (SIZE >> 1);

//     logic clk, n_rst;
//     logic [BITWIDTH-1:0] ctrl;
//     logic [TAGWIDTH-1:0] perm [SIZE-1:0];
//     logic [BITWIDTH-1:0] exp_ctrl;

//     always #(PERIOD/2) clk = ~clk;
//     cbg_benes #(.SIZE(SIZE)) DUT (.perm(perm), .ctrl(ctrl));


//     initial begin
//         perm = {5'd14, 5'd22, 5'd25, 5'd11, 5'd21, 5'd6, 5'd15, 5'd5, 5'd30, 5'd23, 5'd18, 5'd28, 5'd19, 5'd17, 5'd31, 5'd12, 5'd26, 5'd16, 5'd13, 5'd3, 5'd9, 5'd8, 5'd0, 5'd1, 5'd10, 5'd20, 5'd7, 5'd4, 5'd29, 5'd2, 5'd24, 5'd27};
//         // perm = {5'd27, 5'd5'd24, 5'd2, 5'd29, 5'd4, 5'd7, 5'd20, 5'd10, 5'd1, 5'd0, 5'd8, 5'd9, 5'd3, 5'd13, 5'd16, 5'd26,
//         //                 5'd12, 5'd31, 5'd17, 5'd19, 5'd28, 5'd18, 5'd23, 5'd30, 5'd5, 5'd15, 5'd6, 5'd21, 5'd11, 5'd25, 5'd22, 5'd14};
//         exp_ctrl = 144'b111000110101110001100100110011100111001110000000111100000001101100101011001100000000000000000000001000011001000001110110011110001011111001001100;
        
//         #(PERIOD)
//         #(PERIOD)
//         for (int i = 0; i < BITWIDTH; i++) begin
//             if(exp_ctrl[i] != ctrl[i]) begin
//                 $display("WRONG bit %d not equal. Expected: %d, output: %d", i, exp_ctrl[i], ctrl[i]);
//             end
//             else begin
//                 $display("CHECK bit %d was equal. Expected: %d, output: %d", i, exp_ctrl[i], ctrl[i]);
//             end
//         end
//         $finish();
//     end

    
// endmodule











module cbg_benes_tb;
    localparam int PERIOD = 10;
    localparam int SIZE = 32;
    localparam int DWIDTH = 16;
    localparam int TAGWIDTH = $clog2(SIZE);
    localparam int STAGES = (2 * TAGWIDTH) - 1;
    localparam int BITWIDTH = STAGES * (SIZE >> 1);

    logic clk, n_rst;
    logic [BITWIDTH-1:0] ctrl;
    logic [TAGWIDTH-1:0] perm [SIZE-1:0];
    logic [BITWIDTH-1:0] exp_ctrl;

    always #(PERIOD/2) clk = ~clk;
    cbg_benes #(.SIZE(SIZE)) DUT (.perm(perm), .ctrl(ctrl));

    // build inverse permuatation 
    function automatic void invert_int_array(
        input int pi[], input int n,
        output int inv[]
    );
        inv = new[n];
        for (int i = 0; i < n; i++) inv[pi[i]] = i;
    endfunction

    // translate array accross coordinate systems 
    function automatic void composeinv_int(
        input int c[], input int pi[], input int n,
        output int d[]
    );
        int inv[];
        invert_int_array(pi, n, inv);
        d = new[n];
        for (int k = 0; k < n; k++) d[k] = c[inv[k]];
    endfunction

    // convert permuation p[SIZE] itno a plain 
    function automatic void logic_perm_to_int(
        input logic [TAGWIDTH-1:0] p [SIZE],
        output int pi[]
    );
        pi = new[SIZE];
        for (int i = 0; i < SIZE; i++) pi[i] = p[i];
    endfunction

    // recursive computes the control bit for benes network that realizes permuation pi_in, and appends the bits to qb =. this is for checker 
    function automatic void controlbits_rec(
        input int n,
        input int pi_in[], // permutation length n
        inout bit qb[$] // output bit queue, appended
    );
        int m = 0;
        while ((1<<m) < n) m++;

        if (m == 1) begin
            qb.push_back( pi_in[0] & 1 );
            return;
        end

        int pi[], p[], q[];
        pi = new[n];
        p = new[n];
        q = new[n];
        for (int x = 0; x < n; x++) begin
            pi[x] = pi_in[x];
            p[x] = pi[x ^ 1];
            q[x] = pi[x] ^ 1;
        end

        int p1[], q1[];
        composeinv_int(p, q, n, p1);
        composeinv_int(q, p, n, q1);
        p = p1; 
        q = q1;

        int c[];
        c = new[n];
        for (int x = 0; x < n; x++) begin 
            c[x] = (x < p[x]) ? x : p[x];
        end

        composeinv_int(p, q, n, p1);
        composeinv_int(q, p, n, q1);
        p = p1; q = q1;

        for (int ii = 1; ii < m-1; ii++) begin
            int cp[];
            composeinv_int(c, q, n, cp);
            composeinv_int(p, q, n, p1);
            composeinv_int(q, p, n, q1);
            for (int x = 0; x < n; x++) c[x] = (c[x] < cp[x]) ? c[x] : cp[x];
            p = p1; q = q1;
        end

        bit f_bits[$];
        for (int j = 0; j < n/2; j++) begin
            bit fb = c[2*j] & 1;
            f_bits.push_back(fb);
            qb.push_back(fb);  
        end

        int F[];
        F = new[n];
        for (int x = 0; x < n; x++) F[x] = x ^ f_bits[x/2];

        int piinv[], Fpi[];
        invert_int_array(pi, n, piinv);
        composeinv_int(F, piinv, n, Fpi);

        bit l_bits[$];
        for (int k = 0; k < n/2; k++) begin
            l_bits.push_back( Fpi[2*k] & 1 );
        end

        int L[];
        L = new[n];
        for (int y = 0; y < n; y++) L[y] = y ^ l_bits[y/2];

        int M[];
        composeinv_int(Fpi, L, n, M);

        int sub0[], sub1[];
        sub0 = new[n/2];
        sub1 = new[n/2];
        for (int j = 0; j < n/2; j++) begin
            sub0[j] = M[2*j + 0] >> 1;  
            sub1[j] = M[2*j + 1] >> 1;
        end

        bit z0[$], z1[$];
        controlbits_rec(n/2, sub0, z0);
        controlbits_rec(n/2, sub1, z1);

        int mid_len = z0.size(); // equals ((2*(m-1)-1) * (n/4))
        for (int t = 0; t < mid_len; t++) begin
            qb.push_back(z0[t]);
            qb.push_back(z1[t]);
        end
        foreach (l_bits[t]) qb.push_back(l_bits[t]);
    endfunction

    // convert perm to int[], call controlbit_rec, and pack the bit queue 
    function automatic logic [BITWIDTH-1:0] controlbits_ref(input logic [TAGWIDTH-1:0] p [SIZE]);
        bit qb[$];
        int pi[];
        logic_perm_to_int(p, pi);
        controlbits_rec(SIZE, pi, qb);

        logic [BITWIDTH-1:0] out = '0;
        for (int i = 0; i < BITWIDTH; i++) begin 
            out[i] = (i < qb.size()) ? qb[i] : 1'b0;
        end
        return out;
    endfunction

    // Counts how many control bits differ between two vectors
    function automatic int compare_ctrl_bits(input logic [BITWIDTH-1:0] a, input logic [BITWIDTH-1:0] b);
        int errs = 0;
        for (int i = 0; i < BITWIDTH; i++) if (a[i] !== b[i]) errs++;
        return errs;
    endfunction

    // Builds the identity permutation
    task automatic make_identity(output logic [TAGWIDTH-1:0] p [SIZE]);
        for (int i = 0; i < SIZE; i++) p[i] = i[TAGWIDTH-1:0];
    endtask

    // Builds the reverse permutation
    task automatic make_reverse(output logic [TAGWIDTH-1:0] p [SIZE]);
        for (int i = 0; i < SIZE; i++) p[i] = (SIZE-1-i)[TAGWIDTH-1:0];
    endtask

    // Generates a uniform random permutation of SIZE−1 then writes it into perm
    task automatic make_random(output logic [TAGWIDTH-1:0] p [SIZE]);
        int a[SIZE];
        for (int i = 0; i < SIZE; i++) begin 
             a[i] = i;
        end
        for (int i = SIZE-1; i > 0; i--) begin
            int j = $urandom_range(0, i);
            int t = a[i]; a[i] = a[j]; a[j] = t;
        end
        for (int i = 0; i < SIZE; i++) begin 
            p[i] = a[i][TAGWIDTH-1:0];
        end
    endtask

    initial begin : main
        int total_errs = 0;

        clk = 1'b0;
        n_rst = 1'b1;

        make_identity(perm);
        #(PERIOD);
        exp_ctrl = controlbits_ref(perm);
        total_errs += compare_ctrl_bits(ctrl, exp_ctrl);
        $display("Case 0 (identity): %s", (compare_ctrl_bits(ctrl, exp_ctrl)==0) ? "PASS" : "FAIL");

        // Case 1: reverse
        make_reverse(perm);
        #(PERIOD);
        exp_ctrl = controlbits_ref(perm);
        total_errs += compare_ctrl_bits(ctrl, exp_ctrl);
        $display("Case 1 (reverse): %s", (compare_ctrl_bits(ctrl, exp_ctrl)==0) ? "PASS" : "FAIL");

        // current test case
        perm = '{
            5'd14, 5'd22, 5'd25, 5'd11, 5'd21, 5'd6,  5'd15, 5'd5,
            5'd30, 5'd23, 5'd18, 5'd28, 5'd19, 5'd17, 5'd31, 5'd12,
            5'd26, 5'd16, 5'd13, 5'd3,  5'd9,  5'd8,  5'd0,  5'd1,
            5'd10, 5'd20, 5'd7,  5'd4,  5'd29, 5'd2,  5'd24, 5'd27
        };
        #(PERIOD);
        
        exp_ctrl = controlbits_ref(perm);
        total_errs += compare_ctrl_bits(ctrl, exp_ctrl);
        $display("Case 2 (provided perm): %s", (compare_ctrl_bits(ctrl, exp_ctrl)==0) ? "PASS" : "FAIL");

        // Random cases
        int NUM_RANDOM = 10;
        for (int t = 0; t < NUM_RANDOM; t++) begin
            make_random(perm);
            #(PERIOD);
            exp_ctrl = controlbits_ref(perm);
            int errs = compare_ctrl_bits(ctrl, exp_ctrl);
            total_errs += errs;
            $display("Case R%0d (random): %s%s", t, (errs==0) ? "PASS" : "FAIL", (errs==0) ? "" : $sformatf(" mismatches=%0d", errs));
        end

        $display("\nSUMMARY: %s", (total_errs==0) ? "ALL PASS" : $sformatf("TOTAL ERRORS = %0d", total_errs));
        $finish;
    end
endmodule
