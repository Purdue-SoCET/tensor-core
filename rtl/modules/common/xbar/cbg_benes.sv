module cbg_benes #(
    parameter int SIZE = 32,
    parameter int DWIDTH = 16,
    localparam int TAGWIDTH = $clog2(SIZE),
    localparam int STAGES = (2 * TAGWIDTH) - 1, 
    localparam int BITWIDTH = STAGES * (SIZE >> 1)
) (
    logic xif
    input logic [TAGWIDTH-1:0] perm [SIZE],
    output logic [BITWIDTH-1:0] ctrl
)   
    // SIGNALS FOR N=32 
    logic [TAGWIDTH-1:0] block_perm [SIZE];

    logic [TAGWIDTH-1:0] range32  [SIZE];
    logic [TAGWIDTH-1:0] p      [TAGWIDTH] [SIZE];
    logic [TAGWIDTH-1:0] q      [TAGWIDTH] [SIZE];
    logic [TAGWIDTH-1:0] piinv  [TAGWIDTH] [SIZE];

    logic [TAGWIDTH-1:0] r [TAGWIDTH] [SIZE];
    logic [TAGWIDTH-1:0] s [TAGWIDTH] [SIZE];
    logic [TAGWIDTH-1:0] c [TAGWIDTH] [SIZE];

    logic [TAGWIDTH-1:0] t [TAGWIDTH] [SIZE];
    logic [TAGWIDTH-1:0] u [TAGWIDTH] [SIZE];

    logic [TAGWIDTH-1:0] v  [TAGWIDTH]    [TAGWIDTH] [TAGWIDTH-2] [SIZE];
    logic [TAGWIDTH-1:0] cp [TAGWIDTH]    [TAGWIDTH] [TAGWIDTH-2] [SIZE];
    logic [TAGWIDTH-1:0] w  [TAGWIDTH]    [TAGWIDTH] [TAGWIDTH-2] [SIZE];
    logic [TAGWIDTH-1:0] d  [TAGWIDTH]    [TAGWIDTH] [TAGWIDTH-2] [SIZE];

    logic [TAGWIDTH-1:0] f   [TAGWIDTH] [SIZE/2];
    logic [TAGWIDTH-1:0] F   [TAGWIDTH] [SIZE];
    logic [TAGWIDTH-1:0] fpi [TAGWIDTH] [SIZE];

    logic [TAGWIDTH-1:0] l [TAGWIDTH] [SIZE/2];
    logic [TAGWIDTH-1:0] L [TAGWIDTH] [SIZE];
    logic [TAGWIDTH-1:0] M [TAGWIDTH] [SIZE];

    logic [TAGWIDTH-1:0] subM [TAGWIDTH] [SIZE/2][2];
    logic [TAGWIDTH-1:0] subz [TAGWIDTH] [SIZE];

    always_comb begin : range32_logic
        for(int i = 0; i < SIZE; i++) begin
            range32[i] = i;
        end
    end

    generate
        genvar i, level, block;
        for(level = 0; level < TAGWIDTH; level++) begin
            localparam int block_size = N >> level;   // size of each block
            localparam int num_blocks = 1 << level;  // number of blocks
            if (level == 0) begin
                block_perm = perm;
            end
            else begin
                for(int i = 0; i < num_blocks; i++) begin
                    block_perm = subM[level-1];
                end
            end

            for (block = 0; block < num_blocks; block++) begin : blocks
                localparam int offset_lower = block*block_size;
                localparam int offset_upper = offset_lower+block_size-1;
                
                for(i = 0; i < SIZE; i++) begin
                    p[level][i] = perm[level][i ^ 'b1];
                    q[level][i] = perm[level][i] ^ 'b1;
                end

                composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_piinv (
                    .pi(range32[block_size-1:0]), 
                    .c(block_perm[level][offset_upper:offest_lower]),
                    .out(piinv[level][offset_upper:offest_lower])
                );

                composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_r (
                    .pi(p[level][offset_upper:offest_lower]), 
                    .c(q[level][offset_upper:offest_lower]), 
                    .out(r[level][offset_upper:offest_lower])
                );

                composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_s (
                    .pi(q[level][offset_upper:offest_lower]), 
                    .cp(p[level][offset_upper:offest_lower]), 
                    .out(s[level][offset_upper:offest_lower])
                );

                find_min min_c(
                    .in({range32[block_size-1:0], r[level][offset_upper:offest_lower]}),
                    .out(c[level][offset_upper:offest_lower])
                )

                composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_t (
                    .pi(r[level][offset_upper:offest_lower]), 
                    .c(s[level][offset_upper:offest_lower]), 
                    .out(t[level][offset_upper:offest_lower])
                );
                composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_u (
                    .pi(s[level][offset_upper:offest_lower]), 
                    .c(r[level][offset_upper:offest_lower]), 
                    .out(u[level][offset_upper:offest_lower])
                );
                
                // for loop
                while(int i = 0; i < TAGWIDTH-2; i++) begin
                    if(i == 0) begin
                        composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_cp (
                            .pi(c[level][offset_upper:offest_lower]), 
                            .c(u[level][offset_upper:offest_lower]), 
                            .out(cp[level][i][offset_upper:offest_lower])
                        );
                        composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_v (
                            .pi(t[level][offset_upper:offest_lower]), 
                            .c(u[level][offset_upper:offest_lower]), 
                            .out(v[level][i][offset_upper:offest_lower])
                        );
                        composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_w (
                            .pi(u[level][offset_upper:offest_lower]), 
                            .c(t[level][offset_upper:offest_lower]), 
                            .out(w[level][i][offset_upper:offest_lower])
                        );

                        find_min min_d (
                            .in({c[level][offset_upper:offest_lower], cp[level][i][offset_upper:offest_lower]})
                            .out(d[level][i][offset_upper:offest_lower])
                        )
                    end
                    else begin
                        composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_cp (
                            .pi(d[level][i-1][offset_upper:offest_lower]), 
                            .c(w[level][i-1][offset_upper:offest_lower]), 
                            .out(cp[level][i][offset_upper:offest_lower])
                        );
                        composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_v (
                            .pi(v[level][i-1][offset_upper:offest_lower]), 
                            .c(w[level][i-1][offset_upper:offest_lower]), 
                            .out(v[level][i][offset_upper:offest_lower])
                        );
                        composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_w (
                            .pi(w[level][i-1][offset_upper:offest_lower]), 
                            .c(v[level][i-1][offset_upper:offest_lower]), 
                            .out(w[level][i][offset_upper:offest_lower])
                        );

                        find_min min_d (
                            .in({d[level][i-1][offset_upper:offest_lower], cp[level][i][offset_upper:offest_lower]})
                            .out(d[level][i][offset_upper:offest_lower])
                        )
                    end
                end

                for(i = 0; i < SIZE; i++) begin
                    if(i < SIZE/2) begin
                        f[i] = d_2[2*i] % 2;
                    end
                    
                    F[i] = i ^ f[i / 2];

                    if(i < SIZE/2) begin
                        l[i] = fpi[2*i] % 2;
                    end
                    L[i] = i ^ l[i / 2];
                    M[perm[L[i]]] = i;
                end

                composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_fpi (
                    .pi(F), 
                    .c(piinv), 
                    .out(fpi)
                );

                composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_M (
                    .pi(fpi), 
                    .c(L), 
                    .out(M)
                );

                for(i = 0; i < 2; i++) begin
                    for(int j = 0; j < SIZE/2; j++) begin
                        subM[i][j] = M[2*j+i]/2;
                    end
                end
            end
        end
    endgenerate

    logic [BITWIDTH-1:0] first, last;
    always_comb begin
        first = 0;
        last = BITWIDTH-1;
        for(int level = 0; level < TAGWIDTH; level++) begin
            localparam int block_size = N >> level;   // size of each block
            localparam int num_blocks = 1 << level;  // number of blocks

            for(int sub_idx = 0; sub_idx < block_size; sub_idx++) begin
                for(int block = 0; block < num_blocks; block++) begin
                    localparam int offset_first = (block * block_size) + sub_idx;
                    localparam int offset_last = (SIZE - 1) - offset_first;

                    ctrl[first] = f[level][offset_first];
                    ctrl[last] = l[level][offset_last];

                    first++;
                    last--;
                end
            end
            
        end


    end
endmodule

// ========================================
// REFERENCE CODE
// ========================================

// def controlbits(pi):
//     n = len(pi)
//     m = 1

//     while 1<<m < n: m += 1

//     if m == 1: return [pi[0]]

//     p = [pi[x^1] for x in range(n)]
//     q = [pi[x]^1 for x in range(n)]
//     piinv = composeinv(range(n),pi)

//     r,s = composeinv(p,q),composeinv(q,p)
//     c = [min(x,r[x]) for x in range(n)]
//     t,u = composeinv(r,s),composeinv(s,r)

//     for i in range(1,m-1): (3 times for N=32)
//         cp = composeinv(c,u) (d,w) from 2nd iteration
//         v = composeinv(t,u)  (v,w) from 2nd iteration
//         w = composeinv(u,t)  (W,v) from 2nd iteration
//         d = [min(c[x],cp[x]) for x in range(n)]  (d,cp) from 2nd iteration

//     f = [d[2*j]%2 for j in range(n//2)]
//     F = [x^f[x//2] for x in range(n)]
//     Fpi = composeinv(F,piinv)

//     l = [Fpi[2*k]%2 for k in range(n//2)]
//     L = [y^l[y//2] for y in range(n)]
//     M = composeinv(Fpi,L)

//     subM = [[M[2*j+e]//2 for j in range(n//2)] for e in range(2)]
//     subz = map(controlbits,subM)

//     z = [s for s0s1 in zip(*subz) for s in s0s1]

//     return f+z+l