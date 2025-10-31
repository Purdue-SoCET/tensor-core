module cbg_benes #(
    parameter int SIZE = 32,
    localparam int TAGWIDTH = $clog2(SIZE),
    localparam int STAGES = (2 * TAGWIDTH) - 1, 
    localparam int BITWIDTH = STAGES * (SIZE >> 1)
) (
    input logic [TAGWIDTH-1:0] perm [SIZE-1:0],
    output logic [BITWIDTH-1:0] ctrl
);
    // SIGNALS FOR N=32 

    logic [TAGWIDTH-1:0] range32  [SIZE-1:0];
    logic [TAGWIDTH-1:0] p     [TAGWIDTH-1:0] [SIZE-1:0];
    logic [TAGWIDTH-1:0] q     [TAGWIDTH-1:0] [SIZE-1:0];
    logic [TAGWIDTH-1:0] piinv [TAGWIDTH-1:0] [SIZE-1:0];

    logic [TAGWIDTH-1:0] r [TAGWIDTH-1:0] [SIZE-1:0];
    logic [TAGWIDTH-1:0] s [TAGWIDTH-1:0] [SIZE-1:0];
    logic [TAGWIDTH-1:0] c [TAGWIDTH-1:0] [SIZE-1:0];

    logic [TAGWIDTH-1:0] t [TAGWIDTH-1:0] [SIZE-1:0];
    logic [TAGWIDTH-1:0] u [TAGWIDTH-1:0] [SIZE-1:0];

    logic [TAGWIDTH-1:0] v  [TAGWIDTH-1:0] [TAGWIDTH-2-1:0] [SIZE-1:0];
    logic [TAGWIDTH-1:0] cp [TAGWIDTH-1:0] [TAGWIDTH-2-1:0] [SIZE-1:0];
    logic [TAGWIDTH-1:0] w  [TAGWIDTH-1:0] [TAGWIDTH-2-1:0] [SIZE-1:0];
    logic [TAGWIDTH-1:0] d  [TAGWIDTH-1:0] [TAGWIDTH-2-1:0] [SIZE-1:0];

    logic [TAGWIDTH-1:0] f   [TAGWIDTH-1:0] [SIZE/2-1:0];
    logic [TAGWIDTH-1:0] F   [TAGWIDTH-1:0] [SIZE-1:0]  ;
    logic [TAGWIDTH-1:0] fpi [TAGWIDTH-1:0] [SIZE-1:0]  ;

    logic [TAGWIDTH-1:0] l [TAGWIDTH-1:0] [SIZE/2-1:0];
    logic [TAGWIDTH-1:0] L [TAGWIDTH-1:0] [SIZE-1:0]  ;
    logic [TAGWIDTH-1:0] M [TAGWIDTH-1:0] [SIZE-1:0]  ;

    logic [TAGWIDTH-1:0] subM [TAGWIDTH-1:0] [SIZE-1:0];
    logic [TAGWIDTH-1:0] subz [TAGWIDTH-1:0] [SIZE-1:0];

    // logic [TAGWIDTH-1:0] block_perm [TAGWIDTH-1:0] [SIZE-1:0];

    always_comb begin : range32_logic
        for(int i = 0; i < SIZE; i++) begin
            range32[i] = i;
        end
    end

    generate
        genvar i, loop, j, e;
        for(genvar level = 0; level < TAGWIDTH; level++) begin
            localparam int block_size = SIZE >> level;   // size of each block
            localparam int num_blocks = 1 << level;  // number of blocks
            
            logic [TAGWIDTH-1:0] block_perm [SIZE-1:0];
            
            assign block_perm = (level==0) ? perm : subM[level-1];

            for (genvar block = 0; block < num_blocks; block++) begin : blocks
                localparam int offset_lower = block * block_size;
                localparam int offset_upper = offset_lower + block_size - 1;
                
                if(level == TAGWIDTH-1) begin
                    assign f[level][block] = block_perm[offset_lower];
                end
                else begin
                    
                    for(i = 0; i < block_size; i++) begin
                        assign p[level][block*block_size+i] = block_perm[(block*block_size+i) ^ 'b1];
                        assign q[level][block*block_size+i] = block_perm[block*block_size+i] ^ 'b1;
                    end

                    composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_piinv (
                        .pi(range32[block_size-1:0]), 
                        .c(block_perm[offset_upper:offset_lower]),
                        .out(piinv[level][offset_upper:offset_lower])
                    );

                    composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_r (
                        .pi(p[level][offset_upper:offset_lower]), 
                        .c(q[level][offset_upper:offset_lower]), 
                        .out(r[level][offset_upper:offset_lower])
                    );

                    composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_s (
                        .pi(q[level][offset_upper:offset_lower]), 
                        .c(p[level][offset_upper:offset_lower]), 
                        .out(s[level][offset_upper:offset_lower])
                    );

                    find_min #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) min_c(
                        .in({range32[block_size-1:0], r[level][offset_upper:offset_lower]}),
                        .out(c[level][offset_upper:offset_lower])
                    );

                    composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_t (
                        .pi(r[level][offset_upper:offset_lower]), 
                        .c(s[level][offset_upper:offset_lower]), 
                        .out(t[level][offset_upper:offset_lower])
                    );
                    composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_u (
                        .pi(s[level][offset_upper:offset_lower]), 
                        .c(r[level][offset_upper:offset_lower]), 
                        .out(u[level][offset_upper:offset_lower])
                    );
                    
                    // for loop
                    for(loop = 0; loop < TAGWIDTH-2; loop++) begin
                        if(loop == 0) begin
                            composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_cp (
                                .pi(c[level][offset_upper:offset_lower]), 
                                .c(u[level][offset_upper:offset_lower]), 
                                .out(cp[level][loop][offset_upper:offset_lower])
                            );
                            composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_v (
                                .pi(t[level][offset_upper:offset_lower]), 
                                .c(u[level][offset_upper:offset_lower]), 
                                .out(v[level][loop][offset_upper:offset_lower])
                            );
                            composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_w (
                                .pi(u[level][offset_upper:offset_lower]), 
                                .c(t[level][offset_upper:offset_lower]), 
                                .out(w[level][loop][offset_upper:offset_lower])
                            );

                            find_min #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) min_d (
                                .in({c[level][offset_upper:offset_lower], cp[level][loop][offset_upper:offset_lower]}),
                                .out(d[level][loop][offset_upper:offset_lower])
                            );
                        end
                        else begin
                            composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_cp (
                                .pi(d[level][loop-1][offset_upper:offset_lower]), 
                                .c(w[level][loop-1][offset_upper:offset_lower]), 
                                .out(cp[level][loop][offset_upper:offset_lower])
                            );
                            composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_v (
                                .pi(v[level][loop-1][offset_upper:offset_lower]), 
                                .c(w[level][loop-1][offset_upper:offset_lower]), 
                                .out(v[level][loop][offset_upper:offset_lower])
                            );
                            composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_w (
                                .pi(w[level][loop-1][offset_upper:offset_lower]), 
                                .c(v[level][loop-1][offset_upper:offset_lower]), 
                                .out(w[level][loop][offset_upper:offset_lower])
                            );

                            find_min #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) min_d (
                                .in({d[level][loop-1][offset_upper:offset_lower], cp[level][loop][offset_upper:offset_lower]}),
                                .out(d[level][loop][offset_upper:offset_lower])
                            );
                        end
                    end

                    for(i = 0; i < block_size; i++) begin
                        if(i < block_size/2) begin
                            assign f[level][block_size/2*block+i] = d[level][TAGWIDTH-2-1][block_size*block+2*i] % 2;
                        end
                        
                        assign F[level][block_size*block+i] = i ^ f[level][block_size/2*block + (i/2)];
                    end

                    composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_fpi (
                        .pi(F[level][offset_upper:offset_lower]), 
                        .c(piinv[level][offset_upper:offset_lower]), 
                        .out(fpi[level][offset_upper:offset_lower])
                    );

                    for(i = 0; i < block_size; i++) begin
                        if(i < block_size/2) begin
                            assign l[level][block_size/2*block+i] = (fpi[level][block_size*block + (2*i)]) % 2;
                        end
                        assign L[level][block_size*block+i] = i ^ l[level][block_size/2*block + (i/2)];
                    end

                    composeinv #(.SIZE(block_size), .TAGWIDTH(TAGWIDTH)) cinv_M (
                        .pi(fpi[level][offset_upper:offset_lower]), 
                        .c(L[level][offset_upper:offset_lower]), 
                        .out(M[level][offset_upper:offset_lower])
                    );
                    for(e = 0; e < 2; e++) begin
                        for(j = 0; j < block_size/2; j++) begin
                            assign subM[level][j+block_size*block+block_size/2*e] = M[level][2*j+e+block_size*block]/2;
                        end
                        // subM = [[M[2*j+e]//2 for j in range(n//2)] for e in range(2)]
                    end
                end
            end
        end
    endgenerate

    logic [8-1:0] first, last;
    int block_size_sub;
    int num_blocks_sub;

    int offset_first;
    int offset_last;

    always_comb begin
        first = 0;
        last = BITWIDTH-1;

        for(int level = 0; level < TAGWIDTH; level++) begin
            block_size_sub = SIZE >> level;   // size of each block
            num_blocks_sub = 1 << level;  // number of blocks

            if(level == TAGWIDTH-1) begin
                ctrl[first] = f[TAGWIDTH-1][first];
                first = first + 1;
            end
            else begin
                for(int sub_idx = 0; sub_idx < block_size_sub/2; sub_idx++) begin
                    for(int block = 0; block < num_blocks_sub; block++) begin
                        offset_first = (block * block_size_sub/2) + sub_idx;
                        offset_last = (SIZE/2 - 1) - offset_first;

                        ctrl[first] = f[level][offset_first];
                        ctrl[last] = l[level][offset_last];

                        first = first + 1;
                        last = last - 1;
                    end
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