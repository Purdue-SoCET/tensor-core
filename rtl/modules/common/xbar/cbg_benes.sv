module cbg_benes #(
    parameter int SIZE=32;
    parameter int DWIDTH = 16,
    localparam int TAGWIDTH = $clog2(SIZE),
    localparam int STAGES = (2 * TAGWIDTH) - 1, 
    localparam int BITWIDTH = STAGES * (SIZE >> 1)
) (
    input logic [TAGWIDTH-1:0] perm [SIZE-1:0],
    output logic [BITWIDTH-1:0] ctrl
)   
    // SIGNALS FOR N=32 
    logic [TAGWIDTH-1:0] p32 [SIZE-1:0];
    logic [TAGWIDTH-1:0] q32 [SIZE-1:0];
    logic [TAGWIDTH-1:0] piinv32 [SIZE-1:0];
    logic [TAGWIDTH-1:0] r32 [SIZE-1:0];
    logic [TAGWIDTH-1:0] s32 [SIZE-1:0];
    logic [TAGWIDTH-1:0] c32 [SIZE-1:0];

    generate
        genvar i;

        for(i = 0; i < SIZE; i++) begin
            p32[i] = perm[i ^ 1'b1];
            q32[i] = perm[i] ^ 1'b1;
            piinv32[perm[i]] = i;
            r32[perm[i]] = i;
            s32[perm[i]] = i;
            c32[i] = r32[i] < i ? r32[i] : i;
        end
        
    endgenerate
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
//         cp = composeinv(c,u)
//         v = composeinv(t,u)
//         w = composeinv(u,t)
//         c = [min(c[x],cp[x]) for x in range(n)]

//     f = [c[2*j]%2 for j in range(n//2)]
//     F = [x^f[x//2] for x in range(n)]
//     Fpi = composeinv(F,piinv)

//     l = [Fpi[2*k]%2 for k in range(n//2)]
//     L = [y^l[y//2] for y in range(n)]
//     M = composeinv(Fpi,L)

//     subM = [[M[2*j+e]//2 for j in range(n//2)] for e in range(2)]
//     subz = map(controlbits,subM)

//     z = [s for s0s1 in zip(*subz) for s in s0s1]

//     return f+z+l