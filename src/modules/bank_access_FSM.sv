`include "sp_types_pkg.vh"
`include "bank_access_FSM_if.vh"
import sp_types_pkg::*;

module bank_access_FSM #(
    parameter BANK_NUM = 0 
)(
    input logic CLK, nRST,
    bank_access_FSM_if.sp spif
);

    typedef enum logic[4:0] { 
        DECODE, LOAD0, LOAD1, LOAD2, LOAD3, STORE0, STORE1, STORE2, STORE3, I_GEMM0, I_GEMM1, 
        I_GEMM2, I_GEMM3, W_GEMM0, W_GEMM1, W_GEMM2, W_GEMM3, PS_GEMM0, 
        PS_GEMM1, PS_GEMM2, PS_GEMM3, PSUMLOAD
    } state_t;

    state_t state, n_state, p_state;

    logic [WORD_W-1:0] ls_addr, n_ls_addr;
    logic [MAT_S_W-1:0] ls_mat, n_ls_mat;
    logic [MAT_S_W+2-1:0] in, weight, partial_sum, ls;

    assign in = spif.instrFIFO_rdata.ls_addr_gemm_gemm_sel[17:12];
    assign weight = spif.instrFIFO_rdata.ls_addr_gemm_gemm_sel[11:6];
    assign partial_sum = spif.instrFIFO_rdata.ls_addr_gemm_gemm_sel[5:0];
    assign ls = spif.instrFIFO_rdata.ls_matrix_rd_gemm_new_weight;

    always_ff @(posedge CLK, negedge nRST) begin
        if (nRST == 1'b0) begin
            state <= DECODE;
            p_state <= DECODE;
            ls_addr <= '0;
            ls_mat <= '0;
        end
        else begin
            state <= n_state;
            p_state <= state;
            ls_addr <= n_ls_addr;
            ls_mat <= n_ls_mat;
        end
    end

    always_comb begin
        n_state = state;
        spif.instrFIFO_REN = 1'b0;
        n_ls_addr = ls_addr;
        n_ls_mat = ls_mat;
        case (state)
            DECODE: begin
                if(spif.psumoutFIFO_full && (spif.gemm_mat[5:4] == BANK_NUM)) begin
                    n_state = PSUMLOAD;
                end
                else if (~spif.instrFIFO_empty) begin
                    spif.instrFIFO_REN = 1'b1;
                    if ((spif.new_instr) || (p_state == PSUMLOAD) || (p_state == LOAD3) || (p_state == STORE3)) begin
                        case (spif.instrFIFO_rdata.opcode)
                        2'b01: begin
                            spif.instrFIFO_REN = 1'b1;
                            if (ls[5:4] == BANK_NUM) begin
                                n_ls_mat = ls[MAT_S_W-1:0];
                                n_ls_addr = spif.instrFIFO_rdata.ls_addr_gemm_gemm_sel;
                                n_state = LOAD0;
                            end
                        end
                        2'b10: begin
                            spif.instrFIFO_REN = 1'b1;
                            if (ls[5:4] == BANK_NUM) begin
                                n_ls_mat = ls[MAT_S_W-1:0];
                                n_ls_addr = spif.instrFIFO_rdata.ls_addr_gemm_gemm_sel;
                                n_state = STORE0;
                            end
                        end
                        2'b11: begin
                            if (spif.instrFIFO_rdata.ls_matrix_rd_gemm_new_weight[5] && (weight[5:4] == BANK_NUM)) begin
                                n_state = W_GEMM0;
                                spif.instrFIFO_REN = 1'b0;
                            end
                            else if (in[5:4] == BANK_NUM) begin
                                n_state = I_GEMM0;
                                spif.instrFIFO_REN = 1'b0;
                            end
                            else if (partial_sum[5:4] == BANK_NUM) begin
                                n_state = PS_GEMM0;
                                spif.instrFIFO_REN = 1'b0;
                            end
                            else begin
                                spif.instrFIFO_REN = 1'b1;
                            end
                        end
                        endcase
                    end
                end
            end
            PSUMLOAD: begin
                if (spif.psumoutFIFO_rdata.row_s == 2'd3) n_state = DECODE;
            end
            LOAD0: begin
                if (spif.sLoad_hit) n_state = LOAD1;
            end
            LOAD1: begin
                if (spif.sLoad_hit) n_state = LOAD2;
            end
            LOAD2: begin
                if (spif.sLoad_hit) n_state = LOAD3;
            end
            LOAD3: begin
                if (spif.sLoad_hit) n_state = DECODE;
            end
            STORE0: n_state = STORE1;
            STORE1: n_state = STORE2;
            STORE2: n_state = STORE3;
            STORE3: n_state = DECODE;
            W_GEMM0: n_state = W_GEMM1;
            W_GEMM1: n_state = W_GEMM2;
            W_GEMM2: n_state = W_GEMM3;
            W_GEMM3: begin
                if (in[5:4] == BANK_NUM) begin
                    n_state = I_GEMM0;
                end
                else if (partial_sum[5:4] == BANK_NUM) begin
                    n_state = PS_GEMM0;
                end
                else begin
                    n_state = DECODE;
                end
            end
            I_GEMM0: n_state = I_GEMM1;
            I_GEMM1: n_state = I_GEMM2;
            I_GEMM2: n_state = I_GEMM3;
            I_GEMM3: begin
                if (partial_sum[5:4] == BANK_NUM) begin
                    n_state = PS_GEMM0;
                end
                else begin
                    n_state = DECODE;
                end
            end
            PS_GEMM0: n_state = PS_GEMM1;
            PS_GEMM1: n_state = PS_GEMM2;
            PS_GEMM2: n_state = PS_GEMM3;
            PS_GEMM3: begin
                n_state = DECODE;
            end
        endcase
    end

    always_comb begin
        spif.sLoad = 1'b0;
        spif.wFIFO_WEN = 1'b0;
        spif.wFIFO_wdata = '0;
        spif.psumoutFIFO_REN = 1'b0;
        spif.load_addr = '0;
        spif.rFIFO_WEN = 1'b0;
        spif.rFIFO_wdata = '0;
        case (state)
            PSUMLOAD: begin
                spif.wFIFO_WEN = 1'b1;
                spif.wFIFO_wdata.gemm_result = 1'b1;
                spif.wFIFO_wdata.mat_s = spif.gemm_mat[MAT_S_W-1:0];
                spif.wFIFO_wdata.row_s = spif.psumoutFIFO_rdata.row_s;
                spif.wFIFO_wdata.data = spif.psumoutFIFO_rdata.data;
                spif.psumoutFIFO_REN = 1'b1;
            end
            LOAD0: begin
                spif.sLoad = 1'b1;
                spif.load_addr = ls_addr;
                if (spif.sLoad_hit) begin
                    spif.wFIFO_WEN = 1'b1;
                    spif.wFIFO_wdata.gemm_result = 1'b0;
                    spif.wFIFO_wdata.mat_s = ls_mat;
                    spif.wFIFO_wdata.row_s = 2'd0;
                    spif.wFIFO_wdata.data = spif.load_data;
                end
            end
            LOAD1: begin
                spif.sLoad = 1'b1;
                spif.load_addr = ls_addr;
                if (spif.sLoad_hit) begin
                    spif.wFIFO_WEN = 1'b1;
                    spif.wFIFO_wdata.gemm_result = 1'b0;
                    spif.wFIFO_wdata.mat_s = ls_mat;
                    spif.wFIFO_wdata.row_s = 2'd1;
                    spif.wFIFO_wdata.data = spif.load_data;
                end
            end
            LOAD2: begin
                spif.sLoad = 1'b1;
                spif.load_addr = ls_addr;
                if (spif.sLoad_hit) begin
                    spif.wFIFO_WEN = 1'b1;
                    spif.wFIFO_wdata.gemm_result = 1'b0;
                    spif.wFIFO_wdata.mat_s = ls_mat;
                    spif.wFIFO_wdata.row_s = 2'd2;
                    spif.wFIFO_wdata.data = spif.load_data;
                end
            end
            LOAD3: begin
                spif.sLoad = 1'b1;
                spif.load_addr = ls_addr;
                if (spif.sLoad_hit) begin
                    spif.wFIFO_WEN = 1'b1;
                    spif.wFIFO_wdata.gemm_result = 1'b0;
                    spif.wFIFO_wdata.mat_s = ls_mat;
                    spif.wFIFO_wdata.row_s = 2'd3;
                    spif.wFIFO_wdata.data = spif.load_data;
                end
            end
            STORE0: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = ls_addr;
                spif.rFIFO_wdata.mat_t = 2'd0;
                spif.rFIFO_wdata.mat_s = ls_mat;
                spif.rFIFO_wdata.row_s = 2'd0;
            end
            STORE1: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = ls_addr;
                spif.rFIFO_wdata.mat_t = 2'd0;
                spif.rFIFO_wdata.mat_s = ls_mat;
                spif.rFIFO_wdata.row_s = 2'd1;
            end
            STORE2: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = ls_addr;
                spif.rFIFO_wdata.mat_t = 2'd0;
                spif.rFIFO_wdata.mat_s = ls_mat;
                spif.rFIFO_wdata.row_s = 2'd2;
            end
            STORE3: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = ls_addr;
                spif.rFIFO_wdata.mat_t = 2'd0;
                spif.rFIFO_wdata.mat_s = ls_mat;
                spif.rFIFO_wdata.row_s = 2'd3;
            end
            W_GEMM0: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = '0;
                spif.rFIFO_wdata.mat_t = 2'd2;
                spif.rFIFO_wdata.mat_s = weight[MAT_S_W-1:0];
                spif.rFIFO_wdata.row_s = 2'd0;
            end
            W_GEMM1: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = '0;
                spif.rFIFO_wdata.mat_t = 2'd2;
                spif.rFIFO_wdata.mat_s = weight[MAT_S_W-1:0];
                spif.rFIFO_wdata.row_s = 2'd1;
            end
            W_GEMM2: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = '0;
                spif.rFIFO_wdata.mat_t = 2'd2;
                spif.rFIFO_wdata.mat_s = weight[MAT_S_W-1:0];
                spif.rFIFO_wdata.row_s = 2'd2;
            end
            W_GEMM3: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = '0;
                spif.rFIFO_wdata.mat_t = 2'd2;
                spif.rFIFO_wdata.mat_s = weight[MAT_S_W-1:0];
                spif.rFIFO_wdata.row_s = 2'd3;
            end
            I_GEMM0: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = '0;
                spif.rFIFO_wdata.mat_t = 2'd1;
                spif.rFIFO_wdata.mat_s = in[MAT_S_W-1:0];
                spif.rFIFO_wdata.row_s = 2'd0;
            end
            I_GEMM1: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = '0;
                spif.rFIFO_wdata.mat_t = 2'd1;
                spif.rFIFO_wdata.mat_s = in[MAT_S_W-1:0];
                spif.rFIFO_wdata.row_s = 2'd1;
            end
            I_GEMM2: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = '0;
                spif.rFIFO_wdata.mat_t = 2'd1;
                spif.rFIFO_wdata.mat_s = in[MAT_S_W-1:0];
                spif.rFIFO_wdata.row_s = 2'd2;
            end
            I_GEMM3: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = '0;
                spif.rFIFO_wdata.mat_t = 2'd1;
                spif.rFIFO_wdata.mat_s = in[MAT_S_W-1:0];
                spif.rFIFO_wdata.row_s = 2'd3;
            end
            PS_GEMM0: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = '0;
                spif.rFIFO_wdata.mat_t = 2'd3;
                spif.rFIFO_wdata.mat_s = partial_sum[MAT_S_W-1:0];
                spif.rFIFO_wdata.row_s = 2'd0;
            end
            PS_GEMM1: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = '0;
                spif.rFIFO_wdata.mat_t = 2'd3;
                spif.rFIFO_wdata.mat_s = partial_sum[MAT_S_W-1:0];
                spif.rFIFO_wdata.row_s = 2'd1;
            end
            PS_GEMM2: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = '0;
                spif.rFIFO_wdata.mat_t = 2'd3;
                spif.rFIFO_wdata.mat_s = partial_sum[MAT_S_W-1:0];
                spif.rFIFO_wdata.row_s = 2'd2;
            end
            PS_GEMM3: begin
                spif.rFIFO_WEN = 1'b1;
                spif.rFIFO_wdata.addr = '0;
                spif.rFIFO_wdata.mat_t = 2'd3;
                spif.rFIFO_wdata.mat_s = partial_sum[MAT_S_W-1:0];
                spif.rFIFO_wdata.row_s = 2'd3;
            end
        endcase
    end
endmodule