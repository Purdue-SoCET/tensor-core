`include "types_pkg.vh"
`include "load_FSM_if.vh"
import types_pkg::*;

module load_FSM (
    input logic CLK, nRST,
    load_FSM_if.sp spif
);

    typedef enum logic[4:0] { 
        DECODE, LOAD, STORE0, STORE1, STORE2, STORE3, I_GEMM0, I_GEMM1, 
        I_GEMM2, I_GEMM3, W_GEMM0, W_GEMM1, W_GEMM2, W_GEMM3, PS_GEMM0, 
        PS_GEMM1, PS_GEMM2, PS_GEMM3, PSUMLOAD
    } state_t;

    state_t state, n_state;
    logic [MAT_S_W+ROW_S_W-1:0] load_mat, n_load_mat, n_gemm_mat, gemm_mat;
    logic psumoutFIFO_WEN, psumoutFIFO_empty;
    logic [BITS_PER_ROW+ROW_S_W-1:0] psumoutFIFO_wdata;

    always_ff @(posedge CLK, negedge nRST) begin
        if (nRST == 1'b0) begin
            state <= DECODE;
            load_mat <= '0;
            gemm_mat <= '0;
        end
        else begin
            state <= n_state;
            load_mat <= n_load_mat;
            gemm_mat <= n_gemm_mat;
        end
    end

    always_comb begin
        n_state = state;
        case (state)
            DECODE: begin
                if (psumoutFIFO_empty == 1'b0) begin
                    n_state = PSUMLOAD;
                end
                else if  (spif.instr_FIFO_empty == 1'b0) begin
                    case(spif.instrFIFO_rdata[37:36]) 
                        2'b01: n_state = LOAD;
                        2'b10: n_state = STORE0;
                        2'b11: begin
                            if (spif.instr_FIFO_rdata[35]) begin
                                n_state = W_GEMM0;
                            end
                            else begin
                                n_state = I_GEMM0;
                            end
                        end
                    endcase
                end
            end
            LOAD: begin
                if (spif.sLoad_row == 2'd3) begin
                    n_state = DECODE;
                end
            end
            STORE0: begin
                case (spif.instrFIFO_rdata[35:34])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = STORE1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = STORE1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = STORE1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = STORE1;
                        end
                    end
                endcase
            end
            STORE1: begin
                case (spif.instrFIFO_rdata[35:34])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = STORE2;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = STORE2;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = STORE2;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = STORE2;
                        end
                    end
                endcase
            end
            STORE2: begin
                case (spif.instrFIFO_rdata[35:34])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = STORE3;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = STORE3;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = STORE3;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = STORE3;
                        end
                    end
                endcase
            end
            STORE3: begin
                case (spif.instrFIFO_rdata[35:34])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = DECODE;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = DECODE;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = DECODE;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = DECODE;
                        end
                    end
                endcase
            end
            I_GEMM0: begin
                case (spif.instrFIFO_rdata[11:10])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = I_GEMM1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = I_GEMM1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = I_GEMM1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = I_GEMM1;
                        end
                    end
                endcase
            end
            I_GEMM1: begin
                case (spif.instrFIFO_rdata[11:10])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = I_GEMM2;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = I_GEMM2;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = I_GEMM2;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = I_GEMM2;
                        end
                    end
                endcase
            end
            I_GEMM2: begin
                case (spif.instrFIFO_rdata[11:10])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = I_GEMM3;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = I_GEMM3;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = I_GEMM3;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = I_GEMM3;
                        end
                    end
                endcase
            end
            I_GEMM3: begin
                case (spif.instrFIFO_rdata[11:10])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = PS_GEMM0;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = PS_GEMM0;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = PS_GEMM0;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = PS_GEMM0;
                        end
                    end
                endcase
            end
            W_GEMM0: begin
                case (spif.instrFIFO_rdata[7:6])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = W_GEMM1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = W_GEMM1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = W_GEMM1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = W_GEMM1;
                        end
                    end
                endcase
            end
            W_GEMM1: begin
                case (spif.instrFIFO_rdata[7:6])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = W_GEMM2;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = W_GEMM2;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = W_GEMM2;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = W_GEMM2;
                        end
                    end
                endcase
            end
            W_GEMM2: begin
                case (spif.instrFIFO_rdata[7:6])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = W_GEMM3;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = W_GEMM3;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = W_GEMM3;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = W_GEMM3;
                        end
                    end
                endcase
            end
            W_GEMM3: begin
                case (spif.instrFIFO_rdata[7:6])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = I_GEMM0;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = I_GEMM0;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = I_GEMM0;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = I_GEMM0;
                        end
                    end
                endcase
            end
            PS_GEMM0: begin
                case (spif.instrFIFO_rdata[3:2])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = PS_GEMM1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = PS_GEMM1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = PS_GEMM1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = PS_GEMM1;
                        end
                    end
                endcase
            end
            PS_GEMM1: begin
                case (spif.instrFIFO_rdata[3:2])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = PS_GEMM2;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = PS_GEMM2;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = PS_GEMM2;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = PS_GEMM2;
                        end
                    end
                endcase
            end
            PS_GEMM2: begin
                case (spif.instrFIFO_rdata[3:2])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = PS_GEMM3;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = PS_GEMM3;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = PS_GEMM3;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = PS_GEMM3;
                        end
                    end
                endcase
            end
            PS_GEMM3: begin
                case (spif.instrFIFO_rdata[3:2])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            n_state = DECODE;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            n_state = DECODE;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            n_state = DECODE;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            n_state = DECODE;
                        end
                    end
                endcase
            end
            PSUMLOAD: begin
                if (psumoutFIFO_rdata[65:64 == 2'd3]) begin
                    n_state = DECODE;
                end
            end
        endcase
    end

    always_comb begin
        spif.sLoad = 1'b0;
        spif.load_addr = '0;
        n_load_mat = load_mat;
        spif.instrFIFO_REN = 1'b0;
        spif.wFIFO0_wdata = '0;
        spif.wFIFO1_wdata = '0;
        spif.wFIFO2_wdata = '0;
        spif.wFIFO3_wdata = '0;
        spif.wFIFO0_WEN = 1'b0;
        spif.wFIFO1_WEN = 1'b0;
        spif.wFIFO2_WEN = 1'b0;
        spif.wFIFO3_WEN = 1'b0;
        storeFIFO_wdata = '0;
        storeFIFO_WEN = 1'b0;
        n_gemm_mat = gemm_mat;
        psumoutFIFO_REN = 1'b0;
        spif.rFIFO0_wdata = '0;
        spif.rFIFO0_WEN = 1'b0;
        spif.rFIFO1_wdata = '0;
        spif.rFIFO1_WEN = 1'b0;
        spif.rFIFO2_wdata = '0;
        spif.rFIFO2_WEN = 1'b0;
        spif.rFIFO3_wdata = '0;
        spif.rFIFO3_WEN = 1'b0;
        spif.new_weight = 1'b0;
        case (state)    
            LOAD: begin     //Must be in LOAD for more than 1 cycle
                spif.sLoad = 1'b1;
                spif.load_addr = spif.instrFIFO_rdata[31:0];
                n_load_mat = spif.instrFIFO_rdata[35:32];
                if (spif.sLoad_hit) begin    
                    case (load_mat[3:2])
                        2'd0: begin
                            spif.wFIFO0_wdata = {1'b0, load_mat[1:0], spif.sLoad_row, spif.load_data};          //Does not check to see if FIFO is full
                            spif.wFIFO0_WEN = 1'b1;
                        end
                        2'd1: begin
                            spif.wFIFO1_wdata = {1'b0, load_mat[1:0], spif.sLoad_row, spif.load_data};          //Does not check to see if FIFO is full
                            spif.wFIFO1_WEN = 1'b1;
                        end
                        2'd2: begin
                            spif.wFIFO2_wdata = {1'b0, load_mat[1:0], spif.sLoad_row, spif.load_data};          //Does not check to see if FIFO is full
                            spif.wFIFO2_WEN = 1'b1;
                        end
                        2'd3: begin
                            spif.wFIFO3_wdata = {1'b0, load_mat[1:0], spif.sLoad_row, spif.load_data};          //Does not check to see if FIFO is full
                            spif.wFIFO3_WEN = 1'b1;
                        end
                    endcase
                end
                if (spif.sLoad_row == 2'd3) begin
                    spif.instrFIFO_REN = 1'b1;
                end
            end
            STORE0: begin
                case (spif.instrFIFO_rdata[35:34])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd0};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd0};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd0};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd0};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            STORE1: begin
                case (spif.instrFIFO_rdata[35:34])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd1};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd1};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd1};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd1};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            STORE2: begin
                case (spif.instrFIFO_rdata[35:34])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd2};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd2};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd2};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd2};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            STORE3: begin
                case (spif.instrFIFO_rdata[35:34])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd3};
                            spif.rFIFO0_WEN = 1'b1;
                            spif.instrFIFO_REN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd3};
                            spif.rFIFO1_WEN = 1'b1;
                            spif.instrFIFO_REN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd3};
                            spif.rFIFO2_WEN = 1'b1;
                            spif.instrFIFO_REN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {spif.instrFIFO_rdata[31:0], 2'd0, spif.instrFIFO_rdata[33:32], 2'd3};
                            spif.rFIFO3_WEN = 1'b1;
                            spif.instrFIFO_REN = 1'b1;
                        end
                    end
                endcase
            end
            I_GEMM0: begin
                case (spif.instrFIFO_rdata[11:10])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd0};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd0};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd0};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd0};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            I_GEMM1: begin
                case (spif.instrFIFO_rdata[11:10])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd1};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd1};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd1};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd1};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            I_GEMM2: begin
                case (spif.instrFIFO_rdata[11:10])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd2};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd2};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd2};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd2};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            I_GEMM3: begin
                case (spif.instrFIFO_rdata[11:10])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd3};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd3};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd3};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {32'b0, 2'd1, spif.instrFIFO_rdata[9:8], 2'd3};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            W_GEMM0: begin
                spif.new_weight = 1'b1;
                case (spif.instrFIFO_rdata[7:6])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd0};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd0};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd0};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd0};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            W_GEMM1: begin
                case (spif.instrFIFO_rdata[7:6])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd1};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd1};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd1};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd1};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            W_GEMM2: begin
                case (spif.instrFIFO_rdata[7:6])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd2};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd2};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd2};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd2};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            W_GEMM3: begin
                case (spif.instrFIFO_rdata[7:6])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd3};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd3};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd3};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {32'b0, 2'd2, spif.instrFIFO_rdata[5:4], 2'd3};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            PS_GEMM0: begin
                case (spif.instrFIFO_rdata[3:2])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd0};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd0};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd0};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd0};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            PS_GEMM1: begin
                case (spif.instrFIFO_rdata[3:2])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd1};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd1};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd1};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd1};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            PS_GEMM2: begin
                case (spif.instrFIFO_rdata[3:2])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd2};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd2};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd2};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd2};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            PS_GEMM3: begin
                case (spif.instrFIFO_rdata[3:2])
                    2'd0: begin
                        if(spif.rFIFO0_full == 1'b0) begin
                            spif.rFIFO0_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd3};
                            spif.rFIFO0_WEN = 1'b1;
                        end
                    end
                    2'd1: begin
                        if(spif.rFIFO1_full == 1'b0) begin
                            spif.rFIFO1_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd3};
                            spif.rFIFO1_WEN = 1'b1;
                        end
                    end
                    2'd2: begin
                        if(spif.rFIFO2_full == 1'b0) begin
                            spif.rFIFO2_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd3};
                            spif.rFIFO2_WEN = 1'b1;
                        end
                    end
                    2'd3: begin
                        if(spif.rFIFO3_full == 1'b0) begin
                            spif.rFIFO3_wdata = {32'b0, 2'd3, spif.instrFIFO_rdata[1:0], 2'd3};
                            spif.rFIFO3_WEN = 1'b1;
                        end
                    end
                endcase
            end
            PSUMLOAD: begin
                case (gemm_mat[3:2])
                    2'd0: begin
                        spif.wFIFO0_wdata = {1'b1, gemm_mat[1:0], psumoutFIFO_rdata};          //Does not check to see if FIFO is full
                        spif.wFIFO0_WEN = 1'b1;
                        psumoutFIFO_REN = 1'b1;
                    end
                    2'd1: begin
                        spif.wFIFO1_wdata = {1'b1, gemm_mat[1:0], psumoutFIFO_rdata};          //Does not check to see if FIFO is full
                        spif.wFIFO1_WEN = 1'b1;
                        psumoutFIFO_REN = 1'b1;
                    end
                    2'd2: begin
                        spif.wFIFO2_wdata = {1'b1, gemm_mat[1:0], psumoutFIFO_rdata};          //Does not check to see if FIFO is full
                        spif.wFIFO2_WEN = 1'b1;
                        psumoutFIFO_REN = 1'b1;
                    end
                    2'd3: begin
                        spif.wFIFO3_wdata = {1'b1, gemm_mat[1:0], psumoutFIFO_rdata};          //Does not check to see if FIFO is full
                        spif.wFIFO3_WEN = 1'b1;
                        psumoutFIFO_REN = 1'b1;
                    end
                endcase
            end
        endcase
    end

    socetlib_fifo #(.T(logic [BITS_PER_ROW+ROW_S_W-1:0]), .DEPTH(8)) psumoutFIFO (.CLK(CLK), 
    .nRST(nRST), .WEN(spif.psumoutFIFO_WEN), .REN(psumoutFIFO_REN), .clear(), .wdata(spif.psumoutFIFO_wdata), 
    .full(spif.psumoutFIFO_full), .empty(psumoutFIFO_empty), .underrun(), .overrun(), .count(), .rdata(psumoutFIFO_rdata));

endmodule
/*

Inputs:
rFIFO0_full
rFIFO1_full
rFIFO2_full
rFIFO3_full

Outputs:
rFIFO0_wdata
rFIFO0_WEN
rFIFO1_wdata
rFIFO1_WEN
rFIFO2_wdata
rFIFO2_WEN
rFIFO3_wdata
rFIFO3_WEN


*/
/*

Inputs:
instrFIFO_rdata
instrFIFO_empty
sLoad_hit
sLoad_row
load_data
wFIFO0_full
wFIFO1_full
wFIFO2_full
wFIFO3_full
storeFIFO_REN
psumoutFIFO_WEN
psumoutFIFO_wdata

Outputs:
instrFIFO_REN
sLoad
load_addr
wFIFO0_wdata
wFIFO0_WEN
wFIFO1_wdata
wFIFO1_WEN
wFIFO2_wdata
wFIFO2_WEN
wFIFO3_wdata
wFIFO3_WEN
storeFIFO_rdata
storeFIFO_empty
psumoutFIFO_full


*/