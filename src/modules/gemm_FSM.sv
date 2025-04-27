`include "sp_types_pkg.vh"
`include "gemm_FSM_if.vh"
/*
***** Fifo has space not implemented.
*/
import sp_types_pkg::*;

module gemm_FSM (
    input logic CLK, nRST,
    gemm_FSM_if.sp spif
);
    
    typedef enum logic [4:0] {  
        WEIGHT_STALL, WEIGHT0, WEIGHT1, WEIGHT2, WEIGHT3, BANK0_CHECK, BANK1_CHECK, BANK2_CHECK, 
        BANK3_CHECK, BANK0_0, BANK0_1, BANK0_2, BANK0_3, BANK1_0, BANK1_1, BANK1_2, BANK1_3, 
        BANK2_0, BANK2_1, BANK2_2, BANK2_3, BANK3_0, BANK3_1, BANK3_2, BANK3_3
    } state_t;

    // typedef enum logic [1:0] {  
    //     BANK0, BANK1, BANK2, BANK3
    // } WIFSM_t;

    state_t PSFSM_state, n_PSFSM_state, WIFSM_state, n_WIFSM_state;
    logic weight_status, n_weight_status; //1 = Weight needs to be loaded
    logic weight_loaded, PSgemmFIFO0_REN, PSgemmFIFO1_REN, PSgemmFIFO2_REN, PSgemmFIFO3_REN;
    logic WIgemmFIFO0_REN, WIgemmFIFO1_REN, WIgemmFIFO2_REN, WIgemmFIFO3_REN;

    assign spif.gemmFIFO0_REN = PSgemmFIFO0_REN || WIgemmFIFO0_REN;
    assign spif.gemmFIFO1_REN = PSgemmFIFO1_REN || WIgemmFIFO1_REN;
    assign spif.gemmFIFO2_REN = PSgemmFIFO2_REN || WIgemmFIFO2_REN;
    assign spif.gemmFIFO3_REN = PSgemmFIFO3_REN || WIgemmFIFO3_REN;

    always_ff @(posedge CLK, negedge nRST) begin
        if (nRST == 1'b0) begin
            weight_status <= 1'b1;
            PSFSM_state <= WEIGHT_STALL;
            WIFSM_state <= WEIGHT_STALL;
        end
        else begin
            weight_status <= n_weight_status;
            PSFSM_state <= n_PSFSM_state;
            WIFSM_state <= n_WIFSM_state;
        end
    end

    always_comb begin 
        n_weight_status = weight_status;
        if (spif.new_weight) begin
            n_weight_status = 1'b1;
        end
        else if (weight_loaded) begin
            n_weight_status = 1'b0;
        end
    end

    always_comb begin
        n_PSFSM_state = PSFSM_state;
        if (weight_status) begin
            n_PSFSM_state = WEIGHT_STALL;
        end
        else begin
            case(PSFSM_state)
                WEIGHT_STALL: n_PSFSM_state = BANK0_CHECK;
                BANK0_CHECK: n_PSFSM_state = ((spif.gemmFIFO0_rdata.mat_t == 2'd3) && (spif.gemmFIFO0_empty == 1'b0)) ? BANK0_0 : BANK1_CHECK;
                BANK1_CHECK: n_PSFSM_state = ((spif.gemmFIFO1_rdata.mat_t == 2'd3) && (spif.gemmFIFO1_empty == 1'b0)) ? BANK1_0 : BANK2_CHECK;
                BANK2_CHECK: n_PSFSM_state = ((spif.gemmFIFO2_rdata.mat_t == 2'd3) && (spif.gemmFIFO2_empty == 1'b0)) ? BANK2_0 : BANK3_CHECK;
                BANK3_CHECK: n_PSFSM_state = ((spif.gemmFIFO3_rdata.mat_t == 2'd3) && (spif.gemmFIFO3_empty == 1'b0)) ? BANK3_0 : BANK0_CHECK;
                BANK0_0: n_PSFSM_state = BANK0_1;
                BANK0_1: n_PSFSM_state = BANK0_2;
                BANK0_2: n_PSFSM_state = BANK0_3;
                BANK0_3: n_PSFSM_state = BANK1_CHECK;
                BANK1_0: n_PSFSM_state = BANK1_1;
                BANK1_1: n_PSFSM_state = BANK1_2;
                BANK1_2: n_PSFSM_state = BANK1_3;
                BANK1_3: n_PSFSM_state = BANK2_CHECK;
                BANK2_0: n_PSFSM_state = BANK2_1;
                BANK2_1: n_PSFSM_state = BANK2_2;
                BANK2_2: n_PSFSM_state = BANK2_3;
                BANK2_3: n_PSFSM_state = BANK3_CHECK;
                BANK3_0: n_PSFSM_state = BANK3_1;
                BANK3_1: n_PSFSM_state = BANK3_2;
                BANK3_2: n_PSFSM_state = BANK3_3;
                BANK3_3: n_PSFSM_state = BANK0_CHECK;
            endcase
        end
    end

    always_comb begin
        spif.partial_enable = 1'b0;
        spif.partial_sum_row_sel = 2'd0;
        spif.partial_sum_data = '0;
        PSgemmFIFO0_REN = 1'b0;
        PSgemmFIFO1_REN = 1'b0;
        PSgemmFIFO2_REN = 1'b0;
        PSgemmFIFO3_REN = 1'b0;
        case (PSFSM_state)
            BANK0_0: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd0;
                spif.partial_sum_data = spif.gemmFIFO0_rdata.data;
                PSgemmFIFO0_REN = 1'b1;
            end
            BANK0_1: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd1;
                spif.partial_sum_data = spif.gemmFIFO0_rdata.data;
                PSgemmFIFO0_REN = 1'b1;
            end
            BANK0_2: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd2;
                spif.partial_sum_data = spif.gemmFIFO0_rdata.data;
                PSgemmFIFO0_REN = 1'b1;
            end
            BANK0_3: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd3;
                spif.partial_sum_data = spif.gemmFIFO0_rdata.data;
                PSgemmFIFO0_REN = 1'b1;
            end
            BANK1_0: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd0;
                spif.partial_sum_data = spif.gemmFIFO1_rdata.data;
                PSgemmFIFO1_REN = 1'b1;
            end
            BANK1_1: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd1;
                spif.partial_sum_data = spif.gemmFIFO1_rdata.data;
                PSgemmFIFO1_REN = 1'b1;
            end
            BANK1_2: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd2;
                spif.partial_sum_data = spif.gemmFIFO1_rdata.data;
                PSgemmFIFO1_REN = 1'b1;
            end
            BANK1_3: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd3;
                spif.partial_sum_data = spif.gemmFIFO1_rdata.data;
                PSgemmFIFO1_REN = 1'b1;
            end
            BANK2_0: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd0;
                spif.partial_sum_data = spif.gemmFIFO2_rdata.data;
                PSgemmFIFO2_REN = 1'b1;
            end
            BANK2_1: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd1;
                spif.partial_sum_data = spif.gemmFIFO2_rdata.data;
                PSgemmFIFO2_REN = 1'b1;
            end
            BANK2_2: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd2;
                spif.partial_sum_data = spif.gemmFIFO2_rdata.data;
                PSgemmFIFO2_REN = 1'b1;
            end
            BANK2_3: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd3;
                spif.partial_sum_data = spif.gemmFIFO2_rdata.data;
                PSgemmFIFO2_REN = 1'b1;
            end
            BANK3_0: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd0;
                spif.partial_sum_data = spif.gemmFIFO3_rdata.data;
                PSgemmFIFO3_REN = 1'b1;
            end
            BANK3_1: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd1;
                spif.partial_sum_data = spif.gemmFIFO3_rdata.data;
                PSgemmFIFO3_REN = 1'b1;
            end
            BANK3_2: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd2;
                spif.partial_sum_data = spif.gemmFIFO3_rdata.data;
                PSgemmFIFO3_REN = 1'b1;
            end
            BANK3_3: begin
                spif.partial_enable = 1'b1;
                spif.partial_sum_row_sel = 2'd3;
                spif.partial_sum_data = spif.gemmFIFO3_rdata.data;
                PSgemmFIFO3_REN = 1'b1;
            end
        endcase
    end
    
    always_comb begin
        n_WIFSM_state = WIFSM_state;
        if (weight_status && !spif.drained) begin
            n_WIFSM_state = WEIGHT_STALL;
        end
        else begin
            case(WIFSM_state)
                WEIGHT_STALL: n_WIFSM_state = (spif.drained) ? BANK0_CHECK : WEIGHT_STALL;
                BANK0_CHECK: begin
                    if (weight_status) begin
                        n_WIFSM_state = ((spif.gemmFIFO0_rdata.mat_t == 2'd2) && (spif.gemmFIFO0_empty == 1'b0)) ? BANK0_0 : BANK1_CHECK;
                    end
                    else begin
                        n_WIFSM_state = ((spif.gemmFIFO0_rdata.mat_t == 2'd1) && (spif.gemmFIFO0_empty == 1'b0)) ? BANK0_0 : BANK1_CHECK;
                    end
                end
                BANK1_CHECK: begin
                    if (weight_status) begin
                        n_WIFSM_state = ((spif.gemmFIFO1_rdata.mat_t == 2'd2) && (spif.gemmFIFO1_empty == 1'b0)) ? BANK1_0 : BANK2_CHECK;
                    end
                    else begin
                        n_WIFSM_state = ((spif.gemmFIFO1_rdata.mat_t == 2'd1) && (spif.gemmFIFO1_empty == 1'b0)) ? BANK1_0 : BANK2_CHECK;
                    end
                end
                BANK2_CHECK: begin
                    if (weight_status) begin
                        n_WIFSM_state = ((spif.gemmFIFO2_rdata.mat_t == 2'd2) && (spif.gemmFIFO2_empty == 1'b0)) ? BANK2_0 : BANK3_CHECK;
                    end
                    else begin
                        n_WIFSM_state = ((spif.gemmFIFO2_rdata.mat_t == 2'd1) && (spif.gemmFIFO2_empty == 1'b0)) ? BANK2_0 : BANK3_CHECK;
                    end
                end
                BANK3_CHECK: begin
                    if (weight_status) begin
                        n_WIFSM_state = ((spif.gemmFIFO3_rdata.mat_t == 2'd2) && (spif.gemmFIFO3_empty == 1'b0)) ? BANK3_0 : BANK0_CHECK;
                    end
                    else begin
                        n_WIFSM_state = ((spif.gemmFIFO3_rdata.mat_t == 2'd1) && (spif.gemmFIFO3_empty == 1'b0)) ? BANK3_0 : BANK0_CHECK;
                    end
                end
                BANK0_0: n_WIFSM_state = BANK0_1;
                BANK0_1: n_WIFSM_state = BANK0_2;
                BANK0_2: n_WIFSM_state = BANK0_3;
                BANK0_3: n_WIFSM_state = BANK1_CHECK;
                BANK1_0: n_WIFSM_state = BANK1_1;
                BANK1_1: n_WIFSM_state = BANK1_2;
                BANK1_2: n_WIFSM_state = BANK1_3;
                BANK1_3: n_WIFSM_state = BANK2_CHECK;
                BANK2_0: n_WIFSM_state = BANK2_1;
                BANK2_1: n_WIFSM_state = BANK2_2;
                BANK2_2: n_WIFSM_state = BANK2_3;
                BANK2_3: n_WIFSM_state = BANK3_CHECK;
                BANK3_0: n_WIFSM_state = BANK3_1;
                BANK3_1: n_WIFSM_state = BANK3_2;
                BANK3_2: n_WIFSM_state = BANK3_3;
                BANK3_3: n_WIFSM_state = BANK0_CHECK;
            endcase
        end
    end

    always_comb begin
        spif.input_enable = 1'b0;
        spif.weight_enable = 1'b0;
        spif.weight_input_row_sel = 2'd0;
        spif.weight_input_data = '0;
        WIgemmFIFO0_REN = 1'b0;
        WIgemmFIFO1_REN = 1'b0;
        WIgemmFIFO2_REN = 1'b0;
        WIgemmFIFO3_REN = 1'b0;
        weight_loaded = 1'b0;
        case (WIFSM_state)
            BANK0_0: begin
                spif.weight_input_row_sel = 2'd0;
                spif.weight_input_data = spif.gemmFIFO0_rdata.data;
                WIgemmFIFO0_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK0_1: begin
                spif.weight_input_row_sel = 2'd1;
                spif.weight_input_data = spif.gemmFIFO0_rdata.data;
                WIgemmFIFO0_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK0_2: begin
                spif.weight_input_row_sel = 2'd2;
                spif.weight_input_data = spif.gemmFIFO0_rdata.data;
                WIgemmFIFO0_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK0_3: begin
                spif.weight_input_row_sel = 2'd3;
                spif.weight_input_data = spif.gemmFIFO0_rdata.data;
                WIgemmFIFO0_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                    weight_loaded = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK1_0: begin
                spif.weight_input_row_sel = 2'd0;
                spif.weight_input_data = spif.gemmFIFO1_rdata.data;
                WIgemmFIFO1_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK1_1: begin
                spif.weight_input_row_sel = 2'd1;
                spif.weight_input_data = spif.gemmFIFO1_rdata.data;
                WIgemmFIFO1_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK1_2: begin
                spif.weight_input_row_sel = 2'd2;
                spif.weight_input_data = spif.gemmFIFO1_rdata.data;
                WIgemmFIFO1_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK1_3: begin
                spif.weight_input_row_sel = 2'd3;
                spif.weight_input_data = spif.gemmFIFO1_rdata.data;
                WIgemmFIFO1_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                    weight_loaded = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK2_0: begin
                spif.weight_input_row_sel = 2'd0;
                spif.weight_input_data = spif.gemmFIFO2_rdata.data;
                WIgemmFIFO2_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK2_1: begin
                spif.weight_input_row_sel = 2'd1;
                spif.weight_input_data = spif.gemmFIFO2_rdata.data;
                WIgemmFIFO2_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK2_2: begin
                spif.weight_input_row_sel = 2'd2;
                spif.weight_input_data = spif.gemmFIFO2_rdata.data;
                WIgemmFIFO2_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK2_3: begin
                spif.weight_input_row_sel = 2'd3;
                spif.weight_input_data = spif.gemmFIFO2_rdata.data;
                WIgemmFIFO2_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                    weight_loaded = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK3_0: begin
                spif.weight_input_row_sel = 2'd0;
                spif.weight_input_data = spif.gemmFIFO3_rdata.data;
                WIgemmFIFO3_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK3_1: begin
                spif.weight_input_row_sel = 2'd1;
                spif.weight_input_data = spif.gemmFIFO3_rdata.data;
                WIgemmFIFO3_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK3_2: begin
                spif.weight_input_row_sel = 2'd2;
                spif.weight_input_data = spif.gemmFIFO3_rdata.data;
                WIgemmFIFO3_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
            BANK3_3: begin
                spif.weight_input_row_sel = 2'd3;
                spif.weight_input_data = spif.gemmFIFO3_rdata.data;
                WIgemmFIFO3_REN = 1'b1;
                if (weight_status) begin
                    spif.weight_enable = 1'b1;
                    weight_loaded = 1'b1;
                end
                else begin
                    spif.input_enable = 1'b1;
                end
            end
        endcase
    end


endmodule

/*
Inputs:
    gemmFIFO0_rdata
    gemmFIFO1_rdata
    gemmFIFO2_rdata
    gemmFIFO3_rdata
    gemmFIFO0_empty
    gemmFIFO1_empty
    gemmFIFO2_empty
    gemmFIFO3_empty
    drained
    fifo_has_space
    new_weight

Outputs:
    weight_input_data
    partial_sum_data
    weight_input_row_sel
    partial_sum_row_sel
    input_enable
    partial_enable
    weight_enable
    gemmFIFO0_REN
    gemmFIFO1_REN
    gemmFIFO2_REN
    gemmFIFO3_REN

*/

/*
    typedef enum logic [2:0] { 
        DECODE1, DECODE2, WEIGHT_LOAD, CONFLICT, NO_CONFLICT
    } state_t;

    state_t state, n_state;

    logic [2:0] weight_input_sel, partial_sum_sel;
    logic [1:0] n_weight_input_row_sel, n_partial_sum_row_sel;
    logic weight_input_row_sel_en, partial_sum_row_sel_en;
    logic [2:0] empty_count;
    
    assign empty_count = spif.gemmFIFO0_empty + spif.gemmFIFO1_empty + spif.gemmFIFO2_empty + spif.gemmFIFO3_empty;

    always_comb begin
        spif.weight_input_data = '0;
        case (weight_input_sel)
            2'd0: spif.weight_input_data = spif.gemmFIFO0_rdata[63:0];
            2'd1: spif.weight_input_data = spif.gemmFIFO1_rdata[63:0];
            2'd2: spif.weight_input_data = spif.gemmFIFO2_rdata[63:0];
            2'd3: spif.weight_input_data = spif.gemmFIFO3_rdata[63:0];
        endcase
    end

    always_comb begin
        spif.partial_sum_data = '0;
        case (partial_sum_sel)
            2'd0: spif.partial_sum_data = spif.gemmFIFO0_rdata[63:0];
            2'd1: spif.partial_sum_data = spif.gemmFIFO1_rdata[63:0];
            2'd2: spif.partial_sum_data = spif.gemmFIFO2_rdata[63:0];
            2'd3: spif.partial_sum_data = spif.gemmFIFO3_rdata[63:0];
        endcase
    end
    
    always_comb begin
        n_partial_sum_row_sel = spif.partial_sum_row_sel;
        n_weight_input_row_sel = spif.weight_input_row_sel;
        if (weight_input_row_sel_en) begin
            n_weight_input_row_sel += 1;
        end
        if (partial_sum_row_sel_en) begin
            n_partial_sum_row_sel += 1;
        end
    end

    always_ff @(posedge CLK, negedge nRST) begin
        if (nRST == 1'b0) begin
            state <= DECODE1;
            spif.weight_input_row_sel <= '0;
            spif.partial_sum_row_sel <= '0;
        end
        else begin
            state <= n_state;
            spif.weight_input_row_sel <= n_weight_input_row_sel;
            spif.partial_sum_row_sel <= n_partial_sum_row_sel;
        end
    end

    always_comb begin
        n_state = state;
        case (state) 
            DECODE1: begin
                if (empty_count != '0) begin
                    if ((spif.gemmFIFO0_rdata[69:68] == 2'd2) || (spif.gemmFIFO1_rdata[69:68] == 2'd2) || (spif.gemmFIFO2_rdata[69:68] == 2'd2) (spif.gemmFIFO3_rdata[69:68] == 2'd2)) begin
                        if (spif.drained) begin
                            n_state = WEIGHT_LOAD;
                        end
                    end
                    else begin
                        n_state = DECODE2;
                    end
                end
            end
            WEIGHT_LOAD: begin
                if(spif.weight_input_row_sel == 2'd3) begin
                    n_state = DECODE1;
                end
            end
            DECODE2: begin
                if (empty_count == 3'd1) begin
                    n_state = CONFLICT;
                end
                else begin
                    n_state = NO_CONFLICT;
                end
            end
        endcase
    end

    always_comb begin
        spif.gemmFIFO0_REN = 1'b0;
        spif.gemmFIFO1_REN = 1'b0;
        spif.gemmFIFO2_REN = 1'b0;
        spif.gemmFIFO3_REN = 1'b0;
        spif.weight_enable = 1'b0;
        weight_input_row_sel_en = 1'b0;
        weight_input_sel = 3'd7;
        case (state)
            WEIGHT_LOAD: begin
                spif.weight_enable = 1'b1;
                weight_input_row_sel_en = 1'b1;
                if (spif.gemmFIFO0_rdata[69:68] == 2'd2) begin
                    spif.gemmFIFO0_REN = 1'b1;
                    weight_input_sel = 3'd0;
                end
                else if (spif.gemmFIFO1_rdata[69:68] == 2'd2) begin
                    spif.gemmFIFO1_REN = 1'b1;
                    weight_input_sel = 3'd1;
                end
                else if (spif.gemmFIFO2_rdata[69:68] == 2'd2) begin
                    spif.gemmFIFO2_REN = 1'b1;
                    weight_input_sel = 3'd2;
                end
                else if (spif.gemmFIFO3_rdata[69:68] == 2'd2) begin
                    spif.gemmFIFO3_REN = 1'b1;
                    weight_input_sel = 3'd3;
                end
            end
            CONFLICT: begin
                
            end
        endcase
    end
*/