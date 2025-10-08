// Vector Register File Module ============================================
// Author: Joseph Ghanem
// Email: jghanem@purdue.edu
// Banked vector register file implementation for bf16 datatype
// ========================================================================
`include "vector_if.vh"
`include "vector_types.vh"
`include "vbank.sv"

`define BANKNAME(n) BANK``n

// Bank Bus
`define SET_READ_BANK_IN(bank, vif, i) \
    (bank).REN = (vif).REN[(i)];       \
    (bank).vs  = (vif).vs[(i)];
`define SET_WRITE_BANK_IN(bank, vif, i) \
    (bank).WEN   = (vif).WEN[(i)];      \
    (bank).vd    = (vif).vd[(i)];       \
    (bank).vdata = (vif).vdata[(i)];
`define SET_MASK_READ_BANK_IN(mbank, vif, i) \
    (mbank).MREN = (vif).MREN[(i)];          \
    (mbank).vms  = (vif).vms[(i)];
`define SET_MASK_WRITE_BANK_IN(mbank, vif, i) \
    (mbank).MWEN   = (vif).MWEN[(i)];         \
    (mbank).vmd    = (vif).vmd[(i)];          \
    (mbank).mvdata = (vif).mvdata[(i)];
`define SEND_BANK_IN(NUM_PORTS, cnflt, cnflt_nxt, bnum, bank_in, SET_MACRO  ) \
    for (int i = 0; i < NUM_PORTS; i++) begin \
        if (!|cnflt[i]) begin \
        `SET_MACRO(bank_in[bnum[i]], vif.veggie_in, i) \
        end else begin \
        int winR = first_one_idx#(NUM_PORTS)(cnflt[i]); \
        if (winR >= 0) begin \
            `SET_MACRO(bank_in[bnum[i]], vif.veggie_in, i) \
            logic [NUM_PORTS-1:0] keep_col_R = (logic [NUM_PORTS-1:0]'(1)) << winR; \
            for (int r = 0; r < NUM_PORTS; r++) cnflt_nxt[r] &= keep_col_R; \
        end \
        end \
    end

// NOTE: Test Read OR write with 4 banks and compare it to read AND write with 2 banks
// 35 mm 
module veggie #(
    parameter BANK_COUNT=4, //Num banks not including MASK banks
    parameter MASK_BANK_COUNT=2,
    parameter DREAD_PORTS=4, // Veggie #data read ports
    parameter DWRITE_PORTS=4, // Veggie #data write ports
    parameter MREAD_PORTS=2,
    parameter MWRITE_PORTS=2,
    parameter VM_COUNT=16,
    parameter VREG_COUNT=256 
)(
    input logic CLK, nRST,
    vector_if.veggie vif
); 
    import vector_pkg::*;

    // CONTROL LOGIC ========================================================
    fp16_t v1_buffer, v1_data, v2_data, vm_data;
    conflict_type_t conflict;
    
    // BANK ADDRESS MAPPING =================================================
    logic [DREAD_PORTS-1:0][$clog2(BANK_COUNT)-1:0] vs_bnum;
    logic [DWRITE_PORTS-1:0][$clog2(BANK_COUNT)-1:0] vd_bnum;
    logic [MREAD_PORTS-1:0][$clog2(MASK_BANK_COUNT)-1:0] vms_bnum; 
    logic [MWRITE_PORTS-1:0][$clog2(MASK_BANK_COUNT)-1:0] vmd_bnum; 

    genvar i;
    genvar j;
    generate
        // 1. DATA READ PORT ADDRESS
        for (i = 0; i < DREAD_PORTS; i++) begin : gen_read_bnum
            assign vs_bnum[i] = vif.veggie_in.vs[i][$clog2(BANK_COUNT)-1:0];
        end
        // 2. DATA WRITE PORT ADDRESS
        for (i = 0; i < DWRITE_PORTS; i++) begin : gen_write_bnum
            assign vd_bnum[i] = vif.veggie_in.vd[i][$clog2(BANK_COUNT)-1:0];
        end
        // 3. MASK READ ADDRESS
        for (i = 0; i < MREAD_PORTS; i++) begin : gen_read_mask_bnum
            assign vms_bnum[i] = vif.veggie_in.vms[i][$clog2(MASK_BANK_COUNT)-1:0];
        end
        // 4. MASK WRITE ADDRESS
        for (i = 0; i < MWRITE_PORTS; i++) begin : gen_write_mask_bnum
            assign vmd_bnum[i] = vif.veggie_in.vmd[i][$clog2(MASK_BANK_COUNT)-1:0];
        end
    endgenerate

    // CONFLICT DETECTION ===================================================
    logic [DREAD_PORTS-1:0][DREAD_PORTS-1:0] RR_CONFLICT;
    logic [DWRITE_PORTS-1:0][DWRITE_PORTS-1:0] WW_CONFLICT;
    logic [MREAD_PORTS-1:0][MREAD_PORTS-1:0] MRR_CONFLICT;
    logic [MWRITE_PORTS-1:0][MWRITE_PORTS-1:0] MWW_CONFLICT;

    generate
        // 1. DATA RR
        for (i = 0; i < DREAD_PORTS; i++) begin : gen_drr_matrix
            for (j = 0; j < DREAD_PORTS; j++) begin
                assign RR_CONFLICT[i][j] = (vif.veggie_in.REN[i]) &&
                                        vif.veggie_in.REN[j] &&
                                        (i != j) &&
                                        (vs_bnum[i] == vs_bnum[j]);
            end  
        end
        // 2. DATA WW (Write-Write Vector)
        for (i = 0; i < DWRITE_PORTS; i++) begin : gen_dww_matrix
            for (j = 0; j < DWRITE_PORTS; j++) begin
                assign WW_CONFLICT[i][j] = (vif.veggie_in.WEN[i] &&
                                        vif.veggie_in.WEN[j] &&
                                        (i != j) &&
                                        (vd_bnum[i] == vd_bnum[j]));
            end
        end
        // 3. MASK RR (Read-Read Vector)
        for (i = 0; i < MREAD_PORTS; i++) begin : gen_mrr_matrix
            for (j = 0; j < MREAD_PORTS; j++) begin
                assign MRR_CONFLICT[i][j] = (vif.veggie_in.MREN[i] &&
                                        vif.veggie_in.MREN[j] &&
                                        (i != j) &&
                                        (vms_bnum[i] == vms_bnum[j]));
            end
        end
        // 4. MASK WW (Write-Write Vector)
        for (i = 0; i < MWRITE_PORTS; i++) begin : gen_mww_matrix
            for (j = 0; j < MWRITE_PORTS; j++) begin
                assign MWW_CONFLICT[i][j] = (vif.veggie_in.MWEN[i] &&
                                        vif.veggie_in.MWEN[j] &&
                                        (i != j) &&
                                        (vmd_bnum[i] == vmd_bnum[j]));
            end
        end
    endgenerate

    // BANK MANAGEMENT ======================================================
    bank_in_t bank_in [BANK_COUNT-1:0]; 
    mask_bank_in_t mbank_in [MASK_BANK_COUNT-1:0];
    logic conflict;
    conflict_state_t state, next_state;

    logic [DREAD_PORTS-1:0][DREAD_PORTS-1:0] rr_cnflt_mgmt;
    logic [DWRITE_PORTS-1:0][DWRITE_PORTS-1:0]   ww_cnflt_mgmt;
    logic [MREAD_PORTS-1:0][MREAD_PORTS-1:0]     mrr_cnflt_mgmt;
    logic [MWRITE_PORTS-1:0][MWRITE_PORTS-1:0]   mww_cnflt_mgmt;

    function automatic int first_one_idx #(
        int NUM_PORTS
    ) (input logic [NUM_PORTS-1:0] row);
        for (int k = 0; k < NUM_PORTS; k++)
            if (row[k] === 1'b1) return k;
        return -1;
    endfunction
    
    always_comb begin : CONFLICT_HANDLING
        // start from base matrices
        casez(state)
          IDLE: begin
            // clear bank buses
            for (int b = 0; b < BANK_COUNT; b++)
                bank_in[b] = '{default:'0};
            for (int mb = 0; mb < MASK_BANK_COUNT; mb++)
                mbank_in[mb] = '{default:'0};

            // -------------------- DATA BANKS --------------------
            for (int b = 0; b < BANKS; i++) begin

            end
            // -------------------- DATA READS --------------------
            for (int i = 0; i < DREAD_PORTS; i++) begin
                if (!|rr_cnflt_mgmt[i]) begin
                `SET_READ_BANK_IN(bank_in[vs_bnum[i]], vif.veggie_in, i)
                end else begin
                int winR = first_one_idx#(DREAD_PORTS)(rr_cnflt_mgmt[i]);
                if (winR >= 0) begin
                    `SET_READ_BANK_IN(bank_in[vs_bnum[i]], vif.veggie_in, i)
                    logic [DREAD_PORTS-1:0] keep_col_R = (logic [DREAD_PORTS-1:0]'(1)) << winR;
                    for (int r = 0; r < DREAD_PORTS; r++) rr_cnflt_nxt[r] &= keep_col_R;
                end
                end
            end

            // -------------------- DATA WRITES --------------------

            for (int w = 0; w < DWRITE_PORTS; w++) begin
                if (!|ww_cnflt_mgmt[w]) begin
                `SET_WRITE_BANK_IN(bank_in[vd_bnum[w]], vif.veggie_in, w)
                end else begin
                int winW = first_one_idx#(DWRITE_PORTS)(ww_cnflt_mgmt[w]);
                if (winW >= 0) begin
                    `SET_WRITE_BANK_IN(bank_in[vd_bnum[w]], vif.veggie_in, w)
                    logic [DWRITE_PORTS-1:0] keep_col_W = (logic [DWRITE_PORTS-1:0]'(1)) << winW;
                    for (int r = 0; r < DWRITE_PORTS; r++) ww_cnflt_nxt[r] &= keep_col_W;
                end
                end
            end

            // -------------------- MASK READS --------------------
            for (int mr = 0; mr < MREAD_PORTS; mr++) begin
                if (!|mrr_cnflt_mgmt[mr]) begin
                `SET_MASK_READ_BANK_IN(mbank_in[vms_bnum[mr]], vif.veggie_in, mr)
                end else begin
                int winMR = first_one_idx#(MREAD_PORTS)(mrr_cnflt_mgmt[mr]);
                if (winMR >= 0) begin
                    `SET_MASK_READ_BANK_IN(mbank_in[vms_bnum[mr]], vif.veggie_in, mr)
                    logic [MREAD_PORTS-1:0] keep_col_MR = (logic [MREAD_PORTS-1:0]'(1)) << winMR;
                    for (int r = 0; r < MREAD_PORTS; r++) mrr_cnflt_nxt[r] &= keep_col_MR;
                end
                end
            end

            // -------------------- MASK WRITES --------------------
            for (int mw = 0; mw < MWRITE_PORTS; mw++) begin
                if (!|mww_cnflt_mgmt[mw]) begin
                `SET_MASK_WRITE_BANK_IN(mbank_in[vmd_bnum[mw]], vif.veggie_in, mw)
                end else begin
                int winMW = first_one_idx#(MWRITE_PORTS)(mww_cnflt_mgmt[mw]);
                if (winMW >= 0) begin
                    `SET_MASK_WRITE_BANK_IN(mbank_in[vmd_bnum[mw]], vif.veggie_in, mw)
                    logic [MWRITE_PORTS-1:0] keep_col_MW = (logic [MWRITE_PORTS-1:0]'(1)) << winMW;
                    for (int r = 0; r < MWRITE_PORTS; r++) mww_cnflt_nxt[r] &= keep_col_MW;
                end
                end
            end

            // -------------------- Output --------------------
            conflict = (|rr_cnflt_mgmt || |ww_cnflt_mgmt || |mrr_cnflt_mgmt || |mww_cnflt_mgmt);
            vif.veggie_out.ready = conflict 
            if (conflict) begin
                next_state = CONFLICT;
            end else begin
                next_state = IDLE;
            end
          end
          CONFLICT: begin
            // -------------------- Data Banks --------------------


            // -------------------- Mask Banks --------------------

            // -------------------- Output --------------------
            conflict = (|rr_cnflt_mgmt || |ww_cnflt_mgmt || |mrr_cnflt_mgmt || |mww_cnflt_mgmt);
            vif.veggie_out.ready = conflict 
            if (conflict) begin
                next_state = CONFLICT;
            end else begin
                next_state = IDLE;
            end
          end
          default begin 
            next_state = IDLE;
            vif.veggie_out.ready = 1'b0;
          end
        endcase
    end
    
    // FSM for handling conflicts
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            rr_cnflt_mgmt  <= RR_CONFLICT;
            ww_cnflt_mgmt  <= WW_CONFLICT;
            mrr_cnflt_mgmt <= MRR_CONFLICT;
            mww_cnflt_mgmt <= MWW_CONFLICT;
            state <= IDLE;
        end else begin
            rr_cnflt_mgmt  <= rr_cnflt_nxt;
            ww_cnflt_mgmt  <= ww_cnflt_nxt;
            mrr_cnflt_mgmt <= mrr_cnflt_nxt;
            mww_cnflt_mgmt <= mww_cnflt_nxt;
            state <= next_state;
        end
    end

    // Bank Gen =============================================================
    // Assigning bank inputs
    assign bank_in = '0;
    assign bank_in[BANK_COUNT] = bank_vd : (vif.vm == '1) ? (vd_bnum == '1) ? bank_cfg : '0;
    assign bank_in[vd_bnum] = bank_vd;
    assign bank_in[vs1_bnum] = bank_vs1;
    assign bank_in[vs2_bnum] = bank_vs2;

    vbank BANKNAME(_CNTRL) #(
        .INDEX_WIDTH(1),
        .NUM_ELEMENTS(32),
        .DATA_WIDTH(16),
        .NUM_ROWS(1) 
    ) bank (
        .clk(CLK),

        .ren(vif.vm),
        .raddr('0),
        .rdata(vm_data),

        .wen(bank_in[BANK_COUNT].WEN),
        .waddr('0),
        .wdata(bank_in[BANK_COUNT].vdata),
        .wstrb({NUM_ELEMENTS{bank_in[BANK_COUNT].WEN}})
    );

    genvar i;
    generate
        for (i = 0; i < BANK_COUNT; i = i + 1) begin : BANK_GEN
            vbank BANKNAME(i) (
                .clk(CLK),

                .ren(bank_in[i].REN),
                .raddr(bank_in[i].vs),
                .rdata( (i == vs1_bnum) ? v1_data : (i == vs2_bnum) ? v2_data : '0 ),

                .wen(bank_in[i].WEN),
                .waddr(bank_in[i].vd),
                .wdata(bank_in[i].vdata),
                .wstrb({NUM_ELEMENTS{bank_in[i].WEN}})
            );
        end
    endgenerate

    // Mini Operand Buffer ==================================================
    always_ff @(posedge CLK or negedge nRST) begin : Operand_Buffer
        if (!nRST) begin
            v1_buffer = '0;
        end else if (vif.conflict) begin
            v1_buffer = vif.v1;
        end
    end

    always_comb begin : OUTPUTS
        if (conflict) begin
            vif.veggie_out.v1 = v1_buffer;
            vif.veggie_out.v2 = v2_data;
            vif.veggie_out.vmask = vm_data;
            vif.veggie_out.ready = 1'b0;
        end else begin
            vif.veggie_out.v1 = v1_data;
            vif.veggie_out.v2 = v2_data;
            vif.veggie_out.vmask = vm_data;
            vif.veggie_out.ready = 1'b1;
        end
    end
endmodule
