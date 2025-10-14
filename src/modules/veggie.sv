// Vector Register File Module ============================================
// Author: Joseph Ghanem
// Email: jghanem@purdue.edu
// Banked vector register file implementation for bf16 datatype
// ========================================================================
`include "vector_if.vh"
`include "vector_types.vh"

`define BANKNAME(P, N) P``BANK``N

module veggie #(
    parameter BANK_COUNT      = 4,
    parameter MASK_BANK_COUNT = 2,
    parameter DREAD_PORTS     = 4,
    parameter DWRITE_PORTS    = 4,
    parameter MREAD_PORTS     = 2,
    parameter MWRITE_PORTS    = 2,
    parameter BANK_IDX        = 2,
    parameter MASK_BANK_IDX   = 1
)(
    input logic CLK, nRST,
    vector_if.veggie vif
); 
    import vector_pkg::*;

    // BANK ADDRESS MAPPING
    logic [DREAD_PORTS-1:0][BANK_IDX-1:0]       vs_bnum;
    logic [DWRITE_PORTS-1:0][BANK_IDX-1:0]      vd_bnum;
    logic [MREAD_PORTS-1:0][MASK_BANK_IDX-1:0]  vms_bnum; 
    logic [MWRITE_PORTS-1:0][MASK_BANK_IDX-1:0] vmd_bnum; 

    generate
        genvar i;
        for (i = 0; i < DREAD_PORTS; i++)  assign vs_bnum[i] = vif.veggie_in.vs[i][BANK_IDX-1:0];
        for (i = 0; i < DWRITE_PORTS; i++) assign vd_bnum[i] = vif.veggie_in.vd[i][BANK_IDX-1:0];
        for (i = 0; i < MREAD_PORTS; i++)  assign vms_bnum[i] = vif.veggie_in.vms[i][MASK_BANK_IDX-1:0];
        for (i = 0; i < MWRITE_PORTS; i++) assign vmd_bnum[i] = vif.veggie_in.vmd[i][MASK_BANK_IDX-1:0];
    endgenerate

    logic [DREAD_PORTS-1:0]  bank_rreqs[BANK_COUNT-1:0],      bank_rpend[BANK_COUNT-1:0],      bank_rpend_nxt[BANK_COUNT-1:0];
    logic [DWRITE_PORTS-1:0] bank_wreqs[BANK_COUNT-1:0],      bank_wpend[BANK_COUNT-1:0],      bank_wpend_nxt[BANK_COUNT-1:0];
    logic [MREAD_PORTS-1:0]  bank_mrreqs[MASK_BANK_COUNT-1:0], bank_mrpend[MASK_BANK_COUNT-1:0], bank_mrpend_nxt[MASK_BANK_COUNT-1:0];
    logic [MWRITE_PORTS-1:0] bank_mwreqs[MASK_BANK_COUNT-1:0], bank_mwpend[MASK_BANK_COUNT-1:0], bank_mwpend_nxt[MASK_BANK_COUNT-1:0];

    // BANK MANAGEMENT BUSES AND WIRES
    bank_in_t      bank_in[BANK_COUNT-1:0]; 
    bank_out_t     bank_out[BANK_COUNT-1:0]; 
    mbank_in_t     mbank_in[MASK_BANK_COUNT-1:0];
    mbank_out_t    mbank_out[MASK_BANK_COUNT-1:0];
    vreg_t         bank_rdata[BANK_COUNT-1:0];
    logic [63:0]   bank_mrdata[MASK_BANK_COUNT-1:0]; 
    logic [DREAD_PORTS-1:0]  read_grants;
    logic [MREAD_PORTS-1:0]  mread_grants;
    logic conflict, d_conflict, m_conflict, nxt_conflict;
    conflict_state_t state, state_nxt;

    // SINGLE-STATE FSM
    always_comb begin : SINGLE_STATE_FSM
        for (int b = 0; b < BANK_COUNT; b++) begin
            bank_rreqs[b] = '0;
            bank_wreqs[b] = '0;
        end
        for (int b = 0; b < MASK_BANK_COUNT; b++) begin
            bank_mrreqs[b] = '0;
            bank_mwreqs[b] = '0;
        end
        for (int i = 0; i < DREAD_PORTS; i++)  if (vif.veggie_in.REN[i])  bank_rreqs[vs_bnum[i]][i] = 1'b1;
        for (int i = 0; i < DWRITE_PORTS; i++) if (vif.veggie_in.WEN[i])  bank_wreqs[vd_bnum[i]][i] = 1'b1;
        for (int i = 0; i < MREAD_PORTS; i++)  if (vif.veggie_in.MREN[i]) bank_mrreqs[vms_bnum[i]][i] = 1'b1;
        for (int i = 0; i < MWRITE_PORTS; i++) if (vif.veggie_in.MWEN[i]) bank_mwreqs[vmd_bnum[i]][i] = 1'b1;

        //enabled = |vif.veggie_in.REN || |vif.veggie_in.WEN || |vif.veggie_in.MREN || |vif.veggie_in.MWEN;
        //conflict = |{<<{bank_rpend_nxt, bank_wpend_nxt, bank_mrpend_nxt, bank_mwpend_nxt}};
        
        d_conflict = 1'b0;
        for (int b = 0; b < BANK_COUNT; b++) begin
            if ( ($countones(bank_rreqs[b]) > 1) || ($countones(bank_wreqs[b]) > 1)) begin
                d_conflict = 1'b1;
            end
        end
        m_conflict = 1'b0;
        for (int b = 0; b < MASK_BANK_COUNT; b++) begin
            if ( ($countones(bank_mrreqs[b]) > 1) || ($countones(bank_mwreqs[b]) > 1) ) begin
                m_conflict = 1'b1;
            end
        end
        conflict = d_conflict || m_conflict;

        case(state)
            READY: begin
                bank_rpend_nxt = bank_rreqs;
                bank_wpend_nxt = bank_wreqs;
                bank_mrpend_nxt = bank_mrreqs;
                bank_mwpend_nxt = bank_mwreqs;

                vif.veggie_out.ready = conflict;
                //conflict = |{<<{bank_rpend_nxt, bank_wpend_nxt, bank_mrpend_nxt, bank_mwpend_nxt}};
                state_nxt = (conflict) ? CONFLICT : READY;
            end
            CONFLICT: begin

                bank_rpend_nxt = bank_rpend;
                bank_wpend_nxt = bank_wpend;
                bank_mrpend_nxt = bank_mrpend;
                bank_mwpend_nxt = bank_mwpend;

                bank_rreqs = bank_rpend;
                bank_wreqs = bank_wpend;
                bank_mrreqs = bank_mrpend;
                bank_mwreqs = bank_mwpend;

                vif.veggie_out.ready = 1'b0;

                nxt_conflict = 1'b0;

                for (int b = 0; b < BANK_COUNT; b++) begin
                    if ( ($countones(bank_rpend_nxt[b]) > 1) || ($countones(bank_wpend_nxt[b]) > 1)) begin
                        nxt_conflict = 1'b1;
                    end
                end
                m_conflict = 1'b0;
                for (int b = 0; b < MASK_BANK_COUNT; b++) begin
                    if ( ($countones(bank_mrpend_nxt[b]) > 1) || ($countones(bank_mwpend_nxt[b]) > 1) ) begin
                        nxt_conflict = 1'b1;
                    end
                end
                state_nxt = (nxt_conflict/* && enabled*/) ? CONFLICT : READY;
            end
            default: begin vif.veggie_out.ready = 1'b0; state_nxt = READY; end
        endcase 

        read_grants     = '0;
        mread_grants    = '0;

        for (int b = 0; b < BANK_COUNT; b++) bank_in[b] = '{default:'0};
        for (int b = 0; b < MASK_BANK_COUNT; b++) mbank_in[b] = '{default:'0};

        for (int b = 0; b < BANK_COUNT; b++) begin
            if (|(bank_rreqs[b])) begin
                logic [DREAD_PORTS-1:0] winner;
                int winner_idx; 
                winner = bank_rreqs[b] & -bank_rreqs[b]; 
                winner_idx = $clog2(winner);
                
                // Bank Read Bus
                bank_in[b].REN = vif.veggie_in.REN[winner_idx];
                bank_in[b].vs = vif.veggie_in.vs[winner_idx];
                bank_in[b].tag = winner;

                bank_rpend_nxt[b] &= ~winner;
                read_grants[winner_idx] = 1'b1;
            end
            if (|(bank_wreqs[b])) begin
                logic [DWRITE_PORTS-1:0] winner;
                winner = bank_wreqs[b] & -bank_wreqs[b]; 

                // Setting Write Bus
                bank_in[b].WEN   = vif.veggie_in.WEN[$clog2(winner)];
                bank_in[b].vd    = vif.veggie_in.vd[$clog2(winner)];
                bank_in[b].vdata = vif.veggie_in.vdata[$clog2(winner)];

                bank_wpend_nxt[b] &= ~winner;
            end
        end
        for (int b = 0; b < MASK_BANK_COUNT; b++) begin
            if (|(bank_mrreqs[b])) begin
                logic [MREAD_PORTS-1:0] winner; 
                int winner_idx;  
                winner = bank_mrreqs[b] & -bank_mrreqs[b]; 
                winner_idx = $clog2(winner);

                // Mask Read Bus
                mbank_in[b].MREN = vif.veggie_in.MREN[winner_idx];
                mbank_in[b].vms  = vif.veggie_in.vms[winner_idx];
                mbank_in[b].tag  = winner;

                bank_mrpend_nxt[b] &= ~winner;
                mread_grants[winner_idx] = 1'b1;
            end
            if (|(bank_mwreqs[b])) begin
                logic [MWRITE_PORTS-1:0] winner;
                winner = bank_mwreqs[b] & -bank_mwreqs[b];

                // Mask Write Bus
                mbank_in[b].MWEN   = vif.veggie_in.MWEN[$clog2(winner)];
                mbank_in[b].vmd    = vif.veggie_in.vmd[$clog2(winner)];
                mbank_in[b].mvdata = vif.veggie_in.mvdata[$clog2(winner)];

                bank_mwpend_nxt[b] &= ~winner;
            end
        end
    end

    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            state <= READY;
            bank_rpend  <= bank_rreqs;
            bank_wpend  <= bank_wreqs;
            bank_mrpend <= bank_mrreqs;
            bank_mwpend <= bank_mwreqs;
        end else begin
            state <= state_nxt;
            bank_rpend  <= bank_rpend_nxt;
            bank_wpend  <= bank_wpend_nxt;
            bank_mrpend <= bank_mrpend_nxt;
            bank_mwpend <= bank_mwpend_nxt;
        end
    end

    generate
        genvar i_db, i_mb;
        for (i_mb = 0; i_mb < MASK_BANK_COUNT; i_mb++) begin : MASK_BANK_GEN
            vbank #(
                .DATA_WIDTH (1),                       // 1 bit per element
                .NUM_ELEMENTS(VLMAX),                  // 32 elements => 32-bit vector
                .NUM_ROWS   (NUM_MASKS),               // 8 masks per bank
                .INDEX_WIDTH($clog2(NUM_MASKS))        // 3 bits
            ) `BANKNAME(M, i_mb) (
                .clk(CLK),
                .ren(mbank_in[i_mb].MREN),   .raddr(mbank_in[i_mb].vms),    .rdata(mbank_out[i_mb].mdata),
                .wen(mbank_in[i_mb].MWEN),   .waddr(mbank_in[i_mb].vmd),    .wdata(mbank_in[i_mb].mvdata), .wstrb('1)
            );
        end
        for (i_db = 0; i_db < BANK_COUNT; i_db++) begin : DATA_BANK_GEN
            vbank #(
                .DATA_WIDTH (16),          
                .NUM_ELEMENTS(VLMAX),         
                .NUM_ROWS   (32),        
                .INDEX_WIDTH(8) 
            )`BANKNAME(D, i_db) (
                .clk(CLK),
                .ren(bank_in[i_db].REN),     .raddr(bank_in[i_db].vs),      .rdata(bank_out[i_db].ddata),
                .wen(bank_in[i_db].WEN),     .waddr(bank_in[i_db].vd),      .wdata(bank_in[i_db].vdata),   .wstrb('1)
            );
        end
    endgenerate

    always_comb begin : OUTPUTS
    vif.veggie_out.vreg   = '{default:'0};
    vif.veggie_out.dvalid = '0;
    vif.veggie_out.vmask   = '{default:'0};
    vif.veggie_out.mvalid  = '0;

    for (int b = 0; b < BANK_COUNT; b++) begin
        if (bank_in[b].REN) begin
        for (int p = 0; p < DREAD_PORTS; p++) begin
            if (bank_in[b].tag[p]) begin
                vif.veggie_out.vreg[p]   = bank_out[b].ddata;
                vif.veggie_out.dvalid[p] = 1'b1;
            end
        end
        end
    end

    for (int b = 0; b < MASK_BANK_COUNT; b++) begin
        if (mbank_in[b].MREN) begin
        for (int p = 0; p < MREAD_PORTS; p++) begin
            if (mbank_in[b].tag[p]) begin
                vif.veggie_out.vmask[p]   = mbank_out[b].mdata;
                vif.veggie_out.mvalid[p]  = 1'b1;
            end
        end
        end
    end
    end

endmodule