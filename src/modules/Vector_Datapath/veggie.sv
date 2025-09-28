// Vector Register File Module ============================================
// Author: Joseph Ghanem
// Email: jghanem@purdue.edu
// Banked vector register file implementation for fp16 datatype
// ========================================================================
`include "vector_if.vh"
`include "vector_types.vh"
`include "vbank.sv"

`define BANKNAME(n) BANK``n

`define SET_BANK_IN(bank, vif, vs) \ //VS is 1, 2, or 0 for vd
    bank.REN    = (vs == 0) ? '0 : vif.REN; \
    bank.WEN    = (vs == 0) ? vif.WEN : '0; \
    bank.tag    = (vs == 1) ? '0 : '1; \
    bank.vs     = (vs == 0) ? '0 : vif.vs[vs]; \
    bank.vd     = (vs == 0) ? vif.vd : '0; \
    bank.vdata  = (vs == 0) ? vif.vdata : '0;

// NOTE: Test Read OR write with 4 banks and compare it to read AND write with 2 banks
module veggie #(
    parameter BANK_COUNT=4, //Num banks not including control bank
    parameter VREG_COUNT=256 
)(
    input logic CLK, nRST,
    vector_if.veggie vif
); 
    import vector_pkg::*;

    // Control Logic ========================================================
    logic [$clog2(BANK_COUNT):0] vs1_bnum, vs2_bnum, vd_bnum; // +1 for control reg
    fp16_t v1_buffer, v1_data, v2_data, vm_data;
    bank_in_t bank_vs1, bank_vs2, bank_vd;
    bank_in_t bank_in [BANK_COUNT+1]; // +1 for control reg
    conflict_state_t state, next_state;
    conflict_type_t conflict;
    
    assign vs1_bnum = (vif.vs1 == '0) ? '1 : vif.vs1[1:0] % VREG_COUNT;
    assign vs2_bnum = (vif.vs2 == '0) ? '1 : vif.vs2[1:0] % VREG_COUNT;
    assign vd_bnum  = (vif.vd == '0) ? '1 : vif.vd[1:0] % VREG_COUNT;

    // 2 types of conflicts: 10 RR, 1x RW
    always_comb begin : CONFLICT_DETECT
        conflict = 1'b0;
        if (vif.REN && vif.WEN) begin
            if ((vs1_bnum == vd_bnum) || (vs2_bnum == vd_bnum)) begin
                conflict = RW_CONFLICT ^ {1'b0, vs2_bnum == vd_bnum}; // 11 RW w/ v2,  10 w/ v1
            end 
        end else if (vif.REN) begin
            if (vs1_bnum == vs2_bnum) begin
                conflict = RR_CONFLICT;
            end 
        end 
    end 

    always_comb begin : CONFLICT_HANDLING

        `` SET_BANK_IN(bank_vs1, vif, 1)``
        `` SET_BANK_IN(bank_vs2, vif, 2)``
        `` SET_BANK_IN(bank_vd, vif, 0)``

        if (conflict[1]) begin  
            casez(state) : CONFLICT_HANDING
                IDLE: begin
                    vif.conflict = 1'b1;
                    if (conflict == RW_CONFLICT) begin
                        vd_bnum = 1 << $clog2(BANK_COUNT);
                        next_state = WRITE;
                    end else begin 
                        vs2_bnum = 1 << $clog2(BANK_COUNT); //setting to invalid bank (MSB=1)
                        next_state = READ;
                    end 
                end 
                READ: begin
                    vs2_bnum = vs1_bnum;
                    vif.conflict = 1'b0;
                    next_state = IDLE;
                end
                WRITE: begin
                    vd_bnum = (conflict[0]) ? vs2_bnum : vs1_bnum;
                    vif.conflict = 1'b0;
                    next_state = IDLE;
                end
                default: next_state = IDLE;
            endcase
        end
    end
    
    // FSM for handling conflicts
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            state <= IDLE;
        end else begin
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
