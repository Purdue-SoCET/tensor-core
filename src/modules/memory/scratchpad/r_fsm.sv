/*
  Rafael Monteiro Martins Pinheiro
  rmontei@purdue.edu

  Service FSM for Scratchpad Frontend read requests (single VC version)
*/

`include "memory/scratchpad/scpad_types_pkg.vh"
`include "memory/scratchpad/scratchpad_if.vh"

module r_fsm #(
    parameter VC_ID = 0   // parameterize which VC this FSM serves
)(
    input  logic clk, n_rst,
    scpad_if.vc_frontend sif   // new modport for one VC
);
    import scpad_types_pkg::*;

    typedef enum logic [2:0] {
        R_IDLE,
        R_MAKE_XBAR_DESC,
        R_REQ_XBAR,
        R_ISSUE_SRAM,
        R_RESP_DONE
    } state_t;

    state_t state, nextstate;

    frontend_req_t cur_req;
    xbar_desc_t cur_xbar_desc;

    sram_r_req_t sram_read_req_reg;
    logic frontend_read_busy;

    always_comb begin : next_state_logic
        nextstate = state;

        case (state)
            R_IDLE: begin
                if (sif.frontend_req.valid)
                    nextstate = R_MAKE_XBAR_DESC;
            end

            R_MAKE_XBAR_DESC: begin
                nextstate = R_REQ_XBAR;
            end

            R_REQ_XBAR: begin
                if (!sif.sram_busy)
                    nextstate = R_ISSUE_SRAM;
            end

            R_ISSUE_SRAM: begin
                if (sif.frontend_sram_read_res.valid)
                    nextstate = R_RESP_DONE;
            end

            R_RESP_DONE: begin
                if (sif.read_complete) begin
                    if (sif.frontend_req.valid)
                        nextstate = R_MAKE_XBAR_DESC;
                    else
                        nextstate = R_IDLE;
                end
            end
        endcase
    end

    always_ff @(posedge clk, negedge n_rst) begin : state_regs
        if (!n_rst) begin
            state              <= R_IDLE;
            cur_req            <= '0;
            cur_xbar_desc      <= '0;
            frontend_read_busy <= 1'b0;
            sram_read_req_reg  <= '0;
        end else begin
            state              <= nextstate;
            frontend_read_busy <= (nextstate != R_IDLE);

            if (nextstate == R_REQ_XBAR && state == R_MAKE_XBAR_DESC) begin
                // Temporary masks
                // Will change this after I figure how to do the comunication with the handler (if there will be one)
                cur_xbar_desc.slot_mask  <= '{default: '0};
                cur_xbar_desc.shift_mask <= '{default: '0};
                cur_xbar_desc.valid_mask <= '{default: 1'b1};
            end

            if (state == R_REQ_XBAR && nextstate == R_ISSUE_SRAM) begin
                sram_read_req_reg.int_id    <= (VC_ID == 0) ? FRONTEND_VC1_REQ : FRONTEND_VC2_REQ;
                sram_read_req_reg.valid     <= 1'b1;
                sram_read_req_reg.xbar_desc <= cur_xbar_desc;
                sram_read_req_reg.scpad_id  <= cur_req.scpad_id;
            end
        end
    end

    always_comb begin : output_logic
        sif.frontend_res.valid    = 1'b0;
        sif.frontend_res.complete = 1'b0;
        sif.frontend_res.rdata    = '0;

        sif.frontend_sram_read_req = '0;
        sif.frontend_ready         = !frontend_read_busy;

        case (state)
            R_ISSUE_SRAM: begin
                if (sram_read_req_reg.valid) begin
                    sif.frontend_sram_read_req = sram_read_req_reg;
                end else begin
                    // On-the-fly issue
                    sif.frontend_sram_read_req.int_id    = (VC_ID == 0) ? FRONTEND_VC1_REQ : FRONTEND_VC2_REQ;
                    sif.frontend_sram_read_req.valid     = 1'b1;
                    sif.frontend_sram_read_req.xbar_desc = cur_xbar_desc;
                    sif.frontend_sram_read_req.scpad_id  = cur_req.scpad_id;
                end
            end

            R_RESP_DONE: begin
                sif.frontend_res.valid    = 1'b1;
                sif.frontend_res.complete = 1'b0; // wait until read_complete external
                sif.frontend_res.rdata    = sif.frontend_sram_read_res.rdata;
            end
        endcase
    end
endmodule
