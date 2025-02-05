`include "types_pkg.vh"
`include "scratchpad_bank_if.vh"

module scratchpad_bank (
    input logic CLK, nRST,
    scratchpad_bank_if.sp spif
);

    logic [3:0][3:0][15:0] n_mats, mats;

    always_ff @(posedge CLK, negedge nRST) begin
        if (nRST == 1'b0) begin
            mats <= '0
        end
        else begin
            mats <= n_mats;
        end
    end

    always_comb begin
        n_mats = mats;
        if (spif.wen) begin
            n_mats[spif.w_mat_sel][spif.w_row_sel] = spif.wdat;
        end
    end

    assign spif.rdat = mats[spif.r_mat_sel][spif.r_row_sel];

    
endmodule