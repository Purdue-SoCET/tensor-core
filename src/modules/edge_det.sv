`include "edge_det_if.vh"

module edge_det #(parameter TRIG_RISE = 1, TRIG_FALL = 0, RST_VAL = 0) (
    input logic clk, n_rst,
    edge_det_if.edge_mod myedge
);

    logic sync_out1, q;

    always_ff @ (posedge clk, negedge n_rst) begin
        if (!n_rst)
            sync_out1 <= RST_VAL;    // reset value is independent of the rest
        else
            sync_out1 <= myedge.async_in;
    end

    always_ff @ (posedge clk, negedge n_rst) begin
        if (!n_rst)
            myedge.sync_out <= RST_VAL;
        else
            myedge.sync_out <= sync_out1;
    end

    always_ff @ (posedge clk, negedge n_rst) begin
        if (!n_rst)
            q <= RST_VAL;
        else
            q <= myedge.sync_out;
    end

    assign myedge.edge_flag = (TRIG_RISE && (~sync_out1 & myedge.sync_out)) || (TRIG_FALL && (sync_out1 & ~myedge.sync_out)) ? 1'b1 : 1'b0;

endmodule