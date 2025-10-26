/*  Duc Pham Minh - dphammin@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`include "xbar_params.svh"
`include "xbar_if.sv"

import xbar_pkg::*;

module batcher #(
    parameter int SIZE = 32,
    parameter int DWIDTH = 16, 
    parameter batcher_mask_t REGISTER_MASK = 14'b11111111111111, 

    localparam int TAGWIDTH = $clog2(SIZE),
    localparam int STAGES = (TAGWIDTH * (TAGWIDTH + 1)) / 2
) (xbar_if.xbar xif);

    logic [TAGWIDTH-1:0] shift_in [1:STAGES][SIZE];
    logic [DWIDTH-1:0] data_in  [1:STAGES][SIZE];
    logic [TAGWIDTH-1:0] shift_out [1:STAGES][SIZE];
    logic [DWIDTH-1:0] data_out  [1:STAGES][SIZE];

	logic [TAGWIDTH-1:0] shift_latch [1:STAGES-1][SIZE]; 
	logic [DWIDTH-1:0] data_latch [1:STAGES-1][SIZE]; 

    // Pipeline registers
    always_ff @(posedge xif.clk, negedge xif.n_rst) begin
        if (!xif.n_rst) begin
            for (int s = 1; s <= STAGES-1; s++) begin
                for (int i = 0; i < SIZE; i++) begin
                    shift_latch[s][i] <= '0;
                    data_latch[s][i] <= '0;
                end
            end
        end else begin
            for (int s = 1; s <= STAGES-1; s++) begin
                if (REGISTER_MASK[s-1]) begin
                    for (int i = 0; i < SIZE; i++) begin
                        shift_latch[s][i] <= shift_out[s][i];
                        data_latch[s][i] <= data_out[s][i];
                    end
                end
            end
        end
    end

    generate
        genvar ii, s;

        for (s = 1; s < STAGES; s++) begin
            for (ii = 0; ii < SIZE; ii++) begin 
                assign data_in [s][ii] = REGISTER_MASK[s-1] ? data_latch[s-1][ii] : data_out[s-1][ii];
                assign shift_in[s][ii] = REGISTER_MASK[s-1] ? shift_latch[s-1][ii] : shift_out[s-1][ii];
            end
        end
    endgenerate

    generate
        genvar p, q, i;
        for (p = 1; p <= TAGWIDTH; p++) begin 
            localparam int k = (1 << p);
            for (q = p; q >= 1; q--) begin 
                localparam int j = (1 << (q - 1));
                localparam int stage = ((p - 1) * p) / 2 + (p - q + 1);

                for (i = 0; i < SIZE; i++) begin 
                    localparam int ixj = (i ^ j);

                    if (ixj > i) begin 
                        // Intermediate wires between the two compares at this node
                        logic [DWIDTH-1:0] upper_din [2];
                        logic [TAGWIDTH-1:0] upper_shift [2];

                        // First compare: order by data value (from inputs or prior stage)
                        if (stage == 1) begin 
                            compare_switch #(.DATA_W(DWIDTH), .TAG_W(TAGWIDTH)) u_less_comp (
                                .din('{xif.in[i].din, xif.in[ixj].din}),
                                .tin('{xif.in[i].shift,xif.in[ixj].shift}),
                                .cntrl (xif.in[i].din <= xif.in[ixj].din),
                                .dout(upper_din),
                                .tout(upper_shift)
                            );
                        end else begin 
                            compare_switch #(.DATA_W(DWIDTH), .TAG_W(TAGWIDTH)) u_less_comp (
                                .din('{data_in[stage-1][i],data_in[stage-1][ixj]}),
                                .tin('{shift_in[stage-1][i],shift_in[stage-1][ixj]}),
                                .cntrl (data_in [stage-1][i] <=data_in [stage-1][ixj]),
                                .dout(upper_din),
                                .tout(upper_shift)
                            );
                        end

                        compare_switch #(.DATA_W(DWIDTH), .TAG_W(TAGWIDTH)) u_asc_comp (
                            .din('{upper_din[0], upper_din[1]}),
                            .tin('{upper_shift[0], upper_shift[1]}),
                            .cntrl (((i & k) == 0)),
                            .dout('{data_out [stage][i], data_out [stage][ixj]}),
                            .tout('{shift_out[stage][i], shift_out[stage][ixj]})
                        );
                    end
                end
            end
        end
    endgenerate

    always_comb begin
        for (int i = 0; i < SIZE; i++) begin
            xif.out[i] = data_out[STAGES][i];
        end
    end

endmodule
