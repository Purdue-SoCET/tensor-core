/*  Duc Pham Minh - dphammin@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`include "xbar_params.svh"
`include "xbar_if.sv"
`include "compare_switch.sv"

module batcher_xbar #(
    parameter int SIZE = 32, 
    parameter int DWIDTH = 16, 
    localparam int TAGWIDTH = $clog2(SIZE),
    localparam int STAGES = (TAGWIDTH * (TAGWIDTH + 1)) / 2
) (xbar_if.xbar xif);

    // Stages
    logic [TAGWIDTH-1:0] shift_q [1:STAGES][SIZE];
    logic [TAGWIDTH-1:0] shift_d [1:STAGES][SIZE];
    logic [DWIDTH-1:0] data_q [1:STAGES][SIZE];
    logic [DWIDTH-1:0] data_d [1:STAGES][SIZE];

    // Propagate
    always_ff @(posedge xif.clk, negedge xif.n_rst) begin 
        if (!xif.n_rst) begin
            for (int s = 1; s <= STAGES; s++) begin
                for (int i = 0; i < SIZE; i++) begin
                    shift_q[s][i] <= '0;
                    data_q[s][i] <= '0;
                end
            end
        end else begin
            for (int s = 1; s <= STAGES; s++) begin
                for (int i = 0; i < SIZE; i++) begin
                    shift_q[s][i] <= shift_d[s][i];
                    data_q[s][i] <= data_d[s][i];
                end
            end
        end
    end

    always_comb begin 
        for (int s = 1; s <= STAGES; s++) begin 
            for (int i = 0; i < SIZE; i++) begin
                if (s == 1) begin // input grab
                    shift_d[s][i] = xif.in[i].shift;
                    data_d[s][i] = xif.in[i].din; 
                end else begin // propagate
                    shift_d[s][i] = shift_q[s-1][i];
                    data_d[s][i] = data_q[s-1][i];
                end
            end
        end
    end

    generate
        genvar p, q, i;

        for (p = 1; p <= TAGWIDTH; p++) begin
            localparam int k = (1 << p);
            for (q = p; q >= 1; q--) begin
                localparam int j = (1 << (q - 1));
                localparam int stage = ((p-1)*p)/2 + (p - q + 1); // gets current stage

                for (i = 0; i < SIZE; i++) begin
                    localparam int ixj = (i ^ j);

                    if (ixj > i) begin
                        logic [DWIDTH-1:0] upper_din [2];
                        logic [TAGWIDTH-1:0] upper_shift [2];

                        if (stage == 1) begin
                            compare_switch #(.SIZE(SIZE)) u_less_comp (
                                .din({xif.in[i].din, xif.in[ixj].din}), .tin({xif.in[i].shift, xif.in[ixj].shift}), 
                                .cntrl(xif.in[i].din <= xif.in[ixj].din), 
                                .dout({upper_din[0], upper_din[1]}), .tout({upper_shift[0], upper_shift[1]})
                            ); 
                        end else begin
                            compare_switch #(.SIZE(SIZE)) u_less_comp (
                                .din({data_q[stage-1][i], data_q[stage-1][ixj]}), .tin({shift_q[stage-1][i], shift_q[stage-1][ixj]}), 
                                .cntrl(data_q[stage-1][i] <= data_q[stage-1][ixj]), 
                                .dout({upper_din[0], upper_din[1]}), .tout({upper_shift[0], upper_shift[1]})
                            ); 
                        end

                        compare_switch #(.SIZE(SIZE)) u_asc_comp (
                            .din({upper_din[0], upper_din[1]}), .tin({upper_shift[0], upper_shift[1]}),
                            .cntrl(((i & k) == 0)), 
                            .dout({data_d[stage][i], data_d[stage][ixj]}), .tout({shift_d[stage][i], shift_d[stage][ixj]})); 

                    end
                end
            end
        end
    endgenerate


    // Output Stages
    always_comb begin
        for (int i = 0; i < SIZE; i++) begin
            xif.out[i] = data_q[STAGES][i];
        end
    end
 

endmodule