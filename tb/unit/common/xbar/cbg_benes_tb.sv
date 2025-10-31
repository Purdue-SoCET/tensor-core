module cbg_benes_tb;
    localparam int PERIOD = 10;
    localparam int SIZE=32;
    localparam int DWIDTH=16;
    localparam int TAGWIDTH=$clog2(SIZE);
    localparam int STAGES = (2 * TAGWIDTH) - 1;
    localparam int BITWIDTH = STAGES * (SIZE >> 1);

    logic clk, n_rst;
    logic [BITWIDTH-1:0] ctrl;
    logic [TAGWIDTH-1:0] perm [SIZE-1:0];
    logic [BITWIDTH-1:0] exp_ctrl;

    always #(PERIOD/2) clk = ~clk;
    cbg_benes #(.SIZE(SIZE)) DUT (.perm(perm), .ctrl(ctrl));


    initial begin
        perm = {5'd14, 5'd22, 5'd25, 5'd11, 5'd21, 5'd6, 5'd15, 5'd5, 5'd30, 5'd23, 5'd18, 5'd28, 5'd19, 5'd17, 5'd31, 5'd12, 5'd26, 5'd16, 5'd13, 5'd3, 5'd9, 5'd8, 5'd0, 5'd1, 5'd10, 5'd20, 5'd7, 5'd4, 5'd29, 5'd2, 5'd24, 5'd27};
        // perm = {5'd27, 5'd5'd24, 5'd2, 5'd29, 5'd4, 5'd7, 5'd20, 5'd10, 5'd1, 5'd0, 5'd8, 5'd9, 5'd3, 5'd13, 5'd16, 5'd26,
        //                 5'd12, 5'd31, 5'd17, 5'd19, 5'd28, 5'd18, 5'd23, 5'd30, 5'd5, 5'd15, 5'd6, 5'd21, 5'd11, 5'd25, 5'd22, 5'd14};
        exp_ctrl = 144'b111000110101110001100100110011100111001110000000111100000001101100101011001100000000000000000000001000011001000001110110011110001011111001001100;
        
        #(PERIOD)
        #(PERIOD)
        for (int i = 0; i < BITWIDTH; i++) begin
            if(exp_ctrl[i] != ctrl[i]) begin
                $display("WRONG bit %d not equal. Expected: %d, output: %d", i, exp_ctrl[i], ctrl[i]);
            end
            else begin
                $display("CHECK bit %d was equal. Expected: %d, output: %d", i, exp_ctrl[i], ctrl[i]);
            end
        end
        $finish();
    end

    
endmodule