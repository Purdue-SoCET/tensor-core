`timescale 1ns / 1ns

module benes_xbar_tb;
    localparam int PERIOD = 10;
    localparam int SIZE = 32;
    localparam int DWIDTH = 16;
    localparam int TAGWIDTH = $clog2(SIZE);
    localparam int STAGES = (2 * TAGWIDTH) - 1;
    localparam int BITWIDTH = STAGES * (SIZE >> 1);

    logic clk, n_rst;
    logic [BITWIDTH-1:0] control_bit ;

    initial clk = 1'b0;
    always  #5 clk = ~clk;
    
    xbar_if #(.SIZE(SIZE), .DWIDTH(DWIDTH)) xif (.clk(clk), .n_rst(n_rst));
    benes #(.SIZE(SIZE), .DWIDTH(DWIDTH)) DUT (xif, control_bit);

    integer i;
    logic [15:0] val;
    logic [DWIDTH-1:0] exp_out [SIZE-1:0];

    // REQUIRED FOR TESTING WITH CBG

    // typedef logic [DWIDTH-1:0] vec_t [SIZE];
    // vec_t in, exp_out;

    // function automatic void make_vec(output logic [TAGW-1:0] exp_out [SIZE-1:0]);
    //     logic [DWIDTH-1:0] idx [SIZE-1:0];
    //     logic [DWIDTH-1:0] tmp;
    //     integer i, j, tmp;

    //     for (i = 0; i < 32; i++)
    //     idx[i] = i;

    //     for (i = 31; i > 0; i--) begin
    //         j = $urandom_range(0, i); // random index to swap
    //         tmp = idx[i];
    //         idx[i] = idx[j];
    //         idx[j] = tmp;
    //     end

    //     for (i = 0; i < 32; i++)
    //         exp_out[i] = idx[i];

    // endfunction

initial begin
    n_rst = 0;

    #(PERIOD);

    n_rst = 1;
    val = 16'd0;

    for (i = 0; i < 32; i = i + 1) begin
        xif.in[i] = val;
        val = val + 16'd1;
    end
    exp_out = {16'd27, 16'd24, 16'd2, 16'd29, 16'd4, 16'd7, 16'd20, 16'd10, 16'd1, 16'd0, 16'd8, 16'd9, 16'd3, 16'd13, 16'd16, 16'd26,
                    16'd12, 16'd31, 16'd17, 16'd19, 16'd28, 16'd18, 16'd23, 16'd30, 16'd5, 16'd15, 16'd6, 16'd21, 16'd11, 16'd25, 16'd22, 16'd14};
    
    control_bit = 144'b111000110101110001100100110011100111001110000000111100000001101100101011001100000000000000000000001000011001000001110110011110001011111001001100;  
    
    repeat (10) #(PERIOD);
    
    for (i = 0; i < 32; i = i + 1) begin
        if(xif.out[i] != exp_out[(SIZE-1 - i)]) begin
            $display("wrong output for %d", i);
        end
        // $display("output %d: %d", i, xif.out[i]);
    end
    $finish;
end

endmodule