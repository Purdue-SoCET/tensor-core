module gsau_control_unit #(
    parameter VEGGIEREGS = 256,
    parameter FIFOSIZE = 32*3*8
) (
    CLK, nRST
);

    /*
    input               	rstn,               // Active low reset
                            	clk,                // Clock
                            	wr_en, 				// Write enable
                            	rd_en, 				// Read enable
        input      [DDATAWIDTH-1:0] din, 				// Data written into FIFO
        output logic [DDATAWIDTH-1:0] dout, 				// Data read from FIFO
        output              	empty, 				// FIFO is empty when high
                            	full 				// FIFO is full when high
    */

    logic wr_en, rd_en,
    logic [$clog2(VEGGIEREGS)-1:0] vdst_in, vdst_out;
    

    sync_fifo gsau_queue ()
    
endmodule