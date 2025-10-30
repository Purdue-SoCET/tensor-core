`timescale 1ps/1ps

`include "scpad_if.sv"
import scpad_pkg::*;

// // Scheduler <=> Backend
//     modport backend_sched (
//         input clk, n_rst, sched_req,
//         output sched_res
//     );

//     // Backend <=> Body
//     modport backend_body (
//         input clk, n_rst, 
//         input  be_stall, be_res, 
//         output be_req
//     );

//     // Backend <=> DRAM
//     modport backend_dram (
//         input clk, n_rst, 
//         output be_dram_req, be_dram_stall,
//         input dram_be_res
//     );

module backend_tb;

    localparam CLK_PERIOD = 10; 
    
    logic  clk = 0;
    logic  n_rst;

    always #(CLK_PERIOD/2) clk = ~clk;

    scpad_if bif(clk, n_rst);

    // module backend #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (
    // scpad_if.backend_sched bshif, 
    // scpad_if.backend_body bscif, 
    // scpad_if.backend_dram bdrif
    // );
    
    backend #(.IDX(0)) DUT (
    .bshif(bif),   // scpad_if.backend_sched
    .bbif (bif),   // scpad_if.backend_body
    .bdrif(bif)    // scpad_if.backend_dram
    );

    initial begin
        n_rst = 0;
        repeat (5) @(posedge clk);
        n_rst = 1;
    end

    // string fname, wavepath; 
    // getenv("WAVEPATH", wavepath);
    // $sformat(fname, "%s/backend_tb.vcd", wavepath); // idk what this is so I'll ignore it for now

    // initial begin 
    //     $dumpfile(fname);
    //     $dumpvars(0);
    // end 

    test PROG (.bif(bif)); 

    initial begin
        #(10_000 * CLK_PERIOD) $fatal(1, "[TB] Timeout");
    end

endmodule

// modport backend_tb (
//         input clk, n_rst, 
//         input sched_res, be_req,
//         input be_dram_stall, be_dram_req,

//         output be_stall, dram_be_stall,
//         output sched_req, be_res, dram_be_res
//     );

program test (scpad_if.backend_tb bif);
    localparam CLK_PERIOD = 10;
    import scpad_pkg::*;

    task reset(); 
        #(CLK_PERIOD * 2);
    endtask

    task schedule_request(
        logic valid,
        logic write,
        logic [SCPAD_ADDR_WIDTH-1:0] spad_addr,
        logic [DRAM_ADDR_WIDTH-1:0] dram_addr,
        logic [MAX_DIM_WIDTH-1:0] num_rows,
        logic [MAX_DIM_WIDTH-1:0] num_cols,
        logic [SCPAD_ID_WIDTH-1:0] scpad_id
   );
   begin
        bif.sched_req[scpad_id].valid = valid;
        bif.sched_req[scpad_id].write = write;
        bif.sched_req[scpad_id].spad_addr = spad_addr;
        bif.sched_req[scpad_id].dram_addr = dram_addr;
        bif.sched_req[scpad_id].num_rows = num_rows;
        bif.sched_req[scpad_id].num_cols = num_cols;
        bif.sched_req[scpad_id].scpad_id = scpad_id;
    end
   endtask

   task dram_results();
    begin
        // Hard-coded 32 * 8 entries for now
        for (int i = 0; i < 257; i++) begin
        // Mirror request → response
        bif.dram_be_res[0].valid = bif.be_dram_req[0].valid;
        bif.dram_be_res[0].write = bif.be_dram_req[0].write;
        bif.dram_be_res[0].id    = bif.be_dram_req[0].id;
        // Return a dummy data pattern (can be 'i' or a hash of addr/id)
        bif.dram_be_res[0].rdata = {16'(i), 16'(i), 16'(i), 16'(i)};
        #(CLK_PERIOD);
        end
        #(CLK_PERIOD/2);
        bif.sched_req[0].valid = 1'b0;
        #(CLK_PERIOD/2);
        #(CLK_PERIOD);
    end
    endtask

    task sram_results();
    begin
        // Hard-coded 32 entries for now
        for (int i = 0; i < 32; i++) begin
        // Mirror request → response
        bif.be_res[0].valid = bif.be_req[0].valid;
        bif.be_res[0].write = ~bif.be_req[0].write;
        // Return a dummy data pattern (can be 'i' or a hash of addr/id)
        bif.be_res[0].rdata = 512'(i);
        #(CLK_PERIOD);
        end
        #(CLK_PERIOD/2);
        bif.sched_req[0].valid = 1'b0;
        #(CLK_PERIOD/2);
        #(CLK_PERIOD);
    end
    endtask

    initial begin
        bif.be_stall[0] = 'b0;
        bif.dram_be_stall[0] = 'b0;
        bif.sched_req[0] = 'b0;
        bif.be_res[0] = 'b0;
        bif.dram_be_res[0] = 'b0;
        bif.be_stall[1] = 'b0;
        bif.dram_be_stall[1] = 'b0;
        bif.sched_req[1] = 'b0;
        bif.be_res[1] = 'b0;
        bif.dram_be_res[1] = 'b0;
        #(CLK_PERIOD * 5);

        // schedule_request(1'b1, 1'b0, 20'd0, 32'd0, 5'd31, 5'd31, 1'b0); // simulate a normal scpad load, dram read -> sram_write
        // dram_results();
        // #(CLK_PERIOD * 2);
        // schedule_request(1'b0, 1'b0, 20'd0, 32'd0, 5'd31, 5'd31, 1'b0); // invalid request after normal request
        // #(CLK_PERIOD*5);
        schedule_request(1'b1, 1'b1, 20'd0, 32'd0, 5'd31, 5'd31, 1'b0); // simulate a normal scpad write, sram read -> dram_write
        sram_results();
        #(CLK_PERIOD * 2); // 32 = num_cols
        // schedule_request(1'b0, 1'b0, 20'd0, 32'd0, 5'd31, 5'd31, 1'b0); // invalid request after normal request
        // #(CLK_PERIOD*5);
        // schedule_request(1'b1, 1'b1, 20'd0, 32'd0, 5'd11, 5'd4, 1'b0); // simulate worst case scpad load, dram read -> sram_write
        // #(CLK_PERIOD);
    end

endprogram