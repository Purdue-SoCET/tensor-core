`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"
`include "addr_map_if.vh"
`include "dram_read_req_queue_if.vh"

//         modport backend_sched (
//             input  sched_req_valid, sched_req,
//             output sched_req_ready, sched_rsp_valid, sched_rsp
//         );

//         modport backend (
//             // → SCPAD0
//             output be0_rd_req_valid, be0_rd_req, be0_rd_res_ready,
//             input  be0_rd_req_ready, be0_rd_res_valid, be0_rd_res,
//             output be0_wr_req_valid, be0_wr_req, be0_wr_res_ready,
//             input  be0_wr_req_ready, be0_wr_res_valid, be0_wr_res,
//             // → SCPAD1
//             output be1_rd_req_valid, be1_rd_req, be1_rd_res_ready,
//             input  be1_rd_req_ready, be1_rd_res_valid, be1_rd_res,
//             output be1_wr_req_valid, be1_wr_req, be1_wr_res_ready,
//             input  be1_wr_req_ready, be1_wr_res_valid, be1_wr_res
//         );


//        modport backend_dram_ports (
//         output be_dram_req_valid, be_dram_req,
//         input  be_dram_req_ready,
//         input  dram_be_res_valid, dram_be_res,
//         output dram_be_res_ready
//         );

// modport backend_addr (
//         input  row_or_col,
//         input  spad_addr,
//         input  num_rows, num_cols, row_id, col_id,

//         output xbar_desc
//     );
<<<<<<< Updated upstream

// modport backend (
//         input sram_busy,

//         input scheduler_backend_req,
//         output backend_scheduler_res, 

//         input  backend_sram_r_banks_res, backend_sram_w_banks_res,
//         output backend_sram_r_banks_req, backend_sram_w_banks_req, 

//         input  dram_backend_res,
//         output backend_dram_req,
//     );

// typedef struct packed { 
//         logic valid; 
//         logic write; 
//         logic [SCPAD_ADDR_WIDTH-1:0] addr; // always the BASE row, basically an identifier
//         logic [MAX_DIM_WIDTH-1:0] num_rows, num_cols; // purely for sysarray.ld -> loading an entire tile/kernel into the SA
//         logic [SCPAD_ID_WIDTH-1:0] scpad_id; // which scpad to load to
//     } scheduler_req_t scheduler_backend_req; 

// typedef struct packed { 
//         logic valid; 
//         logic complete; 
//     } scheduler_res_t backend_scheduler_res;

// typedef struct packed {
//         sram_interaction_id_t int_id; 
//         logic valid;
//         scpad_data rdata;
//     } sram_r_res_t backend_sram_r_banks_res;

// typedef struct packed {
//         sram_interaction_id_t int_id; 
//         logic valid;
//     } sram_w_res_t backend_sram_w_banks_res;

// typedef struct packed {
//         sram_interaction_id_t int_id; 
//         logic valid;
//         xbar_desc_t xbar_desc; 
//         logic [SCPAD_ID_WIDTH-1:0] scpad_id; // which scpad to read from
//     } sram_r_req_t backend_sram_r_banks_req;

// typedef struct packed {
//         sram_interaction_id_t int_id; 
//         logic valid;
//         xbar_desc_t xbar_desc; 
//         scpad_data wdata;
//         logic [SCPAD_ID_WIDTH-1:0] scpad_id; // which scpad to write to
//     } sram_w_req_t backend_sram_w_banks_req;
=======
>>>>>>> Stashed changes

module backend (
    input logic clk, n_rst, scratchpad_if.backend_sched be_sche,
    scratchpad_if.backend bif, scratchpad_if.backend_dram_ports be_dram
);

logic [DRAM_ID_WIDTH-1:0] uuid, nxt_uuid;

always_ff @(posedge clk, negedge n_rst ) begin
    if(!n_rst) begin
        uuid <= '0;
    end else begin
        uuid <= nxt_uuid; 
        // uuid + 1 whenever the current uuid
        // gets placed into its appropriate latches.
        // things should be placed every cycle except for when hazards occur
    end
    
end

addr_map_if baddr();
dram_read_req_queue_if be_dr_rd_req_q();


addr_map swizzle_metadata(baddr);
assign baddr.row_or_col = be_sche.sched_req.row_or_col;
assign baddr.spad_addr = be_sche.sched_req.spad_addr;
assign baddr.num_rows = be_sche.sched_req.num_rows;
assign baddr.num_cols = be_sche.sched_req.num_cols;
assign baddr.row_id = uuid  // no matter which orientation we are in the uuid keeps track         
assign baddr.col_id = uuid  // of the row_id or col_id, since it only counts up when moving on the next row/col.

dram_read_request_queue dr_rd_req_q(clk, n_rst, be_dr_rd_req_q);
assign be_dr_rd_req_q.dram_addr = be_sche.sched_req.dram_addr;
assign be_dr_rd_req_q.id = uuid;
assign be_dr_rd_req_q.num_bytes = be_sche.sched_req.num_bytes;
assign be_dr_rd_req_q.sched_write = be_sche.sched_req.write;
assign be_dr_rd_req_q.be_dram_req_ready = be_dram.be_dram_req_ready;



endmodule