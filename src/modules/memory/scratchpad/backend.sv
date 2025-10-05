`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

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

module backend (
    input logic clk, n_rst,
    scpad_if.backend bif
); 

endmodule