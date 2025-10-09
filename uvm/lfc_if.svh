`ifndef ADDER_IF_SVH
`define ADDER_IF_SVH

interface lfc_if #(parameter NUM_BANKS = 4, parameter UUID_SIZE = 4) (input logic clk);
  
  // Reset Input for both CPU and RAM
  logic n_rst;

  // CPU Inputs
  logic mem_in;
  logic [31:0] mem_in_addr;
  logic mem_in_rw_mode; // 0 = read, 1 = write
  logic [31:0] mem_in_store_value;
  logic dp_in_halt;

  // CPU Outputs
  logic [3:0] mem_out_uuid;
  logic stall;
  logic hit;
  logic [31:0] hit_load;
  logic [NUM_BANKS-1:0] block_status;
  logic [NUM_BANKS-1:0][UUID_SIZE-1:0] uuid_block;
  logic dp_out_flushed;

  // RAM Inputs
  logic [NUM_BANKS-1:0][31:0] ram_mem_data;
  logic [NUM_BANKS-1:0] ram_mem_complete;

  // RAM Outputs
  logic [NUM_BANKS-1:0] ram_mem_REN;
  logic [NUM_BANKS-1:0] ram_mem_WEN;
  logic [NUM_BANKS-1:0][31:0] ram_mem_addr;
  logic [NUM_BANKS-1:0][31:0] ram_mem_store;

  modport cpu
  (
    input n_rst, mem_in, mem_in_addr, mem_in_rw_mode, mem_in_store_value, dp_in_halt,
    output mem_out_uuid, stall, hit, hit_load, block_status, uuid_block, dp_out_flushed
  );

  modport ram
  (
    input n_rst, ram_mem_data, ram_mem_complete,
    output ram_mem_REN, ram_mem_WEN, ram_mem_addr, ram_mem_store
  );
endinterface

`endif