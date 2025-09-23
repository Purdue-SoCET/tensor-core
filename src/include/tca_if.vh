/*
  Saandiya KPS Mohan
  mohan76@purdue.edu

  TCA Interface V1
*/

`ifndef TCA_IF_VH
`define TCA_IF_VH

interface tca_if;
  import scpad_types_pkg::*;   // reuse basic typedefs (data, addr, etc.)
  import sys_arr_pkg::*;       // systolic-specific typedefs
  import types_pkg::*;

  ////////////////////////////////////////////////////////////////////////////
  ////////////////////////////// Types ///////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////////

  typedef enum logic [1:0] {
      TCA_IDLE   = 2'b00,
      TCA_LOAD   = 2'b01,   // loading inputs
      TCA_COMPUTE= 2'b10,   // systolic array running
      TCA_WRITE  = 2'b11    // writing results back to scratchpad
  } tca_state_t;
  
  typedef struct packed {
    logic valid;                                // request is valid
    logic [SCPAD_ADDR_WIDTH-1:0] base_addr;     // base row/col address of this tile
    logic [15:0] R, S, C, K;                    // kernel dims + channel + output channel
    logic row_major;                            // 0 = col streaming, 1 = row streaming
    logic [SCPAD_ID_WIDTH-1:0] ifmap_id;        // scratchpad bank holding input activations
    logic [SCPAD_ID_WIDTH-1:0] psum_id;         // scratchpad bank for partial sums/output
} tca_req_t;

  typedef struct packed {
      logic valid;      // response is valid this cycle
      logic complete;   // 1 = operation finished, results written back
      logic error;      // 1 = error occurred (bad addr, scratchpad busy, etc.)
  } tca_res_t;

  // Requests to systolic array
  typedef struct packed {
      logic valid;          // request is valid this cycle
      logic load_ifmap;     // load input feature map (rows typically)
    //TODO: do we need this
      logic load_psum;      // load partial sums (if continuing accumulation)
      logic start;          // once all data is loaded, signal SA to start compute
      systolic_data din;    // actual data word being streamed into the SA
  } tca_sa_req_t;

  typedef struct packed {
      logic valid;          // response is valid this cycle
      logic done;           // computation is finished
      systolic_data dout;   // output data word (result from SA)
  } tca_sa_res_t;

  ////////////////////////////////////////////////////////////////////////////
  /////////////////////////////// Signals ////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////////

  // From Scheduler
  tca_req_t  scheduler_tca_req;
  tca_res_t  tca_scheduler_res;

  // To/from Scratchpad
  scpad_if.frontend_req_t  tca_frontend_req;
  scpad_if.frontend_res_t  frontend_tca_res;

  // To/from Systolic Array
  tca_sa_req_t sa_req;
  tca_sa_res_t sa_res;

  ////////////////////////////////////////////////////////////////////////////
  ////////////////////////////// Modports ////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////////

  //TODO: need to check

    // Scheduler: @JayShah
    // Scratchpad: @Akshath
    // Systolic: @Vinay, @Meixuan

  modport top ( //@JayShah
      input  scheduler_tca_req,
      output tca_scheduler_res
  );

  modport scpad ( //@Akshath
      output tca_frontend_req,
      input  frontend_tca_res
  );

  modport systolic ( //@Vinay, @Meixuan
      output sa_req,
      input  sa_res
  );

endinterface
`endif