`include "fetch_if.vh"
`include "arbiter_caches_if.vh"

//TODO: In progress with Scheduler.
//Need imemREN and imemAddr from Scheduler

// Parametric cache design
module icache #(
//   parameter WORD_W = 32,      // Word width
//   parameter ITAG_W = 26,      // Instruction cache tag width
//   parameter IBLK_W = 0;
     parameter IIDX_W = 4           // Instruction cache index width
//   parameter IBYT_W = 2        // Instruction cache byte offset width
)(
  input logic CLK, nRST,
  caches_if.icache cif,
  datapath_cache_if.icache dcif
);
  import caches_pkg::*;

  icachef_t icache_format;
  icache_frame [(1 << IIDX_W) - 1:0] icache, nxt_icache;

  typedef enum logic {
      idle = 1'b0,
      miss = 1'b1
  } icache_fsm;

  icache_fsm icache_state, nxt_icache_state;

  // Sequential logic to update icache and state
  always_ff @(posedge CLK or negedge nRST) begin
      if (~nRST) begin
          icache <= '0;
          icache_state <= idle;
      end else begin
          icache <= nxt_icache;
          icache_state <= nxt_icache_state;
      end
  end

  // Combinational logic for handling cache state
  always_comb begin
      icache_format = '0;
      dcif.ihit = '0;
      cif.iREN = '0;
      cif.iaddr = '0;
      nxt_icache = icache;
      nxt_icache_state = icache_state;

      if (icache[icache_format.idx].tag == icache_format.tag && icache[icache_format.idx].valid && dcif.imemREN) begin
          dcif.ihit = '1;
      end else begin
          nxt_icache_state = miss; 
      end

      if (icache_state == miss) begin
          cif.iREN = dcif.imemREN;
          cif.iaddr = dcif.imemaddr;
          if (cif.iwait == 0) begin
              nxt_icache[icache_format.idx] = '{'1, icache_format.tag, cif.iload};
              nxt_icache_state = idle;
          end
      end
  end
endmodule
