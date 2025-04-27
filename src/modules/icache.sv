module icache (
  input logic CLK, nRST,
  datapath_cache_if.icache dcif,
  caches_if.icache cif,
  arbiter_caches_if.icache acif
);
  import caches_pkg::*;

  icachef_t icache_format;

  assign icache_format = '{dcif.imemaddr[31:6], dcif.imemaddr[5:2], dcif.imemaddr[1:0]};
  icache_frame[15:0] icache, nxt_icache;

  typedef enum logic {
    idle = 1'b0,
    miss = 1'b1
  } icache_fsm;

  icache_fsm icache_state, nxt_icache_state;
  logic freeze, nxt_freeze;

  always_ff @(posedge CLK, negedge nRST) begin
    if (~nRST) begin
      icache <= '0;
      icache_state <= idle;
      freeze <= '0;
    end
    else begin
      icache <= nxt_icache;
      icache_state <= nxt_icache_state;
      freeze <= nxt_freeze;
    end
  end

  assign dcif.imemload = icache[icache_format.idx].data;

  always_comb begin
    dcif.ihit = '0;
    cif.iREN = '0;
    cif.iaddr = '0;
    nxt_icache = icache;
    nxt_icache_state = icache_state;
    acif.irecvhit = '0;
    nxt_freeze = freeze;
    if (dcif.imemREN) begin
      nxt_freeze = 0;
      if (icache[icache_format.idx].tag == icache_format.tag && icache[icache_format.idx].valid) begin
        acif.irecvhit = 1'b1;
        dcif.ihit = '1;
      end
      else begin
        nxt_icache_state = miss;
      end

      if (icache_state == miss) begin
        cif.iREN = '1;
        cif.iaddr = dcif.imemaddr;
        if (cif.iwait == 0 && acif.iload_done) begin
          nxt_icache[icache_format.idx] = '{1, icache_format.tag, cif.iload};
          nxt_icache_state = idle;
        end
      end
    end
    // else if(!dcif.imemREN && icache_state == miss && freeze == 0)begin
    //   cif.iREN = '1;
    //   cif.iaddr = dcif.imemaddr;
    //   if (cif.iwait == 0 && acif.iload_done) begin
    //     nxt_icache[icache_format.idx] = '{1, icache_format.tag, cif.iload};
    //     nxt_icache_state = idle;
    //     nxt_freeze = 1;
    //   end
    // end
    // else if(!dcif.imemREN && icache_state == idle && freeze == 1)begin
    //   if (icache[icache_format.idx].tag == icache_format.tag && icache[icache_format.idx].valid) begin
    //     acif.irecvhit = 1'b1;
    //     dcif.ihit = '1;
    //   end
    //   else begin
    //     nxt_icache_state = miss;
    //   end
    // end
  end
endmodule