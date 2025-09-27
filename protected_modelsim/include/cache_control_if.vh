/*
  Eric Villasenor
  evillase@gmail.com

  interface to coordinate caches and
  implement coherence protocol

  Last modified: Spring 2016 by John Skubic

  The cache_control_if has two responsibilities:
  1) Pack the caches_if signals from one or more caches_if
  and send it to the memory controller through a single modport.

  2) Provide the memory controller with signals used to 
  communicate with RAM.

*/
`ifndef CACHE_CONTROL_IF_VH
`define CACHE_CONTROL_IF_VH

// ram memory types
`include "cpu_types_pkg.vh"
`include "caches_if.vh"

interface cache_control_if(
  caches_if cif0,
  caches_if cif1
);
  // import types
  import cpu_types_pkg::*;

  // access with cpuid on each processor
  parameter CPUS = 2;

  // arbitration
  logic   [CPUS-1:0]       iwait, dwait, iREN, dREN, dWEN;
  word_t  [CPUS-1:0]       iload, dload, dstore;
  word_t  [CPUS-1:0]       iaddr, daddr;

  // coherence
  // CPUS = number of cpus parameter passed from system -> cc
  // ccwait         : lets a cache know it needs to block cpu
  // ccinv          : let a cache know it needs to invalidate entry
  // ccwrite        : high if cache is doing a write of addr
  // ccsnoopaddr    : the addr being sent to other cache with either (wb/inv)
  // cctrans        : high if the cache state is transitioning (i.e. I->S, I->M, etc...)
  logic   [CPUS-1:0]      ccwait, ccinv;
  logic   [CPUS-1:0]      ccwrite, cctrans;
  word_t  [CPUS-1:0]      ccsnoopaddr;

  // ram side
  logic                   ramWEN, ramREN;
  ramstate_t              ramstate;
  word_t                  ramaddr, ramstore, ramload;

  /* 
     These interface assignments are to avoid synthesis errors and
     strange simulation behavior.

     For uniprocessors (CPUS == 1), no indexing into the following
     signals is required by the memory controller.  For multiprocessors, 
     all signals are arrays of 2 and must be indexed.

     Note: iREN, dREN, dWEN, dstore, iaddr, daddr, ccwrite, and cctrans
	   cannot be assigned directly through the cache_control_if. 
	   These signals can be written to through a caches_if sent
		 into the cache_control_interface
  */
  always_comb begin
    if (CPUS == 2) begin
      iREN[0] = cif0.iREN;
      dREN[0] = cif0.dREN;
      dWEN[0] = cif0.dWEN;
      dstore[0] = cif0.dstore;
      iaddr[0] = cif0.iaddr;
      daddr[0] = cif0.daddr;
      ccwrite[0] = cif0.ccwrite;
      cctrans[0] = cif0.cctrans;
      iREN[1] = cif1.iREN;
      dREN[1] = cif1.dREN;
      dWEN[1] = cif1.dWEN;
      dstore[1] = cif1.dstore;
      iaddr[1] = cif1.iaddr;
      daddr[1] = cif1.daddr;
      ccwrite[1] = cif1.ccwrite;
      cctrans[1] = cif1.cctrans;

      cif0.iwait = iwait[0];
      cif0.dwait = dwait[0];
      cif0.iload = iload[0];
      cif0.dload = dload[0];
      cif0.ccwait = ccwait[0];
      cif0.ccinv = ccinv[0];
      cif0.ccsnoopaddr = ccsnoopaddr[0];
      cif1.iwait = iwait[1];
      cif1.dwait = dwait[1];
      cif1.iload = iload[1];
      cif1.dload = dload[1];
      cif1.ccwait = ccwait[1];
      cif1.ccinv = ccinv[1];
      cif1.ccsnoopaddr = ccsnoopaddr[1];
    end
    else begin
      iREN = cif0.iREN;
      dREN = cif0.dREN;
      dWEN = cif0.dWEN;
      dstore = cif0.dstore;
      iaddr = cif0.iaddr;
      daddr = cif0.daddr;
      ccwrite = cif0.ccwrite;
      cctrans = cif0.cctrans;

      cif0.iwait = iwait;
      cif0.dwait = dwait;
      cif0.iload = iload;
      cif0.dload = dload;
      cif0.ccwait = ccwait;
      cif0.ccinv = ccinv;
      cif0.ccsnoopaddr = ccsnoopaddr;
    end
  end

  // controller ports to ram and caches
  modport cc (
            // cache inputs
    input   iREN, dREN, dWEN, dstore, iaddr, daddr,
            // ram inputs
            ramload, ramstate,
            // coherence inputs from cache
            ccwrite, cctrans,
            // cache outputs
    output  iwait, dwait, iload, dload,
            // ram outputs
            ramstore, ramaddr, ramWEN, ramREN,
            // coherence outputs to cache
            ccwait, ccinv, ccsnoopaddr
  );

endinterface

`endif //CACHE_CONTROL_IF_VH
