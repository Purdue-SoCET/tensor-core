/*
  Eric Villasenor
  evillase@gmail.com

  interface to coordinate caches and
  implement coherence protocol
  TODO: make interface array of 2 and pass array, or something
*/
`ifndef CACHE_CONTROL_IF_VH
`define CACHE_CONTROL_IF_VH

// ram memory types
`include "ram_pkg.vh"
`include "isa_types.vh"

// split this into cache_control_if and ram_if
interface cache_control_if;
  // import types
  import ram_pkg::*;
  import isa_pkg::*;

  // access with cpuid on each processor
  parameter CPUS = 1;
  parameter CPUID = 0;

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

  // icache ports to controller
  modport icache (
    input   iwait, iload,
    output  iREN, iaddr
  );

  // dcache ports to controller
  modport dcache (
    input   dwait, dload,
            ccwait, ccinv, ccsnoopaddr,
    output  dREN, dWEN, daddr, dstore,
            ccwrite, cctrans
  );

endinterface

`endif //CACHE_CONTROL_IF_VH