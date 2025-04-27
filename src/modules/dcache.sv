`include "caches_pkg.vh"

module dcache (
  input logic CLK, nRST,
  caches_if.dcache cif,
  datapath_cache_if.dcache dcif,
  arbiter_caches_if.dcache acif                               
);

import caches_pkg::*;
// import "DPI-C" function void mem_write(input bit [31:0] address, input bit [31:0] data);
// import "DPI-C" function void mem_save(); 

// Cache configuration parameters
parameter CS = 1024;        // Cache size in bits Currently: 1KB dcache
parameter BS = 2;           // Block size in words
parameter A = 2;            // Associativity
parameter ADDR_BITS = 32;   // Address bits

//Cache Organization parameters
localparam WORD_SIZE = 32;
localparam BYTES_PER_WORD = WORD_SIZE/8;
localparam FRAMES = CS/(BS * WORD_SIZE);          // Currently: 16 frames
localparam NUM_SETS = FRAMES/A;                   // Currently: 8 sets
localparam INDEX_BITS = $clog2(NUM_SETS);         // Currently: 3 bits
localparam BLKOFF_BITS = $clog2(BS);              // Currently: 1 bit
localparam BYTEOFF_BITS = $clog2(BYTES_PER_WORD); // Currently: 2 bits
localparam TAG_BITS = ADDR_BITS - INDEX_BITS - BLKOFF_BITS - BYTEOFF_BITS; // Currently: 26 bits

// Address struct
typedef struct packed {
    logic [TAG_BITS-1:0]     tag;
    logic [INDEX_BITS-1:0]   idx;
    logic                    blkoff;
    logic [BYTEOFF_BITS-1:0] bytoff;
} dcachef_t;

// Internal signals
word_t hit_count, next_hit_count, latched_dmemaddr;
logic miss, finish_flush;
logic [NUM_SETS-1:0] lru, next_lru;
logic [INDEX_BITS-1:0] flush_idx, next_flush_idx;
logic [4:0] flush_counter, next_flush_counter;
dcache_frame [NUM_SETS-1:0][A-1:0] dcache, next_dcache;
dcachef_t dcache_format;

// Address
assign dcache_format.tag = dcif.dmemaddr[ADDR_BITS-1 : ADDR_BITS-TAG_BITS];
assign dcache_format.idx = dcif.dmemaddr[ADDR_BITS-TAG_BITS-1 : BYTEOFF_BITS+BLKOFF_BITS];
assign dcache_format.blkoff = dcif.dmemaddr[BYTEOFF_BITS+BLKOFF_BITS-1];
assign dcache_format.bytoff = dcif.dmemaddr[BYTEOFF_BITS-1:0];

// Sequential logic
always_ff @(posedge CLK, negedge nRST) begin
  if (!nRST) begin
    dcache <= '0;
    flush_idx <= '0;
    lru <= '0;
    flush_counter <= 0;
    latched_dmemaddr <= '0;
  end else begin
    dcache <= next_dcache;
    flush_idx <= next_flush_idx;
    lru <= next_lru;
    flush_counter <= next_flush_counter;
    latched_dmemaddr <= dcif.dmemaddr;
  end
end

// FSM states
typedef enum logic [3:0] {
  IDLE, LOAD0, LOAD1, WB0, WB1, 
  FLUSH, WRITE0, WRITE1, HALT//, COUNT, HALT
} dcache_states;

dcache_states dcache_state, next_dcache_state;

// FSM registers
always_ff @(posedge CLK, negedge nRST) begin
  if (!nRST) begin
    dcache_state <= IDLE;
  end else begin
    dcache_state <= next_dcache_state;
  end
end

// FSM transition logic
always_comb begin
  next_dcache_state = dcache_state;
  case(dcache_state)
    IDLE: begin
      if (dcif.halt) next_dcache_state = FLUSH;
      else if (miss) begin
      // if (miss) begin
        if (dcache[dcache_format.idx][lru[dcache_format.idx]].dirty)
          next_dcache_state = WB0;
        else
          next_dcache_state = LOAD0;
      end
    end
    WB0: if (!cif.dwait && acif.store_done) next_dcache_state = WB1;
    WB1: if (!cif.dwait && acif.store_done) next_dcache_state = LOAD0;
    LOAD0: if (!cif.dwait && acif.load_done) next_dcache_state = LOAD1;
    LOAD1: if (!cif.dwait && acif.load_done) next_dcache_state = IDLE;
    FLUSH: begin
      if (finish_flush) begin
        next_dcache_state = HALT;
      end
      else if ((flush_counter < NUM_SETS && dcache[flush_idx][0].dirty) || 
               (flush_counter >= NUM_SETS && dcache[flush_idx][1].dirty))
        next_dcache_state = WRITE0;
    end
    WRITE0: if (!cif.dwait && acif.store_done) next_dcache_state = WRITE1;
    WRITE1: if (!cif.dwait && acif.store_done) next_dcache_state = FLUSH;
    // COUNT: if (!cif.dwait) next_dcache_state = HALT;
    HALT: next_dcache_state = HALT;
    default: next_dcache_state = IDLE;
  endcase
end

// Cache controller logic
always_comb begin
  dcif.dhit = '0;
  dcif.dmemload = '0;
  cif.dREN = '0;
  cif.dWEN = '0;
  cif.daddr = '0;
  cif.dstore = '0;
  miss = 0;
  finish_flush = 0;
  next_flush_counter = flush_counter;
  next_hit_count = hit_count;
  next_dcache = dcache;
  next_flush_idx = flush_idx;
  next_lru = lru;
  dcif.flushed = '0;
  acif.drecvhit = '0;

  case(dcache_state)
    IDLE: begin
      if (dcif.dmemREN || dcif.dmemWEN) begin
        // Way 0 check
        if (dcache[dcache_format.idx][0].valid && 
            (dcache_format.tag == dcache[dcache_format.idx][0].tag)) begin
          dcif.dhit = 1'b1;
          acif.drecvhit = 1'b1;
          next_hit_count = hit_count + 1;
          next_lru[dcache_format.idx] = 1'b1;
          if (dcif.dmemWEN) begin
            next_dcache[dcache_format.idx][0].data[dcache_format.blkoff] = dcif.dmemstore;
            next_dcache[dcache_format.idx][0].dirty = 1'b1;
          end else begin
            dcif.dmemload = dcache[dcache_format.idx][0].data[dcache_format.blkoff];
          end
        end
        // Way 1 check
        else if (dcache[dcache_format.idx][1].valid && 
                 (dcache_format.tag == dcache[dcache_format.idx][1].tag)) begin
          dcif.dhit = 1'b1;
          acif.drecvhit = 1'b1;
          next_hit_count = hit_count + 1;
          next_lru[dcache_format.idx] = 1'b0;
          if (dcif.dmemWEN) begin
            next_dcache[dcache_format.idx][1].data[dcache_format.blkoff] = dcif.dmemstore;
            next_dcache[dcache_format.idx][1].dirty = 1'b1;
          end else begin
            dcif.dmemload = dcache[dcache_format.idx][1].data[dcache_format.blkoff];
          end
        end
        else begin
          miss = 1'b1;
          next_hit_count = hit_count - 1;
        end
      end
    end

    WB0, WB1: begin
      cif.dWEN = 1'b1;
      cif.daddr = {dcache[dcache_format.idx][lru[dcache_format.idx]].tag,
                   dcache_format.idx,
                   {(BLKOFF_BITS+BYTEOFF_BITS){1'b0}}} + 
                  ((dcache_state == WB1) ? (1 << BYTEOFF_BITS) : 0);
      cif.dstore = dcache[dcache_format.idx][lru[dcache_format.idx]].data[dcache_state == WB1];
      // mem_write(cif.daddr, cif.dstore);
      // mem_save();
      if (!cif.dwait && dcache_state == WB1) begin
        next_dcache[dcache_format.idx][lru[dcache_format.idx]].dirty = 1'b0;
        next_dcache[dcache_format.idx][lru[dcache_format.idx]].valid = 1'b0;
      end
    end

    LOAD0, LOAD1: begin
      logic way_sel;
      cif.dREN = 1'b1;
      cif.daddr = {dcache_format.tag, dcache_format.idx, {(BLKOFF_BITS+BYTEOFF_BITS){1'b0}}} +
                  ((dcache_state == LOAD1) ? (1 << BYTEOFF_BITS) : 0);
      
      way_sel = lru[dcache_format.idx];
      if (!dcache[dcache_format.idx][0].valid) way_sel = 0;
      else if (!dcache[dcache_format.idx][1].valid) way_sel = 1;

      if (!cif.dwait) begin
        next_dcache[dcache_format.idx][way_sel].data[dcache_state == LOAD1] = cif.dload;
        if (dcache_state == LOAD1) begin
          next_dcache[dcache_format.idx][way_sel].tag = dcache_format.tag;
          next_dcache[dcache_format.idx][way_sel].valid = 1'b1;
          next_dcache[dcache_format.idx][way_sel].dirty = 1'b0;
        end
      end
    end

    FLUSH: begin
      if (flush_counter < NUM_SETS*2) begin
        next_flush_idx = flush_counter[INDEX_BITS-1:0];
        if (flush_counter >= NUM_SETS) begin
          if (!dcache[next_flush_idx][1].dirty) next_flush_counter = flush_counter + 1;
        end else begin
          if (!dcache[next_flush_idx][0].dirty) next_flush_counter = flush_counter + 1;
        end
      end else begin
        finish_flush = 1'b1;
      end
    end

    WRITE0, WRITE1: begin
      logic way_sel;
      cif.dWEN = 1'b1;
      way_sel = (flush_counter >= NUM_SETS);
      cif.daddr = {dcache[flush_idx][way_sel].tag, flush_idx, 
                  {(BLKOFF_BITS+BYTEOFF_BITS){1'b0}}} +
                  ((dcache_state == WRITE1) ? (1 << BYTEOFF_BITS) : 0);
      cif.dstore = dcache[flush_idx][way_sel].data[dcache_state == WRITE1];
      // mem_write(cif.daddr, cif.dstore);
      // mem_save();
      if (!cif.dwait && dcache_state == WRITE1) begin
        next_dcache[flush_idx][way_sel].dirty = 1'b0;
        next_dcache[flush_idx][way_sel].valid = 1'b0;
        next_flush_counter = flush_counter + 1;
      end
    end

    // COUNT: begin
    //   cif.dWEN = 1'b1;
    //   cif.daddr = 32'h3100;
    //   cif.dstore = hit_count;
    // end

    HALT: begin
      dcif.flushed = 1'b1;
    end
  endcase
end

endmodule