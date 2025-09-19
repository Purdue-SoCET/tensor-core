`ifndef CACHES_PKG_VH
`define CACHES_PKG_VH


// CHANGE: Size of Data changed from 32bits to 64bits




package caches_pkg;

  // word width and size
  parameter WORD_W    = 32;
  parameter WBYTES    = WORD_W/8;

  // icache format widths
  parameter ITAG_W    = 26;
  parameter IIDX_W    = 4;
  parameter IBLK_W    = 0;
  parameter IBYT_W    = 2;

  // dcache format widths
  parameter DTAG_W    = 26;
  parameter DIDX_W    = 3;
  parameter DBLK_W    = 1;
  parameter DBYT_W    = 2;
  parameter DWAY_ASS  = 2;

// cache address format types
  // icache format type
  typedef struct packed {
    logic [ITAG_W-1:0]  tag;
    
    logic [IIDX_W-1:0]  idx;
    logic [IBYT_W-1:0]  bytoff;
  } icachef_t;

  // dcache format type
  typedef struct packed {
    logic [DTAG_W-1:0]  tag;
    logic [DIDX_W-1:0]  idx;
    logic [DBLK_W-1:0]  blkoff;
    logic [DBYT_W-1:0]  bytoff;
  } dcachef_t;

// word_t
  typedef logic [WORD_W-1:0] word_t;

// memory state
  // ramstate
  typedef enum logic [1:0] {
    FREE,
    BUSY,
    ACCESS,
    ERROR
  } ramstate_t;

// cache frame structs
  //dcache frame
  typedef struct packed {
	logic valid;
	logic dirty;
	logic [DTAG_W - 1:0] tag;
	logic [63:0] [1:0] data;
  } dcache_frame;

  //icache frame  
  typedef struct packed {
	logic valid;
	logic [ITAG_W - 1:0] tag;
	logic [63:0] data;
  } icache_frame;

endpackage
`endif //CPU_TYPES_PKG_VH
