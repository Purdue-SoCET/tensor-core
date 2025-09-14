`ifndef DRAM_PKG_VH
`define DRAM_PKG_VH

package dram_pkg;

    // WORD SIZE
    parameter WORD_W            = 32;

    // CONFIGS
    parameter CONFIG_BITS = 2;
    
    // ADDRESS PARAMETERS
    parameter RANK_BITS         = 1;
    parameter BANK_GROUP_BITS   = 2;
    parameter BANK_BITS         = 2;
    parameter ROW_BITS          = 15;
    parameter COLUMN_BITS       = 10;
    parameter OFFSET_BITS       = 2;
    parameter IGNORE_BITS       = 1;

    // TIMING PARAMETERS
    parameter tRCD = 10;
    parameter tAL = 1;
    parameter tCL = 10;
    parameter tBURST = 10;
    parameter tCWL = 10;
    parameter tREFI = 10;
    parameter tRP = 10;
    parameter tRFC = 10;
    parameter tRAS = 10;
    parameter tRC = tRAS + tRP;
    parameter tRL = tAL + tCL;        // Read Latency
    parameter tWL = tAL + tCWL;       // Write Latency

    // word_t
    typedef logic [WORD_W-1:0] word_t;

    // configs_t - x4, x8, x16
    typedef enum logic [CONFIG_BITS-1:0] {
        x4  = 2'b00,
        x8  = 2'b01,
        x16 = 2'b10
    } configs_t;

    // command FSM states
    typedef enum logic [4:0] {
        POWER_UP,
        IDLE,
        ACTIVATE,
        ACTIVATING,
        WRITE,
        WRITING,
        PRECHARGE,
        READ,
        READING,
        REFRESH
    } cmd_fsm_t; 

endpackage

`endif // DRAM_PKG_VH