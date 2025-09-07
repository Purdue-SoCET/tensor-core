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
    // parameter tRCD = ;
    // parameter tAL = ;
    // parameter tCL = ;
    // parameter tBURST = ;
    // parameter tRCD = ;
    // parameter tCWL = ;
    // parameter tREFI = ;
    // parameter tRP = ;
    // parameter tRFC = ;

    // word_t
    typedef logic [WORD_W-1:0] word_t;

    // configs_t - x4, x8, x16
    typedef enum logic [CONFIG_BITS-1:0] {
        x4  = 2'b00,
        x8  = 2'b01,
        x16 = 2'b10
    } configs_t; 

endpackage

`endif // DRAM_PKG_VH