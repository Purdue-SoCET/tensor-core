`ifndef DRAM_COMMAND_IF
`define DRAM_COMMAND_IF

package dram_pack;

// typedef enum logic [4:0] {
//         POWER_UP,
//         PRE_RESET,
//         RESET,
//         NOP,
//         LOAD_MODE_DLL,
//         LOAD_BG0_REG3,
//         LOAD_BG1_REG6,
//         LOAD_BG1_REG5,
//         LOAD_BG1_REG4,
//         LOAD_BG0_REG2,
//         LOAD_BG0_REG1,
//         LOAD_BG0_REG0,
//         ZQ_CL,
//         IDLE,
//         ACTIVATE,
//         WRITE_COMMAND,
//         PRECHARGE,
//         READ_COMMAND
//     } dram_state_t;

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



    //Format for addressing mapping testing
    typedef struct packed {
        logic rank;
        logic blank;
        logic [14:0] row;
        logic [1:0] bank;
        logic bg1;
        logic [6:0] col_1;
        logic bg0;
        logic [2:0] col_0;
        logic [1:0] offset;
    } addr_x4_t;


    //CONFIGURABLE MODE (define by MICRON arch_defines.v)

    parameter int MAX_DM_BITS         = 2;
    parameter int MAX_DBI_BITS        = MAX_DM_BITS; // DM/DBI share pins in current spec.
    parameter int MAX_ADDR_BITS       = 21;
    parameter int MAX_ROW_ADDR_BITS   = 18;
    parameter int MAX_COL_ADDR_BITS   = 14; // Include AP/BLFLY //HAVE CHANGED THIS PARAMETER BY TRI
    parameter int MAX_BANK_BITS       = 2;
    parameter int MAX_RANK_BITS       = 3;
    parameter int MAX_DQ_BITS         = 16;
    parameter int MAX_DQS_BITS        = 2;
    parameter int MAX_CRC_EQUATION    = 8;
    parameter int MAX_CRC_TRANSFERS   = 2;
    parameter int MAX_BANK_GROUP_BITS = 2;
    parameter int MAX_BURST_LEN       = 8;
    parameter int AUTOPRECHARGEADDR   = 10;
    parameter int BLFLYSELECT         = 12;
    parameter int BANK_GROUP_SHIFT    = MAX_ADDR_BITS + MAX_BANK_BITS;
    parameter int BANK_SHIFT          = MAX_ADDR_BITS;
    parameter int MAX_MODEREGS        = 2**(MAX_BANK_BITS+MAX_BANK_GROUP_BITS);
    parameter int MODEREG_BITS        = MAX_ADDR_BITS + MAX_BANK_BITS + MAX_BANK_GROUP_BITS;
    parameter int MAX_MODEREG_SET_BITS = 14;
    parameter int MAX_BANKS_PER_GROUP = 2**(MAX_BANK_BITS);
    parameter int MAX_BANK_GROUPS     = 2**(MAX_BANK_GROUP_BITS);
    parameter int MAX_RANKS           = 2**(MAX_RANK_BITS);
    parameter int RTT_BITS = 16;
    parameter FLY_BY = 1;
    parameter NO_AUTO_PRE = 0;

    // parameter     
    //     POWER_UP_PRG  = 5'b01111,
    //     LOAD_MODE_CMD = 5'b01000,
    //     REFRESH_CMD   = 5'b01001,
    //     PRECHARGE_CMD = 5'b01010,
    //     ACTIVATE_CMD  = 5'b00xxx,
    //     WRITE_CMD     = 5'b01100,
    //     READ_CMD      = 5'b01101,
    //     ZQ_CMD        = 5'b01110,
    //     NOP_CMD       = 5'b01111,
    //     SELF_REF_CMD  = 5'b01001,
    //     DESEL_CMD     = 5'b10000
    // ;
    // {cs, act, ras, cas, we}
    typedef enum logic [4:0] {
        POWER_UP_PRG  = 5'b01111,
        LOAD_MODE_CMD = 5'b01000,
        REFRESH_CMD   = 5'b01001,
        PRECHARGE_CMD = 5'b01010,
        ACTIVATE_CMD  = 5'b00xxx,
        WRITE_CMD     = 5'b01100,
        READ_CMD      = 5'b01101,
        ZQ_CMD        = 5'b01110,
        DESEL_CMD     = 5'b11000
    } cmd_t;

    
    ////////////////// Parameters DDR4 Speed 1600 ///////////////
    parameter BURST_LENGTH  = 8;
    parameter CONFIGURED_DQ_BITS     = 8;
    parameter CONFIGURED_DQS_BITS     = (16 == CONFIGURED_DQ_BITS) ? 2 : 1;
    parameter CONFIGURED_DM_BITS     = (16 == CONFIGURED_DQ_BITS) ? 2 : 1;

    parameter CONFIGURED_RANKS = 1;
    parameter DM_BITS       = 16;
    parameter tRESET        = 80;
    parameter tPWUP         = 80;
    parameter tRESETCKE     = 80;
    parameter tPDc          = 3;
    parameter tXPR          = 217;
    parameter tDLLKc        = 597;
    parameter tZQinitc      = 1024;
    parameter tMOD          = 25;

    


    //Bank timing
    parameter tCCD_S        = 4;
    parameter tCCD_L        = 5;

    //Ranking timing //Command
    parameter tRTRS = 1; //DDR4 Doesnt have RTRS so for now put 1?
    parameter tOST  = 2; // need to check

    //commanding timing
    parameter tCMD = 1; //May dont' need it tho
    //Burst length timing
    parameter tBURST = BURST_LENGTH == 8 ? 4 : 2;

    //ACTIVATION timing
    parameter tRCD   = 12;
    parameter tRRD_L = 4;
    parameter tRRD_S = 4;
    parameter tFAW   = CONFIGURED_DQ_BITS == 16 ? 35 : CONFIGURED_DQ_BITS == 8 ? 25 : 20; //Relate with the page size

    //REFRESH timing
    parameter tRFC = CONFIGURED_DQ_BITS == 16 ? 208 : CONFIGURED_DQ_BITS == 8 ? 128 : 88;  //Relate with the page size

    //WRITING TIMING
    parameter  tAL = 0; //Only for SDRAM but will change later if something is weird
    parameter tCWD = 12; // Put 12 for now due to the micron testing [9, 20]
    parameter tWTR = 12; //pur 12 for now due to micron testing [10, 28] 
    parameter tWR = 12; //pur 12 for now due to micron testing [10, 28] 
    parameter tWL = tAL + tCWD;


    //Reading timing    
    parameter tCAL = 3;
    parameter tCAS = 12;
    parameter tRAS = tRCD + tCAL + tBURST;

    //Prechargning 
    parameter tRP = 10;

    


endpackage: dram_pack
interface dram_command_if();
    import dram_pack::*;
    //Signals from command generator to DRAM
    logic[1:0] CK; // CK[0]==CK_c CK[1]==CK_t
    logic ACT_n;
    logic RAS_n_A16;
    logic CAS_n_A15;
    logic WE_n_A14;
    logic ALERT_n;
    logic PARITY;
    logic RESET_n;
    logic TEN;
    logic CS_n;
    logic CKE;
    logic ODT;
    logic[MAX_RANK_BITS-1:0] C;
    logic[MAX_BANK_GROUP_BITS-1:0] BG;
    logic[MAX_BANK_BITS-1:0] BA;
    logic[13:0] ADDR;
    logic ADDR_17;
    wire[CONFIGURED_DM_BITS-1:0] DM_n;
    wire[CONFIGURED_DQ_BITS-1:0] DQ;
    wire[CONFIGURED_DQS_BITS-1:0] DQS_t;
    wire[CONFIGURED_DQS_BITS-1:0] DQS_c;
    logic ZQ;
    logic PWR;
    logic VREF_CA;
    logic VREF_DQ;


    //Signals command from Scheduler buffer to command generator
    logic [MAX_RANK_BITS - 1 : 0]Ra0, Ra1; //Rank prev and curr
    logic [MAX_BANK_BITS - 1 : 0] BA0, BA1; //bank prev and curr
    logic [MAX_ROW_ADDR_BITS - 1 : 0] R0, R1; //Rol prev and curr
    logic [10 - 1 : 0]COL0, COL1; //Col prev and curr
    logic [MAX_BANK_GROUP_BITS - 1: 0] BG0, BG1;
    logic ramREN_curr, ramWEN_curr, ramREN_ftrt, ramWEN_ftrt;
    
    logic [31:0] data_callback, write_data;
    logic request_done;

    logic wr_en, rd_en;

    //Timing counter REFRESH
    logic REFRESH;
    modport dram_command_sche_buff(
        input Ra0, Ra1, BG0, BG1, BA0, BA1, R0, R1, COL0, COL1, ramREN_curr, ramWEN_curr, ramREN_ftrt, ramWEN_ftrt, REFRESH, write_data,
        output data_callback, request_done, wr_en, rd_en
    );

    modport dram_command_RAM (
        input DM_n, DQ, DQS_t, DQS_c,
        output ACT_n, RAS_n_A16, CAS_n_A15, WE_n_A14, ALERT_n, PARITY, RESET_n, TEN, CS_n, CKE, ODT, C, BG, BA, ADDR, ADDR_17, PWR, VREF_CA, VREF_DQ, ZQ

    );

    

endinterface

`endif
