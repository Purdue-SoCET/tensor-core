`include "dram_pkg.vh"
`include "address_mapper_if.vh"
`include "timing_signals_if.vh"
`include "command_fsm_if.vh"
`include "row_open_if.vh"
`include "init_state_if.vh"

module control_unit (
    input logic clk, nRST,
    address_mapper_if amif,
    init_state_if initif,
    row_open_if polif,
    command_fsm_if cfsmif,
    timing_signals_if timif,
    control_unit_if cuif
);
    init_state              init_state      (.CLK(clk), .nRST(nRST), .it(initif));
    addr_mapper             addr_mapper     (.amif(amif.addr_mapper));
    row_open #(.DEPTH(16))  row_open        (.CLK(clk), .nRST(nRST), .pol_if(polif.row_open), .amif(amif.row_open),
                                            .timif(timif.row_open));
    command_FSM             command_fsm     (.CLK(clk), .nRST(nRST), .mycmd(cfsmif.cmd_fsm), .polif(polif.cmd_fsm),
                                            .timif(timif.cmd_fsm));
    timing_control          timing_control  (.clk(clk), .nRST(nRST), .timif(timif.timing_ctrl), 
                                            .cfsmif(cfsmif.timing_ctrl));

    
    // Registering init_done signal because it takes 1 cycle to update states (go from INIT -> CMD_FSM)
    // after init_done goes high
    logic init_done;
    always_ff @(posedge clk, negedge nRST) begin : INIT_DONE_REG
        if (!nRST) begin
            init_done <= 1'b0;
        end
        else begin
            init_done <= initif.init_valid;
        end 
    end
    
    always_comb begin : SIGNAL_CONNECTIONS
        // Assign state signals
        cuif.state  = (init_done == 1'b0) ? initif.init_state   : cfsmif.cmd_state;
        cuif.nstate = (init_done == 1'b0) ? initif.n_init_state : cfsmif.ncmd_state;
        initif.init = cfsmif.init_req;
        
        // Assign address mapping signals
        cuif.rank = amif.rank;
        cuif.BG = amif.BG;
        cuif.bank = amif.bank;
        cuif.row = amif.row;
        cuif.col = amif.col;
        cuif.offset = amif.offset;

        // Assign data transfer signals
        cuif.wr_en = timif.wr_en;
        cuif.rd_en = timif.rd_en;
        cuif.clear = timif.clear;

        // Assign cmd_fsm signals
        cfsmif.dREN = cuif.dREN;
        cfsmif.dWEN = cuif.dWEN;
        cuif.ram_wait = cfsmif.ram_wait;
        cfsmif.init_done   = initif.init_valid;

        // Assign address mapper signals
        amif.address = cuif.address;

        // Assign row policy signals
        polif.row_resolve  = cfsmif.row_resolve;
        polif.req_en       = cuif.dREN || cuif.dWEN;       
    end
endmodule