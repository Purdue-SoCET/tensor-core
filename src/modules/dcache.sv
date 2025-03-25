`include "datapath_cache_if.vh"
`include "caches_if.vh"

module dcache(
    input logic CLK,
    input logic nRST,
    datapath_cache_if.dcache dp,
    caches_if.dcache ca
);
    import cpu_types_pkg::*;



    // typedef struct packed {
    //     logic [25:0] addr_tag_set1;
    //     logic [25:0] addr_tag_set2;
    //     logic valid1, dirty1, valid2, dirty2;
    //     logic [63:0] data1, data2;
    // } dcache_t;
    
    typedef enum logic [3:0] { 
        IDLE,
        REQUEST_BLOCK1,
        REQUEST_BLOCK2,
        WB_BLOCK1,
        WB_BLOCK2,
        UPDATE_MEM_CACHE,
        WB_FLUSH1,
        WB_FLUSH2,
        SEND_HIT
    } state_cache_t;

    
    state_cache_t state, n_state;
    logic hit1, hit2;
    dcachef_t addr_format;
    dcache_frame [7:0] set1, set2;
    logic n_dREN, n_dWEN;
    word_t [1:0] buff_data;
    word_t datastore;

    ////////////////////Signals for IDLE //////////////////////////////
    logic update1_write, update2_write;

    ////////////////////Signals for REQUEST BLOCK 1 and 2 /////////////
    logic write_block1, write_block2;

    /////////////////Signals for UPDATE_MEM_CACHE /////////////////////
    logic write1_MISS, write2_MISS;


    ///////////////Signals for WB BLOCK 1 and 2 ///////////////////////

    //Right now is none

    //////////////////// VARIABLE FOR LRU and EVICT case //////////////
    logic [7:0] LRU_trk;
    logic evict;
    logic least_recent;

    /////////////////// VARIABLE FOR HANDLING HALT ////////////////////
    logic halt1, halt2, dhalt;

    ////////////////// VARIABLE FOR FLUSHING //////////////////////////
    logic [2:0] idx_flush, n_idx_flush;
    logic clear_idx_flush;

    ////////////////// VARIABLE FOR counting_hit //////////////////////////
    word_t counting_hit, n_counting_hit;
    logic  miss_appear, n_miss_appear;

    assign addr_format = dcachef_t'(dp.dmemaddr);
    assign dp.dmemload = buff_data[addr_format.blkoff];

    
    typedef struct packed {
        logic [25:0] addr_tag_set1;
        logic [25:0] addr_tag_set2;
        logic valid1, dirty1, valid2, dirty2;
        word_t [1:0] data1, data2;
    } dcache_t;

    always_ff @(posedge CLK, negedge nRST) begin: HIT_COUNTING_logic
        if(!nRST) begin
            counting_hit <= '0;        
            miss_appear <= '0;
        end else begin
            counting_hit <= n_counting_hit;
            miss_appear <= n_miss_appear;
        end
        
    end

    always_ff @(posedge CLK, negedge nRST) begin: FLUSH_logic
        if(!nRST) begin
            idx_flush <= '0;
        end else begin
            idx_flush <= n_idx_flush;
            if (dp.flushed) begin
                set1 <= '0;
                set2 <= '0;
            end
            //Logic for clearing the flux
            if (clear_idx_flush) begin
                if (!set1[idx_flush].dirty) begin
                    set1[idx_flush].dirty = 1'b0;
                end else begin
                    set2[idx_flush].dirty = 1'b0;
                end
            end
        end
    end
    always_ff @(posedge CLK, negedge nRST) begin: HANDLE_HALT
        if (!nRST) begin
            halt1 <= '0;
            halt2 <= '0;
            dhalt <= '0;
        end else begin
            halt1 <= dp.halt;
            halt2 <= halt1;
            dhalt <= halt2;
        end
    end

    always_ff @(posedge CLK, negedge nRST) begin : LRU
        if (!nRST) begin
            LRU_trk <= '0;
        end else begin
            if (dp.dhit) begin
                LRU_trk[addr_format.idx] <= least_recent;
            end
        end

    end

    always_ff @( posedge CLK, negedge nRST ) begin : STATE_LOGIC
        if (!nRST) begin
            state <= IDLE;
            datastore = '0;
            ca.dREN <= '0;
            ca.dWEN <= '0;
        end else begin
            state <= n_state;
            ca.dREN <= n_dREN;
            ca.dWEN <= n_dWEN;
            if (write_block1) begin
                datastore[0] <= ca.dload;
            end else if (write_block2) begin
                datastore[1] <= ca.dload;
            end
        end
    end

    always_ff @(posedge CLK, negedge nRST) begin : update_CACHE_logic
        if (!nRST) begin
            set1 <= '0;
            set2 <= '0;
        end else begin

            //Logic for writing if cache is valid
            if (update1_write) begin
                set1[addr_format.idx].valid <= 1'b1;
                set1[addr_format.idx].dirty <= 1'b1; 
                set1[addr_format.idx].tag   <= addr_format.tag;
                set1[addr_format.idx].data[addr_format.blkoff] <= dp.dmemstore; 
            end else if (update2_write) begin
                set2[addr_format.idx].valid = 1'b1;
                set2[addr_format.idx].dirty = 1'b1; 
                set2[addr_format.idx].tag   = addr_format.tag;
                set2[addr_format.idx].data[addr_format.blkoff] = dp.dmemstore; 
            end

            //Logic for writing from RAM to cache if it's miss
            if (write1_MISS) begin
                set1[addr_format.idx].valid <= 1'b1;
                set1[addr_format.idx].dirty <= 1'b0; 
                set1[addr_format.idx].tag <= addr_format.tag;
                set1[addr_format.idx].data <= datastore;
            end else if (write2_MISS) begin
                set2[addr_format.idx].valid <= 1'b1;
                set2[addr_format.idx].dirty <= 1'b0; 
                set2[addr_format.idx].tag <= addr_format.tag;
                set2[addr_format.idx].data <= datastore;
            end
            // Evict case
            if (evict) begin
                //If we need to evict set2
                if (LRU_trk[addr_format.idx]) begin
                    set2[addr_format.idx] <= '0;
                end else begin
                    set1[addr_format.idx] <= '0;
                end
            end
        end
    end

    always_comb begin : COUNING_LOGIC
        n_counting_hit = counting_hit;
        
        if (!miss_appear) begin
            if (dp.dhit) begin
                if (counting_hit + 1 < '1) begin
                    n_counting_hit = counting_hit + 1;
                end 
            end
        end
    end

    //Handling output logic and next state logic
    always_comb begin
        n_state = state;
        buff_data = '0;
        hit1 = (set1[addr_format.idx].tag == addr_format.tag) && (set1[addr_format.idx].valid);
        hit2 = (set2[addr_format.idx].tag == addr_format.tag) && (set2[addr_format.idx].valid);
        n_idx_flush = idx_flush;

        //default value for datapath cache
        {dp.dhit, dp.flushed} = '0;

        //default value cache and memory controller
        // {ca.dREN, ca.dWEN, ca.daddr, ca.dstore} = '0;
        n_dREN = ca.dREN;
        n_dWEN = ca.dWEN;
        

        //default value for write from datapath to cache IDLE case
        {update1_write, update2_write} = '0;

        //default value for request block 1 and request block 2
        {write_block1, write_block2} = '0;
        {write1_MISS, write2_MISS}   = '0;

        //default value for evict
        evict = 1'b0;
        least_recent = '0;
        
        n_miss_appear = miss_appear;
        case (state)
            IDLE: begin
                if (dhalt) begin
                    n_state = WB_FLUSH1;
                end
                if (dp.dmemREN) begin
                    dp.dhit = (hit1 || hit2) ? 1'b1 : 1'b0;
                    least_recent = hit1 ? 1'b1 : 1'b0;
                    buff_data = hit1 ? set1[addr_format.idx].data : hit2 ? set2[addr_format.idx].data : '0;
                    //Checking both blocks are full or not
                    if (!dp.dhit && (set1[addr_format.idx].valid && set2[addr_format.idx].valid)) begin
                        //Checking dirty or not
                        if (set1[addr_format.idx].dirty || set2[addr_format.idx].dirty) begin
                            n_state = WB_BLOCK1;
                        end else begin
                            evict = 1'b1;
                            n_state = REQUEST_BLOCK1;
                        end
                    end else if (!dp.dhit) begin
                        n_state = REQUEST_BLOCK1;
                    end
                end
                else if (dp.dmemWEN) begin
                    dp.dhit = (hit1 || hit2) ? 1'b1 : 1'b0;
                    least_recent = hit1 ? 1'b1 : 1'b0;

                    //Checking both blocks are full or not
                    if (!dp.dhit && (set1[addr_format.idx].valid && set2[addr_format.idx].valid)) begin
                        //Checking dirty or not
                        if (set1[addr_format.idx].dirty || set2[addr_format.idx].dirty) begin
                            n_state = WB_BLOCK1;
                        end else begin
                            evict = 1'b1;
                            n_state = REQUEST_BLOCK1;
                        end
                    end else if (!dp.dhit) begin
                        n_state = REQUEST_BLOCK1;
                    end else begin 
                        if (set1[addr_format.idx].tag == addr_format.tag) begin
                            update1_write = 1'b1;
                        end else if (set2[addr_format.idx].tag == addr_format.tag) begin
                            update2_write = 1'b1;
                        end
                    end
                end
            end

            REQUEST_BLOCK1: begin
                //Output logic
                n_dREN = 1'b1;
                n_miss_appear = 1'b1;
                ca.daddr = {addr_format.tag, addr_format.idx, 1'b0, addr_format.bytoff};
                if (ca.dwait == 0) begin
                    n_dREN = 1'b0;
                    write_block1 = 1'b1;                    
                    n_state = REQUEST_BLOCK2;
                end
            end
            REQUEST_BLOCK2: begin
                n_dREN = 1'b1;
                ca.daddr = {addr_format.tag, addr_format.idx, 1'b1, addr_format.bytoff};
                
                if (ca.dwait == 0) begin
                    n_dREN = 1'b0;
                    write_block2 = 1'b1;
                    n_state = UPDATE_MEM_CACHE;
                end
            end


            UPDATE_MEM_CACHE: begin
                
                if (!set1[addr_format.idx].valid) begin
                    write1_MISS = 1'b1;
                    n_miss_appear = 1'b0;
                end else begin
                    write2_MISS = 1'b1;
                    n_miss_appear = 1'b0;
                end
                n_state = IDLE;
            end

            WB_BLOCK1: begin
                

                //If least recent is set2
                if (LRU_trk[addr_format.idx]) begin
                    n_dWEN = 1'b1;
                    ca.daddr = {set2[addr_format.idx].tag, addr_format.idx, 1'b0, '0}; //According to GTAs, block set will always 0
                    ca.dstore = set2[addr_format.idx].data[0];
                end else begin
                    n_dWEN = 1'b1;
                    //if least recent is set1
                    ca.daddr = {set1[addr_format.idx].tag, addr_format.idx, 1'b0, '0}; //According to GTAs, block set will always 0
                    ca.dstore = set1[addr_format.idx].data[0];
                end

                if (ca.dwait == 0) begin
                    n_dWEN = 1'b0;
                    n_state = WB_BLOCK2;
                end
            end

            WB_BLOCK2: begin
                if (LRU_trk[addr_format.idx]) begin
                    n_dWEN = 1'b1;
                    ca.daddr = {set2[addr_format.idx].tag, addr_format.idx, 1'b1, '0}; //According to GTAs, block set will always 0
                    ca.dstore = set2[addr_format.idx].data[1];
                end else begin
                    //if least recent is set1
                    n_dWEN = 1'b1;
                    ca.daddr = {set1[addr_format.idx].tag, addr_format.idx, 1'b1, '0}; //According to GTAs, block set will always 0
                    ca.dstore = set1[addr_format.idx].data[1];
                end

                if (ca.dwait == 0) begin
                    n_dWEN = 1'b0;
                    evict = 1'b1;
                    n_state  = REQUEST_BLOCK1;
                end

            end

            WB_FLUSH1: begin
                if ((!set1[idx_flush].dirty && !set2[idx_flush].dirty) && (idx_flush == 3'd7)) begin
                    dp.flushed = 1'b1;
                    n_state = SEND_HIT;
                end else begin
                    if (!set1[idx_flush].dirty && !set2[idx_flush].dirty) begin
                        n_idx_flush = idx_flush + 1;
                    end else if (set1[idx_flush].dirty) begin
                        n_dWEN = 1'b1;
                        ca.daddr = {set1[idx_flush].tag, idx_flush, 1'b0, '0}; //According to GTAs, block set will always 0
                        ca.dstore = set1[idx_flush].data[0];
                    end
                    else begin
                        n_dWEN = 1'b1;
                        ca.daddr = {set2[idx_flush].tag, idx_flush, 1'b0, '0}; //According to GTAs, block set will always 0
                        ca.dstore = set2[idx_flush].data[0];
                        
                    end

                    if (ca.dwait == 0) begin
                        n_dWEN = 1'b0;
                        n_state = WB_FLUSH2;
                    end
                end
            end

            WB_FLUSH2: begin
                if (set1[idx_flush].dirty) begin
                    n_dWEN = 1'b1;
                    ca.daddr = {set1[idx_flush].tag, idx_flush, 1'b1, '0}; //According to GTAs, block set will always 0
                    ca.dstore = set1[idx_flush].data[1];
                    
                end else begin
                    n_dWEN = 1'b1;
                    ca.daddr = {set2[idx_flush].tag, idx_flush, 1'b1, '0}; //According to GTAs, block set will always 0
                    ca.dstore = set2[idx_flush].data[1]; 
                end
                if (ca.dwait == 0) begin
                    n_dWEN = 1'b0;
                    clear_idx_flush = 1'b1;
                    n_state = WB_FLUSH1;
                end
            end

            SEND_HIT: begin
                n_dWEN = 1'b1;
                ca.daddr = 32'h3100;
                ca.dstore = counting_hit;
                if (ca.dwait == 0) begin
                    n_dWEN = 1'b0;
                    n_state = IDLE;
                end
            end
            default:;
        endcase
    end
endmodule