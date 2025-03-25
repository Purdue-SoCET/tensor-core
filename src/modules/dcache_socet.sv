/*
*   Copyright 2016 Purdue University
*
*   Licensed under the Apache License, Version 2.0 (the "License");
*   you may not use this file except in compliance with the License.
*   You may obtain a copy of the License at
*
*       http://www.apache.org/licenses/LICENSE-2.0
*
*   Unless required by applicable law or agreed to in writing, software
*   distributed under the License is distributed on an "AS IS" BASIS,
*   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
*   See the License for the specific language governing permissions and
*   limitations under the License.
*
*
*   Filename:     l1_cache.sv
*
*   Created by:   Rufat Imanov, Aedan Frazier, Dhruv Gupta
*   Email:        rimanov@purdue.edu
*   Date Created: 06/20/2021
*   Description:  L1 Cache. The following are configurable:
*                   - Cache Size
*                   - Non-Cacheable start address
*                   - Block Size | max 8
*	            - ASSOC | either 1 or 2
*/

`include "generic_bus_if.vh"
`include "cache_coherence_if.vh"

`ifdef XCELIUM
`timescale 1ns/100ps
`endif

module l1_cache #(
    parameter CACHE_SIZE          = 1024, // must be power of 2, in bytes, max 4k - 4 * 2^10
    parameter BLOCK_SIZE          = 2, // must be power of 2, max 8
    parameter ASSOC               = 1, // dont set this to 0
    parameter NONCACHE_START_ADDR = 32'hF000_0000 // sh/sb still have issues when uncached; not sure whats up with that still tbh
)
(
    input logic CLK, nRST,
    input logic clear, flush, reserve, exclusive,
    output logic clear_done, flush_done,
    generic_bus_if.cpu mem_gen_bus_if,
    generic_bus_if.generic_bus proc_gen_bus_if,
    cache_coherence_if.cache ccif //Coherency interface, connected to coherency unit
);
    import rv32i_types_pkg::*;
    
    // local parameters
    localparam N_TOTAL_BYTES      = CACHE_SIZE / 8;
    localparam N_TOTAL_WORDS      = N_TOTAL_BYTES / 4;
    localparam N_TOTAL_FRAMES     = N_TOTAL_WORDS / BLOCK_SIZE;
    localparam N_SETS             = N_TOTAL_FRAMES / ASSOC;
    localparam N_FRAME_BITS       = $clog2(ASSOC) + (ASSOC == 1);
    localparam N_SET_BITS         = $clog2(N_SETS) + (N_SETS == 1);
    localparam N_BLOCK_BITS       = $clog2(BLOCK_SIZE) + (BLOCK_SIZE == 1);
    localparam N_TAG_BITS         = WORD_SIZE - N_SET_BITS - N_BLOCK_BITS - 2;
    localparam FRAME_SIZE         = WORD_SIZE * BLOCK_SIZE + N_TAG_BITS + 2 + 1; // in bits (+1 for exclusive bit)
    localparam SRAM_W             = FRAME_SIZE * ASSOC;                      // sram parameters
    localparam SRAM_TAG_W         = (N_TAG_BITS + 3) * ASSOC; // +3 for valid, dirty, and exclusive
    localparam CLEAR_LENGTH       = $clog2(BLOCK_SIZE) + 2;

    typedef struct packed {
        logic exclusive;
        logic valid;
        logic dirty;
        logic [N_TAG_BITS-1:0] tag_bits;
    } cache_tag_t;

    typedef struct packed{
        cache_tag_t tag;
        word_t [BLOCK_SIZE - 1:0] data;
    } cache_frame_t;    // cache frame

    typedef struct packed {
        cache_frame_t [ASSOC - 1:0] frames;
    } cache_set_t;      // cache set

    typedef struct packed {
        logic [N_TAG_BITS-1:0] tag_bits;
        logic [N_SET_BITS-1:0] idx_bits;
        logic [N_BLOCK_BITS-1:0] block_bits;
    } decoded_cache_idx_t;

    typedef struct packed {
        decoded_cache_idx_t idx;
        logic [1:0] byte_bits;
    } decoded_cache_addr_t;   // cache address type

    typedef struct packed {
        logic finish;
        logic [N_SET_BITS-1:0] set_num;
        logic [N_FRAME_BITS-1:0] frame_num; // assoc
    } flush_idx_t;             // flush counter type

    typedef enum {
       IDLE, HIT, FETCH, WB, FLUSH_CACHE, SNOOP, CANCEL_REQ
    } cache_fsm_t;            // cache state machine

    typedef struct packed {
        decoded_cache_idx_t idx;
        logic reserved;
    } reservation_set_t;
    
    // counter signals
    flush_idx_t flush_idx, next_flush_idx;
    logic clear_flush_count, enable_flush_count, enable_flush_count_nowb;
    // States
    cache_fsm_t state, next_state;
    // lru
    logic [N_FRAME_BITS-1:0] ridx;
    logic [N_SETS-1:0] last_used;
    logic [N_SETS-1:0] next_last_used;
    // address
    word_t read_addr, next_read_addr;
    decoded_cache_addr_t decoded_req_addr, next_decoded_req_addr;
    decoded_cache_addr_t decoded_addr, snoop_decoded_addr;
    //decoded_cache_addr_t decoded_snoop_addr;
    // Cache Hit
    logic hit, pass_through;
    word_t [BLOCK_SIZE-1:0] hit_data;
    logic [N_FRAME_BITS-1:0] hit_idx;
    // sram signals
    cache_set_t sramWrite, sramRead, sramMask;
    cache_tag_t [ASSOC-1:0] sramTags, sramTagsMask;
    logic sramWEN; // no need for REN
    logic [N_SET_BITS-1:0] sramSEL, sramSNOOPSEL;
    cache_tag_t [ASSOC-1:0] read_tag_bits; //Tag coming from bus
    // flush reg
    logic flush_req, nflush_req;
    logic idle_done;
    // Reservation tracking
    reservation_set_t reservation_set, next_reservation_set;
    logic addr_is_reserved;

    //Snooping signals
    logic[N_TAG_BITS-1:0] bus_frame_tag; //Tag from bus to compare

    assign snoop_decoded_addr = decoded_cache_addr_t'(ccif.addr);

    // sram instance
    assign sramSEL = (state == FLUSH_CACHE || state == IDLE) ? flush_idx.set_num
                   : (state == SNOOP) ? snoop_decoded_addr.idx.idx_bits
                   : decoded_addr.idx.idx_bits;
    sram #(.SRAM_WR_SIZE(SRAM_W), .SRAM_HEIGHT(N_SETS)) 
        CPU_SRAM(.CLK(CLK), .nRST(nRST), .wVal(sramWrite), .rVal(sramRead), .REN(1'b1), .WEN(sramWEN), .SEL(sramSEL), .wMask(sramMask));
    sram #(.SRAM_WR_SIZE(SRAM_TAG_W), .SRAM_HEIGHT(N_SETS))
        BUS_SRAM(.CLK(CLK), .nRST(nRST), .wVal(sramTags), .rVal(read_tag_bits), .REN(1'b1), .WEN(sramWEN), .SEL(sramSNOOPSEL), .wMask(sramTagsMask));

    assign bus_frame_tag = snoop_decoded_addr.idx.tag_bits;

    // flip flops
    always_ff @ (posedge CLK, negedge nRST) begin
        if(~nRST) begin
            state <= IDLE;
            flush_idx <= 0;
            last_used <= 0;
            read_addr <= 0;
            decoded_req_addr <= 0;
            flush_req <= 0;
            ccif.abort_bus <= 0;
            reservation_set <= 0;
        end
        else begin
            state <= next_state;                        // cache state machine
            flush_idx <= next_flush_idx;                // index for flushing the cache entries
            last_used <= next_last_used;                // MRU index
            read_addr <= next_read_addr;                // cache address to provide to memory
            decoded_req_addr <= next_decoded_req_addr;  // cache address requested by core
            flush_req <= nflush_req;                    // flush requested by core
            ccif.abort_bus <= !proc_gen_bus_if.ren && !proc_gen_bus_if.wen;
            reservation_set <= next_reservation_set;
        end
    end

    // counters
    always_comb begin
        next_flush_idx = flush_idx;

        // flush counter logic
        if (clear_flush_count)
            next_flush_idx = 0;
        else if (enable_flush_count_nowb && BLOCK_SIZE != 1)
            next_flush_idx = flush_idx + 1;
        else if (enable_flush_count || enable_flush_count_nowb)
            next_flush_idx = flush_idx + 1;

        // correction for non-powers of 2
        if (next_flush_idx.set_num == N_SETS) begin
            next_flush_idx.finish = 1;
            next_flush_idx.set_num = 0;
            next_flush_idx.frame_num = 0;
        end
        else if (next_flush_idx.frame_num == ASSOC) begin
            next_flush_idx.set_num = flush_idx.set_num + 1;
            next_flush_idx.frame_num = 0;
        end

        // FOR ASSOC == 1 FINISH FLAG
        if (next_flush_idx.set_num == 0 && flush_idx.set_num == N_SETS - 1) begin
            next_flush_idx.finish = 1;
            next_flush_idx.set_num = 0;
            next_flush_idx.frame_num = 0;
        end
    end

    // decoded address conversion
    assign decoded_addr = state == SNOOP ? snoop_decoded_addr : decoded_cache_addr_t'(proc_gen_bus_if.addr);

    logic coherence_hit, sc_valid_block;

    // Hit logic with pass through
    // CPU and bus sram have different always_comb blocks to prevent false
    // circular logic
    always_comb begin
        hit 	        = 0;
        hit_idx         = 0;
        hit_data        = 0;
        pass_through    = proc_gen_bus_if.addr >= NONCACHE_START_ADDR;
        coherence_hit   = 0;
        sc_valid_block  = 0;

        if (!pass_through) begin
            for(int i = 0; i < ASSOC; i++) begin
                if(sramRead.frames[i].tag.tag_bits == decoded_addr.idx.tag_bits && sramRead.frames[i].tag.valid) begin
                    sc_valid_block = addr_is_reserved;
                    coherence_hit = sramRead.frames[i].tag.dirty || sramRead.frames[i].tag.exclusive;
                    //Read or write hit
                    if((state == HIT && (proc_gen_bus_if.ren || (proc_gen_bus_if.wen && coherence_hit))) || state == SNOOP) begin
	                    hit       = 1'b1;
        	            hit_data  = sramRead.frames[i].data;
                	    hit_idx   = i;
                    end
                end
            end
        end
    end

    always_comb begin
        ccif.snoop_hit  = 0;
        ccif.valid = 0;
        ccif.dirty = 0;
        ccif.exclusive = 0;

        for(int i = 0; i < ASSOC; i++) begin
            if (read_tag_bits[i].tag_bits == bus_frame_tag && read_tag_bits[i].valid) begin
                ccif.snoop_hit = 1'b1;
                ccif.valid = read_tag_bits[i].valid;
                ccif.dirty = read_tag_bits[i].dirty;
                ccif.exclusive = read_tag_bits[i].exclusive;
            end
        end
    end

    // cache output logic
    // Outputs: counter control signals, cache, signals to memory, signals to processor
    always_comb begin
        sramWEN                 = 0;
        sramWrite               = 0;
        sramMask                = '1;
        proc_gen_bus_if.busy    = 1;
        proc_gen_bus_if.rdata   = 0; // TODO: Can this be optimized?
        mem_gen_bus_if.ren      = 0;
        mem_gen_bus_if.wen      = 0;
        mem_gen_bus_if.addr     = 0; 
        mem_gen_bus_if.wdata    = 0; 
        mem_gen_bus_if.byte_en  = '1; // set this to all 1s for evictions
        enable_flush_count      = 0;
        enable_flush_count_nowb = 0;
        clear_flush_count       = 0;
        flush_done 	            = 0;
        idle_done               = 0;
        clear_done 	            = 0;
        // This logic should not change as it may cause bizarre issues during
        // simulation. During testing it was found that this exact logic was
        // found in multiple places in the below `casez` statement, however,
        // it wouldn't execute correctly. For example, 0x80000510 would become
        // 0x80000500 for a block size of 2.
        next_read_addr          = proc_gen_bus_if.addr & ~{CLEAR_LENGTH{1'b1}};
        next_decoded_req_addr   = decoded_req_addr;
        next_last_used          = last_used;
        ccif.dWEN               = 1'b0;
        ccif.requested_data     = {BLOCK_SIZE{32'hBAD1BAD1}};

        // associativity, using NRU
        if (ASSOC == 1 || (last_used[decoded_addr.idx.idx_bits] == (ASSOC - 1)))
            ridx = 0;
        else
            ridx = last_used[decoded_addr.idx.idx_bits] + 1;

        // state dependent output logic
        casez(state)
            IDLE: begin
                // clear out caches with flush
                sramWEN = 1;
    	        sramWrite.frames[flush_idx.frame_num] = '0;
                sramMask.frames[flush_idx.frame_num] = '0;
                enable_flush_count_nowb = 1;
                // flag the completion of flush
                if (flush_idx.finish) begin
                    clear_flush_count  = 1;
                    idle_done 	       = 1;
                    flush_done = 1; //HACK: Remove if this causes bugs, used for testbench
                end
            end
            HIT: begin
                // cache hit on a processor read
                if(proc_gen_bus_if.ren && hit && !flush) begin
                    proc_gen_bus_if.busy = 0;
                    proc_gen_bus_if.rdata = hit_data[decoded_addr.idx.block_bits];
                    next_last_used[decoded_addr.idx.idx_bits] = hit_idx;
                    // Delay so we can set the reservation set
                    if (reserve && !addr_is_reserved) begin
                        proc_gen_bus_if.busy = 1;
                    end
                end
                // cache hit on a processor write
                else if(proc_gen_bus_if.wen && hit && (!reserve || (reserve && addr_is_reserved)) && !flush) begin
                    proc_gen_bus_if.busy = 0;
                    sramWEN = 1;
                    casez (proc_gen_bus_if.byte_en)
                        4'b0001:    sramMask.frames[hit_idx].data[decoded_addr.idx.block_bits] = 32'hFFFFFF00;
                        4'b0010:    sramMask.frames[hit_idx].data[decoded_addr.idx.block_bits] = 32'hFFFF00FF;
                        4'b0100:    sramMask.frames[hit_idx].data[decoded_addr.idx.block_bits] = 32'hFF00FFFF;
                        4'b1000:    sramMask.frames[hit_idx].data[decoded_addr.idx.block_bits] = 32'h00FFFFFF;
                        4'b0011:    sramMask.frames[hit_idx].data[decoded_addr.idx.block_bits] = 32'hFFFF0000;
                        4'b1100:    sramMask.frames[hit_idx].data[decoded_addr.idx.block_bits] = 32'h0000FFFF;
                        default:    sramMask.frames[hit_idx].data[decoded_addr.idx.block_bits] = 32'h0;
                    endcase
                    sramWrite.frames[hit_idx].data[decoded_addr.idx.block_bits] = proc_gen_bus_if.wdata;
                    sramWrite.frames[hit_idx].tag.dirty = 1;
                    sramWrite.frames[hit_idx].tag.exclusive = 0; //Set exclusive bit in tag to 0, E -> M case
                    sramMask.frames[hit_idx].tag.dirty = 0;
                    sramMask.frames[hit_idx].tag.exclusive = 0;
                    next_last_used[decoded_addr.idx.idx_bits] = hit_idx;
                    proc_gen_bus_if.rdata = 0;
                end
                // passthrough
                else if(pass_through) begin
                    mem_gen_bus_if.wen      = proc_gen_bus_if.wen;
                    mem_gen_bus_if.ren      = proc_gen_bus_if.ren;
                    mem_gen_bus_if.addr     = proc_gen_bus_if.addr;
                    mem_gen_bus_if.byte_en  = proc_gen_bus_if.byte_en;
                    proc_gen_bus_if.busy    = mem_gen_bus_if.busy;
                    proc_gen_bus_if.rdata   = mem_gen_bus_if.rdata;
                    if(proc_gen_bus_if.wen) begin
                        casez (proc_gen_bus_if.byte_en)
                            4'b0001:    mem_gen_bus_if.wdata  = {24'd0, proc_gen_bus_if.wdata[7:0]};
                            4'b0010:    mem_gen_bus_if.wdata  = {16'd0,proc_gen_bus_if.wdata[15:8],8'd0};
                            4'b0100:    mem_gen_bus_if.wdata  = {8'd0, proc_gen_bus_if.wdata[23:16], 16'd0};
                            4'b1000:    mem_gen_bus_if.wdata  = {proc_gen_bus_if.wdata[31:24], 24'd0};
                            4'b0011:    mem_gen_bus_if.wdata  = {16'd0, proc_gen_bus_if.wdata[15:0]};
                            4'b1100:    mem_gen_bus_if.wdata  = {proc_gen_bus_if.wdata[31:16],16'd0};
                            default:    mem_gen_bus_if.wdata  = proc_gen_bus_if.wdata;
                        endcase
                    end 
                end
                // Cache miss of sc
                else if (proc_gen_bus_if.wen && reserve && !sc_valid_block && ~pass_through) begin
                    proc_gen_bus_if.busy = 0;
                    proc_gen_bus_if.rdata = 32'b1;
                end
                // cache miss on a clean block
		        else if((proc_gen_bus_if.ren || proc_gen_bus_if.wen) && ~hit && ~sramRead.frames[ridx].tag.dirty && ~pass_through) begin
                    next_decoded_req_addr = decoded_addr;
			    end
                // cache miss on a dirty block
			    else if((proc_gen_bus_if.ren || proc_gen_bus_if.wen) && ~hit && sramRead.frames[ridx].tag.dirty && ~pass_through) begin
                        next_decoded_req_addr = decoded_addr;
                        next_read_addr        =  {sramRead.frames[ridx].tag, decoded_addr.idx.idx_bits, N_BLOCK_BITS'('0), 2'b00};
                    end
            end 
            FETCH: begin
                // set cache to be invalid before cache completes fetch
                mem_gen_bus_if.wen = proc_gen_bus_if.wen;
                mem_gen_bus_if.ren = proc_gen_bus_if.ren || !ccif.abort_bus;
                mem_gen_bus_if.addr = read_addr;
                sramWrite.frames[ridx].tag.valid = 0;
                sramMask.frames[ridx].tag.valid = 0;
                // fill data
                if(~mem_gen_bus_if.busy) begin
                    sramWEN                             = 1'b1;
                    sramWrite.frames[ridx].data         = mem_gen_bus_if.rdata;
                    sramWrite.frames[ridx].tag.valid    = 1'b1;
                    sramWrite.frames[ridx].tag.tag_bits = decoded_req_addr.idx.tag_bits;
                    sramMask.frames[ridx].data          = 1'b0;
                    sramMask.frames[ridx].tag.valid     = 1'b0;
                    sramMask.frames[ridx].tag.tag_bits  = 1'b0;

                    sramWrite.frames[ridx].tag.exclusive = (ccif.state_transfer == EXCLUSIVE);
                    sramWrite.frames[ridx].tag.dirty = (ccif.state_transfer == MODIFIED);
                    sramMask.frames[ridx].tag.exclusive = 0;
                    sramMask.frames[ridx].tag.dirty = 0;

                    if (proc_gen_bus_if.wen) begin
                        casez (proc_gen_bus_if.byte_en)
                            4'b0001:    sramWrite.frames[ridx].data[decoded_addr.idx.block_bits][7:0] = proc_gen_bus_if.wdata[7:0];
                            4'b0010:    sramWrite.frames[ridx].data[decoded_addr.idx.block_bits][15:8] = proc_gen_bus_if.wdata[15:8];
                            4'b0100:    sramWrite.frames[ridx].data[decoded_addr.idx.block_bits][23:16] = proc_gen_bus_if.wdata[23:16];
                            4'b1000:    sramWrite.frames[ridx].data[decoded_addr.idx.block_bits][31:24] = proc_gen_bus_if.wdata[31:24];
                            4'b0011:    sramWrite.frames[ridx].data[decoded_addr.idx.block_bits][15:0] = proc_gen_bus_if.wdata[15:0];
                            4'b1100:    sramWrite.frames[ridx].data[decoded_addr.idx.block_bits][31:16] = proc_gen_bus_if.wdata[31:16];
                            default:    sramWrite.frames[ridx].data[decoded_addr.idx.block_bits] = proc_gen_bus_if.wdata;
                        endcase
                    end
                end
            end
            WB: begin
                // set stim for eviction
                ccif.dWEN = 1'b1;
                mem_gen_bus_if.wen = 1'b1;
                mem_gen_bus_if.addr = read_addr; 
                mem_gen_bus_if.wdata = sramRead.frames[ridx].data;
                next_read_addr =  {sramRead.frames[ridx].tag, decoded_addr.idx.idx_bits, N_BLOCK_BITS'('0), 2'b00};
                // increment eviction word counter
                if(!mem_gen_bus_if.busy) begin
                    // invalidate when eviction is complete
                    sramWEN = 1;
                    sramWrite.frames[ridx].tag.dirty = 0;
                    sramWrite.frames[ridx].tag.valid = 0;
                    sramMask.frames[ridx].tag.dirty  = 0;
                    sramMask.frames[ridx].tag.valid  = 0;
                end
            end
            SNOOP: begin
                ccif.requested_data = sramRead.frames[hit_idx].data;
                if (!mem_gen_bus_if.busy) begin
                    sramWEN = 1;
                    case(ccif.state_transfer)
                        INVALID: begin
                            sramWrite.frames[hit_idx].tag.dirty     = 0;
                            sramWrite.frames[hit_idx].tag.valid     = 0;
                            sramWrite.frames[hit_idx].tag.exclusive = 0;
                            sramMask.frames[hit_idx].tag.dirty         = 0;
                            sramMask.frames[hit_idx].tag.valid         = 0;
                            sramMask.frames[hit_idx].tag.exclusive     = 0;
                        end 
                        SHARED: begin
                            sramWrite.frames[hit_idx].tag.dirty     = 0;
                            sramWrite.frames[hit_idx].tag.valid     = 1;
                            sramWrite.frames[hit_idx].tag.exclusive = 0;
                            sramMask.frames[hit_idx].tag.dirty      = 0;
                            sramMask.frames[hit_idx].tag.valid      = 0;
                            sramMask.frames[hit_idx].tag.exclusive  = 0;
                        end 
                        EXCLUSIVE: begin
                            sramWrite.frames[hit_idx].tag.dirty     = 0;
                            sramWrite.frames[hit_idx].tag.valid     = 1;
                            sramWrite.frames[hit_idx].tag.exclusive = 1;
                            sramMask.frames[hit_idx].tag.dirty      = 0;
                            sramMask.frames[hit_idx].tag.valid      = 0;
                            sramMask.frames[hit_idx].tag.exclusive  = 0;
                        end 
                        MODIFIED: begin
                            sramWrite.frames[hit_idx].tag.dirty     = 1;
                            sramWrite.frames[hit_idx].tag.valid     = 1;
                            sramWrite.frames[hit_idx].tag.exclusive = 0;
                            sramMask.frames[hit_idx].tag.dirty      = 0;
                            sramMask.frames[hit_idx].tag.valid      = 0;
                            sramMask.frames[hit_idx].tag.exclusive  = 0;
                        end 
                    endcase
                end
            end
            FLUSH_CACHE: begin
                // flush to memory if valid & dirty
                if (sramRead.frames[flush_idx.frame_num].tag.valid && sramRead.frames[flush_idx.frame_num].tag.dirty) begin
                    ccif.dWEN             = 1'b1;
                    mem_gen_bus_if.wen    = 1'b1;
                    mem_gen_bus_if.addr   = {sramRead.frames[flush_idx.frame_num].tag.tag_bits, flush_idx.set_num, {N_BLOCK_BITS{1'b0}}, 2'b00};
                    mem_gen_bus_if.wdata  = sramRead.frames[flush_idx.frame_num].data;
                    // increment to next word when flush of word is done
                    if (~mem_gen_bus_if.busy) begin
                        enable_flush_count = 1;
                        // clears entry when flushed
                        sramWEN = 1;
                        sramWrite.frames[flush_idx.frame_num] = 0;
                        sramMask.frames[flush_idx.frame_num] = 0;
                    end
                end
                // else clears entry, moves to next frame
                else begin
                    sramWEN = 1;
	    	        sramWrite.frames[flush_idx.frame_num] = 0;
                    sramMask.frames[flush_idx.frame_num] = 0;
                    enable_flush_count_nowb = 1;
                end
                // flag the completion of flush
                if (flush_idx.finish) begin
                    clear_flush_count  = 1;
                    flush_done 	       = 1;
                end
            end
            CANCEL_REQ: begin
                mem_gen_bus_if.wen     = 0;
                mem_gen_bus_if.ren     = 1;
                mem_gen_bus_if.addr    = decoded_addr;
                mem_gen_bus_if.byte_en = 0;
                proc_gen_bus_if.busy   = 1;
            end
        endcase

        // Same as sramSEL except try to lookup the snoop addr when there's
        // a request
        sramSNOOPSEL    = sramWEN ? sramSEL
                        : ccif.snoop_req ? snoop_decoded_addr.idx.idx_bits
                        : sramSEL;
        ccif.snoop_busy = sramWEN || !ccif.snoop_req;

        for (int i = 0; i < ASSOC; i++) begin
            sramTags[i] = sramWrite.frames[i].tag;
            sramTagsMask[i] = sramMask.frames[i].tag;
        end
    end

    always_comb begin
        // To properly catch this case, set epoch size to 10k and range to
        // be % 512 in cache stress testbench
        if (CLK == 1 && sramWEN) begin
            if (sramSEL != sramSNOOPSEL) begin
                $warning("WARNING: sram sels should be same");
            end
        end
        if (sramSNOOPSEL == sramSEL) begin
            for (int i = 0; i < ASSOC; i++) begin
                if (read_tag_bits[i] != sramRead.frames[i].tag) begin
                    $warning("WARNING: sram tags are out of sync!");
                end
            end
        end
        if (state == SNOOP && next_state == SNOOP) begin
            if (sramSNOOPSEL != sramSEL) begin
                $timeformat(-12, 2, " ps", 20);
                $warning("WARNING: sram selection incorrect!");
            end
            if (sramRead.frames[hit_idx].tag.tag_bits != bus_frame_tag) begin
                $timeformat(-12, 2, " ps", 20);
                $warning("WARNING: returning incorrect hit_idx data!");
                $warning(
                    "hit_idx: %d, addr tag: %x, tag: %x, bus_frame: %x",
                    hit_idx,
                    decoded_addr.idx.tag_bits,
                    sramRead.frames[hit_idx].tag.tag_bits,
                    bus_frame_tag
                );
            end
        end
    end

    // next state logic
    always_comb begin
	    next_state = state;
	    casez(state)
            IDLE: begin
                if (idle_done) //Used when flushing
                    next_state = HIT;
	        end
	        HIT: begin
                if (ccif.snoop_hit && !ccif.snoop_busy)
                    next_state = SNOOP;
                else if (proc_gen_bus_if.wen && reserve && !sc_valid_block && ~pass_through) // Don't transition on a failed sc
                    next_state = state;
                else if ((proc_gen_bus_if.ren || proc_gen_bus_if.wen) && ~hit && sramRead.frames[ridx].tag.dirty && ~pass_through)
                    next_state = WB;
                else if ((proc_gen_bus_if.ren || proc_gen_bus_if.wen) && ~hit && ~sramRead.frames[ridx].tag.dirty && ~pass_through)
                    next_state = FETCH;
                if (flush || flush_req)  
                    next_state = FLUSH_CACHE;
	        end
	        FETCH: begin
                if (!mem_gen_bus_if.busy || mem_gen_bus_if.error)
                    next_state = HIT; 
                else if (ccif.snoop_hit && !ccif.snoop_busy)
                    next_state = SNOOP;
                else if (!ccif.abort_bus && !proc_gen_bus_if.ren && !proc_gen_bus_if.wen)
                    next_state = CANCEL_REQ;
            end
            WB: begin
                if (!mem_gen_bus_if.busy)
                    next_state = HIT; 
                else if (ccif.snoop_hit && !ccif.snoop_busy)
                    next_state = SNOOP;
            end
            SNOOP: begin
                next_state = ccif.snoop_req ? SNOOP :
                             flush_req      ? FLUSH_CACHE : HIT;
            end
            FLUSH_CACHE: begin
                if (flush_done)
                    next_state = HIT;
                else if (ccif.snoop_hit && !ccif.snoop_busy)
                    next_state = SNOOP;
            end
            CANCEL_REQ: begin
               if (!mem_gen_bus_if.busy) begin
                   next_state = HIT;
               end else if (ccif.snoop_hit && !ccif.snoop_busy) begin
                   next_state = SNOOP;
               end
            end
	    endcase
    end

    // flush saver
    always_comb begin
        nflush_req = flush_req;
        if (flush)
            nflush_req = 1;
        if (flush_done)
            nflush_req = 0;
    end

    // Reservation tracking logic
    // TODO: Remove exclusive signal
    always_comb begin
        next_reservation_set = reservation_set;
        if (proc_gen_bus_if.ren && reserve && hit) begin
            next_reservation_set.idx = decoded_addr.idx;
            next_reservation_set.reserved = 1'b1;
        end else if (((proc_gen_bus_if.ren || proc_gen_bus_if.wen) && !proc_gen_bus_if.busy) || clear || flush) begin
            next_reservation_set.reserved = 1'b0;
        end
        addr_is_reserved = reservation_set.idx == decoded_addr.idx && reservation_set.reserved;
    end
endmodule