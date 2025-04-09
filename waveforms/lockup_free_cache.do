onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider TEST
add wave -noupdate /lockup_free_cache_tb/tb_clk
add wave -noupdate /lockup_free_cache_tb/tb_nrst
add wave -noupdate /lockup_free_cache_tb/testcase
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_mem_in
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_mem_out_uuid
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/uuid
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_mem_in_addr
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_mem_in_rw_mode
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_mem_in_store_value
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_stall
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_hit
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_halt
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_flushed
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_hit_load
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_block_status
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_uuid_block
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_ram_mem_REN
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_ram_mem_WEN
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_ram_mem_addr
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_ram_mem_store
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_ram_mem_data
add wave -noupdate -group TOP_LEVEL /lockup_free_cache_tb/tb_ram_mem_complete
add wave -noupdate -divider {BANK 0}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/CLK}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/nRST}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/miss}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/bank_id}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/mem_instr}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/bank_empty}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/mshr_out}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/stall}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/uuid_out}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/buffer_empty}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/buffer}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/next_buffer}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/buffer_copy}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/secondary_misses}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/mshr_new_miss}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/uuid}
add wave -noupdate -group {MSHR BUFFER 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/next_uuid}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/CLK}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/nRST}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/bank_id}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/instr_valid}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/ram_mem_data}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/mshr_entry}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/mem_instr_in}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/ram_mem_complete}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/halt}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/cache_bank_busy}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/scheduler_hit}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/ram_mem_REN}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/ram_mem_WEN}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/ram_mem_store}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/ram_mem_addr}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/scheduler_data_out}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/scheduler_uuid_out}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/scheduler_uuid_ready}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/flushed}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/mshr_hit}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/next_mshr_hit}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/curr_state}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/next_state}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/count_FSM}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/next_count_FSM}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/count_flush}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/latched_block_pull_buffer}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/latched_victim_eject_buffer}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/flush_count}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/next_flush_count}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/latched_victim_way_index}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/victim_way_index}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/hit_way_index}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/max_way}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/next_flush_way}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/flush_way}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/mshr_hit_way}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/latched_victim_set_index}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/set_index}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/victim_set_index}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/next_flush_set}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/flush_set}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/lru}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/next_lru}
add wave -noupdate -group {BANK 0} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/max_age}
add wave -noupdate -divider {BANK 1}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/CLK}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/nRST}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/miss}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/bank_id}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/mem_instr}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/bank_empty}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/mshr_out}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/stall}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/uuid_out}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/buffer_empty}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/buffer}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/next_buffer}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/buffer_copy}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/secondary_misses}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/mshr_new_miss}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/uuid}
add wave -noupdate -group {MSHR BUFFER 1} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/mshr_buffer_i/next_uuid}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/CLK}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/nRST}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/bank_id}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/instr_valid}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/ram_mem_data}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/mshr_entry}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/mem_instr_in}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/ram_mem_complete}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/halt}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/cache_bank_busy}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/scheduler_hit}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/ram_mem_REN}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/ram_mem_WEN}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/ram_mem_store}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/ram_mem_addr}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/scheduler_data_out}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/scheduler_uuid_out}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/scheduler_uuid_ready}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/flushed}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/mshr_hit}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/next_mshr_hit}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/curr_state}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/next_state}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/count_FSM}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/next_count_FSM}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/count_flush}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/latched_block_pull_buffer}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/latched_victim_eject_buffer}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/flush_count}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/next_flush_count}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/latched_victim_way_index}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/victim_way_index}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/hit_way_index}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/max_way}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/next_flush_way}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/flush_way}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/mshr_hit_way}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/latched_victim_set_index}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/set_index}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/victim_set_index}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/next_flush_set}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/flush_set}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/lru}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/next_lru}
add wave -noupdate -group {BANK 1 } {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[1]/u_cache_bank/max_age}
add wave -noupdate -divider {BANK 2}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/CLK}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/nRST}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/miss}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/bank_id}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/mem_instr}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/bank_empty}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/mshr_out}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/stall}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/uuid_out}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/buffer_empty}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/buffer}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/next_buffer}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/buffer_copy}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/secondary_misses}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/mshr_new_miss}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/uuid}
add wave -noupdate -group {MSHR BUFFER 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/mshr_buffer_i/next_uuid}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/CLK}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/nRST}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/bank_id}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/instr_valid}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/ram_mem_data}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/mshr_entry}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/mem_instr_in}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/ram_mem_complete}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/halt}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/cache_bank_busy}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/scheduler_hit}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/ram_mem_REN}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/ram_mem_WEN}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/ram_mem_store}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/ram_mem_addr}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/scheduler_data_out}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/scheduler_uuid_out}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/scheduler_uuid_ready}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/flushed}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/mshr_hit}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/next_mshr_hit}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/curr_state}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/next_state}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/count_FSM}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/next_count_FSM}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/count_flush}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/latched_block_pull_buffer}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/latched_victim_eject_buffer}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/flush_count}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/next_flush_count}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/latched_victim_way_index}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/victim_way_index}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/hit_way_index}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/max_way}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/next_flush_way}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/flush_way}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/mshr_hit_way}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/latched_victim_set_index}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/set_index}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/victim_set_index}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/next_flush_set}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/flush_set}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/lru}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/next_lru}
add wave -noupdate -group {BANK 2} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[2]/u_cache_bank/max_age}
add wave -noupdate -divider {BANK 3}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/CLK}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/nRST}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/miss}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/bank_id}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/mem_instr}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/bank_empty}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/mshr_out}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/stall}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/uuid_out}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/buffer_empty}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/buffer}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/next_buffer}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/buffer_copy}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/secondary_misses}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/mshr_new_miss}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/uuid}
add wave -noupdate -group {MSHR BUFFER 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/mshr_buffer_i/next_uuid}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/CLK}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/nRST}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/bank_id}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/instr_valid}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/ram_mem_data}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/mshr_entry}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/mem_instr_in}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/ram_mem_complete}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/halt}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/cache_bank_busy}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/scheduler_hit}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/ram_mem_REN}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/ram_mem_WEN}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/ram_mem_store}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/ram_mem_addr}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/scheduler_data_out}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/scheduler_uuid_out}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/scheduler_uuid_ready}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/flushed}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/mshr_hit}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/next_mshr_hit}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/curr_state}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/next_state}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/count_FSM}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/next_count_FSM}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/count_flush}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/latched_block_pull_buffer}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/latched_victim_eject_buffer}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/flush_count}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/next_flush_count}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/latched_victim_way_index}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/victim_way_index}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/hit_way_index}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/max_way}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/next_flush_way}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/flush_way}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/mshr_hit_way}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/latched_victim_set_index}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/set_index}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/victim_set_index}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/next_flush_set}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/flush_set}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/lru}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/next_lru}
add wave -noupdate -group {BANK 3} {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[3]/u_cache_bank/max_age}
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {134 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {1067 ps}
