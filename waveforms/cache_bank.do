onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /cache_bank_tb/PROG/tb_clk
add wave -noupdate /cache_bank_tb/PROG/tb_nrst
add wave -noupdate /cache_bank_tb/PROG/tb_bank_id
add wave -noupdate /cache_bank_tb/PROG/test_id
add wave -noupdate /cache_bank_tb/PROG/SingleCycle_RW_Done
add wave -noupdate /cache_bank_tb/PROG/MSHR_Thread_Done
add wave -noupdate -divider PROG
add wave -noupdate -expand -subitemconfig {/cache_bank_tb/PROG/tb_mshr_entry.block_addr -expand} /cache_bank_tb/PROG/tb_mshr_entry
add wave -noupdate -subitemconfig {/cache_bank_tb/PROG/tb_mem_instr.addr -expand} /cache_bank_tb/PROG/tb_mem_instr
add wave -noupdate -group {PROG Inputs} /cache_bank_tb/PROG/tb_ram_mem_REN
add wave -noupdate -group {PROG Inputs} /cache_bank_tb/PROG/tb_ram_mem_WEN
add wave -noupdate -group {PROG Inputs} /cache_bank_tb/PROG/tb_ram_mem_store
add wave -noupdate -group {PROG Inputs} /cache_bank_tb/PROG/tb_ram_mem_addr
add wave -noupdate -group {PROG Inputs} /cache_bank_tb/PROG/tb_scheduler_data_out
add wave -noupdate -group {PROG Inputs} /cache_bank_tb/PROG/tb_scheduler_uuid_out
add wave -noupdate -group {PROG Inputs} /cache_bank_tb/PROG/tb_scheduler_hit
add wave -noupdate -group {PROG Inputs} /cache_bank_tb/PROG/tb_scheduler_uuid_ready
add wave -noupdate -group {PROG Outputs} /cache_bank_tb/PROG/tb_nrst
add wave -noupdate -group {PROG Outputs} /cache_bank_tb/PROG/tb_bank_id
add wave -noupdate -group {PROG Outputs} /cache_bank_tb/PROG/tb_instr_valid
add wave -noupdate -group {PROG Outputs} /cache_bank_tb/PROG/tb_ram_mem_data
add wave -noupdate -group {PROG Outputs} /cache_bank_tb/PROG/tb_ram_mem_complete
add wave -noupdate -divider FSM
add wave -noupdate /cache_bank_tb/dut/curr_state
add wave -noupdate /cache_bank_tb/dut/next_state
add wave -noupdate /cache_bank_tb/dut/halt
add wave -noupdate /cache_bank_tb/dut/scheduler_hit
add wave -noupdate /cache_bank_tb/dut/scheduler_uuid_ready
add wave -noupdate -group Bank -expand -subitemconfig {{/cache_bank_tb/dut/bank[0]} -expand} /cache_bank_tb/dut/bank
add wave -noupdate -group Bank /cache_bank_tb/dut/next_bank
add wave -noupdate -group Misc /cache_bank_tb/dut/instr_valid
add wave -noupdate -group Misc /cache_bank_tb/dut/ram_mem_data
add wave -noupdate -group Misc /cache_bank_tb/dut/mshr_entry_in
add wave -noupdate -group Misc /cache_bank_tb/dut/mem_instr_in
add wave -noupdate -group Misc /cache_bank_tb/dut/ram_mem_complete
add wave -noupdate -group Misc /cache_bank_tb/dut/cache_bank_free
add wave -noupdate -group Misc /cache_bank_tb/dut/ram_mem_REN
add wave -noupdate -group Misc /cache_bank_tb/dut/ram_mem_WEN
add wave -noupdate -group Misc /cache_bank_tb/dut/ram_mem_store
add wave -noupdate -group Misc /cache_bank_tb/dut/ram_mem_addr
add wave -noupdate -group Misc /cache_bank_tb/dut/scheduler_data_out
add wave -noupdate -group Misc /cache_bank_tb/dut/scheduler_uuid_out
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/count_FSM
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/next_count_FSM
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/count_flush
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/set_index
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/flushed
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/mshr_hit
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/latched_mshr_hit
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/mshr_entry
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/latched_mshr_entry
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/block_pull_buffer
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/latched_block_pull_buffer
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/victim_eject_buffer
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/latched_victim_eject_buffer
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/hit_way_index
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/mshr_hit_way
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/latched_mshr_hit_way
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/victim_set_index
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/victim_way_index
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/new_victim_way_index
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/latched_victim_set_index
add wave -noupdate -expand -group {Cache Controller} /cache_bank_tb/dut/latched_victim_way_index
add wave -noupdate -group Flush /cache_bank_tb/dut/next_flush_way
add wave -noupdate -group Flush /cache_bank_tb/dut/flush_way
add wave -noupdate -group Flush /cache_bank_tb/dut/next_flush_set
add wave -noupdate -group Flush /cache_bank_tb/dut/flush_set
add wave -noupdate -group Flush /cache_bank_tb/dut/flush_count
add wave -noupdate -group Flush /cache_bank_tb/dut/next_flush_count
add wave -noupdate -group PLRU /cache_bank_tb/dut/tree_lru
add wave -noupdate -group PLRU /cache_bank_tb/dut/next_tree_lru
add wave -noupdate -divider RAM
add wave -noupdate /cache_bank_tb/u_RAM/ram_addr
add wave -noupdate /cache_bank_tb/u_RAM/ram_store
add wave -noupdate /cache_bank_tb/u_RAM/ram_REN
add wave -noupdate /cache_bank_tb/u_RAM/ram_WEN
add wave -noupdate /cache_bank_tb/u_RAM/ram_load
add wave -noupdate /cache_bank_tb/u_RAM/ram_ready
add wave -noupdate /cache_bank_tb/u_RAM/current_addr
add wave -noupdate /cache_bank_tb/u_RAM/prev_addr
add wave -noupdate /cache_bank_tb/u_RAM/counter
add wave -noupdate /cache_bank_tb/u_RAM/next_counter
add wave -noupdate /cache_bank_tb/u_RAM/state
add wave -noupdate /cache_bank_tb/u_RAM/next_state
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {97877 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 228
configure wave -valuecolwidth 171
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
WaveRestoreZoom {97819 ps} {97940 ps}
