onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /cache_bank_tb/PROG/tb_clk
add wave -noupdate /cache_bank_tb/PROG/tb_nrst
add wave -noupdate /cache_bank_tb/PROG/tb_bank_id
add wave -noupdate /cache_bank_tb/PROG/test_id
add wave -noupdate /cache_bank_tb/PROG/SingleCycle_RW_Done
add wave -noupdate /cache_bank_tb/PROG/MSHR_Thread_Done
add wave -noupdate -divider PROG
add wave -noupdate -subitemconfig {/cache_bank_tb/PROG/tb_mshr_entry.block_addr {-height 16 -childformat {{tag -radix decimal} {index -radix hexadecimal}} -expand} /cache_bank_tb/PROG/tb_mshr_entry.block_addr.tag {-radix decimal} /cache_bank_tb/PROG/tb_mshr_entry.block_addr.index {-radix hexadecimal}} /cache_bank_tb/PROG/tb_mshr_entry
add wave -noupdate -expand -subitemconfig {/cache_bank_tb/PROG/tb_mem_instr.addr -expand} /cache_bank_tb/PROG/tb_mem_instr
add wave -noupdate -expand -group {PROG Inputs} /cache_bank_tb/PROG/tb_cache_bank_busy
add wave -noupdate -expand -group {PROG Inputs} /cache_bank_tb/PROG/tb_ram_mem_REN
add wave -noupdate -expand -group {PROG Inputs} /cache_bank_tb/PROG/tb_ram_mem_WEN
add wave -noupdate -expand -group {PROG Inputs} /cache_bank_tb/PROG/tb_ram_mem_store
add wave -noupdate -expand -group {PROG Inputs} /cache_bank_tb/PROG/tb_ram_mem_addr
add wave -noupdate -expand -group {PROG Inputs} /cache_bank_tb/PROG/tb_scheduler_data_out
add wave -noupdate -expand -group {PROG Inputs} /cache_bank_tb/PROG/tb_scheduler_uuid_out
add wave -noupdate -expand -group {PROG Inputs} /cache_bank_tb/PROG/tb_scheduler_hit
add wave -noupdate -expand -group {PROG Inputs} /cache_bank_tb/PROG/tb_scheduler_uuid_ready
add wave -noupdate -expand -group {PROG Outputs} /cache_bank_tb/PROG/tb_nrst
add wave -noupdate -expand -group {PROG Outputs} /cache_bank_tb/PROG/tb_bank_id
add wave -noupdate -expand -group {PROG Outputs} /cache_bank_tb/PROG/tb_instr_valid
add wave -noupdate -expand -group {PROG Outputs} /cache_bank_tb/PROG/tb_ram_mem_data
add wave -noupdate -expand -group {PROG Outputs} /cache_bank_tb/PROG/tb_ram_mem_complete
add wave -noupdate -divider FSM
add wave -noupdate /cache_bank_tb/dut/wrong_state
add wave -noupdate -group Bank /cache_bank_tb/dut/bank
add wave -noupdate -group Bank /cache_bank_tb/dut/next_bank
add wave -noupdate -group {Cache Controller Logic} /cache_bank_tb/dut/set_index
add wave -noupdate -group {Cache Controller Logic} /cache_bank_tb/dut/hit_way_index
add wave -noupdate -group {FSM State Logic} /cache_bank_tb/dut/latched_block_pull_buffer
add wave -noupdate -group {FSM State Logic} /cache_bank_tb/dut/latched_victim_eject_buffer
add wave -noupdate -group {FSM State Logic} /cache_bank_tb/dut/latched_victim_way_index
add wave -noupdate -group {FSM State Logic} /cache_bank_tb/dut/latched_victim_set_index
add wave -noupdate -group {FSM State Logic} /cache_bank_tb/dut/victim_set_index
add wave -noupdate -group {FSM State Logic} /cache_bank_tb/dut/victim_way_index
add wave -noupdate -group {FSM State Logic} /cache_bank_tb/dut/count_FSM
add wave -noupdate -group {FSM State Logic} /cache_bank_tb/dut/curr_state
add wave -noupdate -group {FSM State Logic} /cache_bank_tb/dut/next_state
add wave -noupdate -group {FSM State Logic} /cache_bank_tb/dut/count_enable
add wave -noupdate -group {FSM State Logic} /cache_bank_tb/dut/count_flush
add wave -noupdate -group {FSM State Logic} /cache_bank_tb/dut/mshr_entry
add wave -noupdate -group {LRU Logic} /cache_bank_tb/dut/lru
add wave -noupdate -group {LRU Logic} -childformat {{{/cache_bank_tb/dut/next_lru[3]} -radix decimal -childformat {{lru_way -radix decimal} {age -radix decimal}}} {{/cache_bank_tb/dut/next_lru[2]} -radix decimal -childformat {{lru_way -radix decimal} {age -radix decimal}}} {{/cache_bank_tb/dut/next_lru[1]} -radix decimal -childformat {{lru_way -radix decimal} {age -radix decimal}}} {{/cache_bank_tb/dut/next_lru[0]} -radix decimal -childformat {{lru_way -radix decimal} {age -radix decimal}}}} -expand -subitemconfig {{/cache_bank_tb/dut/next_lru[3]} {-height 16 -radix decimal -childformat {{lru_way -radix decimal} {age -radix decimal}}} {/cache_bank_tb/dut/next_lru[3].lru_way} {-radix decimal} {/cache_bank_tb/dut/next_lru[3].age} {-radix decimal} {/cache_bank_tb/dut/next_lru[2]} {-height 16 -radix decimal -childformat {{lru_way -radix decimal} {age -radix decimal}}} {/cache_bank_tb/dut/next_lru[2].lru_way} {-radix decimal} {/cache_bank_tb/dut/next_lru[2].age} {-radix decimal} {/cache_bank_tb/dut/next_lru[1]} {-height 16 -radix decimal -childformat {{lru_way -radix decimal} {age -radix decimal}}} {/cache_bank_tb/dut/next_lru[1].lru_way} {-radix decimal} {/cache_bank_tb/dut/next_lru[1].age} {-radix decimal} {/cache_bank_tb/dut/next_lru[0]} {-height 16 -radix decimal -childformat {{lru_way -radix decimal} {age -radix decimal}}} {/cache_bank_tb/dut/next_lru[0].lru_way} {-radix decimal} {/cache_bank_tb/dut/next_lru[0].age} {-radix decimal}} /cache_bank_tb/dut/next_lru
add wave -noupdate -group {LRU Logic} /cache_bank_tb/dut/max_age
add wave -noupdate -group {LRU Logic} /cache_bank_tb/dut/max_way
add wave -noupdate -group {LRU Logic} /cache_bank_tb/dut/latched_victim_way_index
add wave -noupdate -group {LRU Logic} /cache_bank_tb/dut/latched_victim_set_index
add wave -noupdate -group {LRU Logic} /cache_bank_tb/dut/hit_way_index
add wave -noupdate -group {LRU Logic} /cache_bank_tb/dut/set_index
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {329 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 228
configure wave -valuecolwidth 88
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
WaveRestoreZoom {2 ps} {879 ps}
