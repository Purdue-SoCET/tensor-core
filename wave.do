onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /lockup_free_cache_tb/tb_clk
add wave -noupdate /lockup_free_cache_tb/tb_nrst
add wave -noupdate {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/secondary_misses}
add wave -noupdate -expand {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/buffer}
add wave -noupdate {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/mshr_out}
add wave -noupdate {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/mshr_buffer_i/bank_empty}
add wave -noupdate {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/curr_state}
add wave -noupdate {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/count_FSM}
add wave -noupdate {/lockup_free_cache_tb/u_lockup_free_cache/BANK_GEN[0]/u_cache_bank/ram_mem_complete}
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {16 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ps} {56 ps}
