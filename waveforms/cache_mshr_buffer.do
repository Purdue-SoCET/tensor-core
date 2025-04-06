onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /cache_mshr_buffer_tb/buffer/CLK
add wave -noupdate /cache_mshr_buffer_tb/buffer/nRST
add wave -noupdate -divider Testbench
add wave -noupdate /cache_mshr_buffer_tb/PROG/tb_miss
add wave -noupdate /cache_mshr_buffer_tb/PROG/tb_mem_instr
add wave -noupdate /cache_mshr_buffer_tb/PROG/tb_bank_empty
add wave -noupdate /cache_mshr_buffer_tb/PROG/tb_mem_out_uuid
add wave -noupdate /cache_mshr_buffer_tb/PROG/tb_mshr_out
add wave -noupdate /cache_mshr_buffer_tb/PROG/tb_stall
add wave -noupdate -divider Design
add wave -noupdate /cache_mshr_buffer_tb/buffer/miss
add wave -noupdate /cache_mshr_buffer_tb/buffer/mem_instr
add wave -noupdate /cache_mshr_buffer_tb/buffer/bank_empty
add wave -noupdate /cache_mshr_buffer_tb/buffer/mshr_out
add wave -noupdate /cache_mshr_buffer_tb/buffer/stall
add wave -noupdate /cache_mshr_buffer_tb/buffer/uuid_out
add wave -noupdate /cache_mshr_buffer_tb/buffer/buffer
add wave -noupdate /cache_mshr_buffer_tb/buffer/next_buffer
add wave -noupdate /cache_mshr_buffer_tb/buffer/buffer_copy
add wave -noupdate /cache_mshr_buffer_tb/buffer/secondary_misses
add wave -noupdate /cache_mshr_buffer_tb/buffer/mshr_new_miss
add wave -noupdate /cache_mshr_buffer_tb/buffer/uuid
add wave -noupdate /cache_mshr_buffer_tb/buffer/next_uuid
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
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
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ps} {1 ns}
