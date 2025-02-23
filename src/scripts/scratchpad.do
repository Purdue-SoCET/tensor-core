onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /scratchpad_tb/spif/instrFIFO_WEN
add wave -noupdate /scratchpad_tb/spif/psumout_en
add wave -noupdate /scratchpad_tb/spif/drained
add wave -noupdate /scratchpad_tb/spif/fifo_has_space
add wave -noupdate /scratchpad_tb/spif/sLoad_hit
add wave -noupdate /scratchpad_tb/spif/sStore_hit
add wave -noupdate /scratchpad_tb/spif/instrFIFO_wdata
add wave -noupdate /scratchpad_tb/spif/psumout_row_sel_in
add wave -noupdate /scratchpad_tb/spif/sLoad_row
add wave -noupdate /scratchpad_tb/spif/psumout_data
add wave -noupdate /scratchpad_tb/spif/load_data
add wave -noupdate /scratchpad_tb/spif/instrFIFO_full
add wave -noupdate /scratchpad_tb/spif/partial_enable
add wave -noupdate /scratchpad_tb/spif/weight_enable
add wave -noupdate /scratchpad_tb/spif/input_enable
add wave -noupdate /scratchpad_tb/spif/sLoad
add wave -noupdate /scratchpad_tb/spif/sStore
add wave -noupdate /scratchpad_tb/spif/gemm_complete
add wave -noupdate /scratchpad_tb/spif/weight_input_data
add wave -noupdate /scratchpad_tb/spif/partial_sum_data
add wave -noupdate /scratchpad_tb/spif/store_data
add wave -noupdate /scratchpad_tb/spif/weight_input_row_sel
add wave -noupdate /scratchpad_tb/spif/partial_sum_row_sel
add wave -noupdate /scratchpad_tb/spif/load_addr
add wave -noupdate /scratchpad_tb/spif/store_addr
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
quietly wave cursor active 0
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
WaveRestoreZoom {0 ns} {1 us}
