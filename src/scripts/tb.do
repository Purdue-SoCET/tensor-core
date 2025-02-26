onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb/tt_timesets
add wave -noupdate /tb/tCK
add wave -noupdate /tb/tOffset
add wave -noupdate /tb/max_tCK
add wave -noupdate /tb/min_tCK
add wave -noupdate /tb/clk_val
add wave -noupdate /tb/clk_enb
add wave -noupdate -radix symbolic /tb/func_str
add wave -noupdate /tb/_dut_config
add wave -noupdate /tb/active_cmd
add wave -noupdate /tb/timing
add wave -noupdate /tb/model_enable
add wave -noupdate /tb/model_enable_val
add wave -noupdate /tb/odt_wire
add wave -noupdate /tb/driving_cmd
add wave -noupdate /tb/dq_en
add wave -noupdate /tb/dqs_en
add wave -noupdate -color Magenta /tb/dq_out
add wave -noupdate /tb/dqs_out
add wave -noupdate /tb/dm_out
add wave -noupdate /tb/dm_fifo
add wave -noupdate /tb/dq_fifo
add wave -noupdate /tb/q0
add wave -noupdate /tb/q1
add wave -noupdate /tb/q2
add wave -noupdate /tb/q3
add wave -noupdate /tb/ptr_rst_n
add wave -noupdate /tb/burst_cntr
add wave -noupdate /tb/odt_out
add wave -noupdate /tb/odt_fifo
add wave -noupdate /tb/_dut_mode_config
add wave -noupdate /tb/load_mode/bg
add wave -noupdate /tb/load_mode/ba
add wave -noupdate /tb/load_mode/addr
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {3239621 ps} 0}
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
configure wave -timelineunits ns
update
WaveRestoreZoom {3096533 ps} {3298387 ps}