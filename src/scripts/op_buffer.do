onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /op_buffer_tb/dut/CLK
add wave -noupdate /op_buffer_tb/dut/nRST
add wave -noupdate /op_buffer_tb/dut/vmask_tmp
add wave -noupdate /op_buffer_tb/dut/vreg_tmp
add wave -noupdate /op_buffer_tb/dut/dready
add wave -noupdate /op_buffer_tb/dut/mready
add wave -noupdate /op_buffer_tb/#ublk#195706642#31/testname
add wave -noupdate /op_buffer_tb/vif/opbuff_in
add wave -noupdate /op_buffer_tb/vif/opbuff_out
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {62 ns} 0}
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
WaveRestoreZoom {0 ns} {1 us}
