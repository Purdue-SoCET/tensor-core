onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /vreduction_alu_tb/casename
add wave -noupdate /vreduction_alu_tb/alu_if/value_a
add wave -noupdate /vreduction_alu_tb/alu_if/value_b
add wave -noupdate /vreduction_alu_tb/alu_if/value_out
add wave -noupdate /vreduction_alu_tb/alu_if/alu_op
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {568 ns} 0}
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
WaveRestoreZoom {0 ns} {1 us}
