onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /vreduction_tb/CLK
add wave -noupdate /vreduction_tb/nRST
add wave -noupdate /vreduction_tb/dut/level_regs
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
configure wave -timelineunits ps
update
WaveRestoreZoom {144050 ps} {145050 ps}
