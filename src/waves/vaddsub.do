onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -label enable /vaddsub_tb/vaddsubif/enable
add wave -noupdate -label nrst /vaddsub_tb/nRST
add wave -noupdate -label clk /vaddsub_tb/CLK
add wave -noupdate -label sub /vaddsub_tb/vaddsubif/sub
add wave -noupdate -label out /vaddsub_tb/vaddsubif/out
add wave -noupdate -label expected /vaddsub_tb/exp
add wave -noupdate -label porta /vaddsub_tb/vaddsubif/port_a
add wave -noupdate -label portb /vaddsub_tb/vaddsubif/port_b
add wave -noupdate -label overflow /vaddsub_tb/vaddsubif/overflow
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {655 ns} 0}
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
WaveRestoreZoom {0 ns} {1061 ns}
