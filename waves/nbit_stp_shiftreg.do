onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /nbit_stp_shiftreg_tb/PERIOD
add wave -noupdate /nbit_stp_shiftreg_tb/casename
add wave -noupdate /nbit_stp_shiftreg_tb/CLK
add wave -noupdate /nbit_stp_shiftreg_tb/nRST
add wave -noupdate /nbit_stp_shiftreg_tb/enable
add wave -noupdate /nbit_stp_shiftreg_tb/in
add wave -noupdate -radix binary /nbit_stp_shiftreg_tb/out
add wave -noupdate /nbit_stp_shiftreg_tb/casenum
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {19270 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 276
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
WaveRestoreZoom {12080 ps} {20420 ps}
