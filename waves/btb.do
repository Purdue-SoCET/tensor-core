onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /btb_tb/PERIOD
add wave -noupdate /btb_tb/CLK
add wave -noupdate /btb_tb/nRST
add wave -noupdate /btb_tb/casenum
add wave -noupdate /btb_tb/casename
add wave -noupdate /btb_tb/DUT/btb
add wave -noupdate -expand -group Inputs /btb_tb/btbif/pc_res
add wave -noupdate -expand -group Inputs /btb_tb/btbif/bt_res
add wave -noupdate -expand -group Inputs /btb_tb/btbif/enable_res
add wave -noupdate -expand -group Inputs /btb_tb/btbif/pc_fetch
add wave -noupdate -expand -group Outputs /btb_tb/btbif/bt_fetch
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1023490 ps} 0}
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
WaveRestoreZoom {1022500 ps} {1032500 ps}
