onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand /masku_tb/vif/masku_in
add wave -noupdate /masku_tb/#ublk#144880018#43/test_case
add wave -noupdate -expand /masku_tb/vif/masku_out
add wave -noupdate -divider DUT
add wave -noupdate /masku_tb/dut/vif/masku_in
add wave -noupdate /masku_tb/dut/vif/masku_out
add wave -noupdate /masku_tb/dut/vmask
add wave -noupdate /masku_tb/dut/vmask
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {92 ps} 0}
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
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {105 ps}
