onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand /masku_tb/vif/masku_in
add wave -noupdate -expand /masku_tb/vif/masku_out
add wave -noupdate /masku_tb/#ublk#144880018#13/testname
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {8 ns} 0}
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
WaveRestoreZoom {0 ns} {19 ns}
