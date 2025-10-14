onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /vbank_tb/dut/clk
add wave -noupdate /vbank_tb/dut/ren
add wave -noupdate /vbank_tb/dut/raddr
add wave -noupdate /vbank_tb/dut/rdata
add wave -noupdate /vbank_tb/dut/wen
add wave -noupdate /vbank_tb/dut/waddr
add wave -noupdate /vbank_tb/dut/wdata
add wave -noupdate /vbank_tb/dut/wstrb
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {420 ns} 0}
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
