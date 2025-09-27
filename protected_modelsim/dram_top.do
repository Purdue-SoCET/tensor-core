onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group control_arb /dram_top_tb/dc_if/dWEN
add wave -noupdate -expand -group control_arb /dram_top_tb/dc_if/dREN
add wave -noupdate -expand -group control_arb /dram_top_tb/dc_if/ram_wait
add wave -noupdate -expand -group control_arb /dram_top_tb/dc_if/ram_addr
add wave -noupdate -expand -group control_arb /dram_top_tb/dc_if/ramload
add wave -noupdate -expand -group control_arb /dram_top_tb/dc_if/ramstore
add wave -noupdate -expand -group control_arb /dram_top_tb/dc_if/wr_en
add wave -noupdate -expand -group control_arb /dram_top_tb/dc_if/rd_en
add wave -noupdate -expand -group control_arb /dram_top_tb/dc_if/clear
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {50 ps} 0}
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
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {3 ps}
