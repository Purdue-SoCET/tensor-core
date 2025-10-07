onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /sqrt_tb/CLK
add wave -noupdate /sqrt_tb/nRST
add wave -noupdate /sqrt_tb/dut/valid_data_in
add wave -noupdate /sqrt_tb/dut/is_subnormal
add wave -noupdate -expand -group decomp /sqrt_tb/dut/input_val
add wave -noupdate -expand -group decomp -expand -group {decomp of input} /sqrt_tb/dut/sign
add wave -noupdate -expand -group decomp -expand -group {decomp of input} /sqrt_tb/dut/exponent
add wave -noupdate -expand -group decomp -expand -group {decomp of input} /sqrt_tb/dut/mantissa
add wave -noupdate -expand -group decomp /sqrt_tb/dut/input_slope
add wave -noupdate -expand -group decomp /sqrt_tb/dut/input_intercept
add wave -noupdate -expand -group decomp /sqrt_tb/dut/normalized_mantissa
add wave -noupdate -expand -group decomp /sqrt_tb/dut/index
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {57568 ps} 0}
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
WaveRestoreZoom {0 ps} {320250 ps}
