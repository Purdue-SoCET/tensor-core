onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /sqrt_tb/CLK
add wave -noupdate /sqrt_tb/nRST
add wave -noupdate /sqrt_tb/srif/ready
add wave -noupdate -expand -group {registered values} /sqrt_tb/dut/sign
add wave -noupdate -expand -group {registered values} /sqrt_tb/dut/exp
add wave -noupdate -expand -group {registered values} /sqrt_tb/dut/frac
add wave -noupdate -expand -group {registered values} /sqrt_tb/dut/slope
add wave -noupdate -expand -group {registered values} /sqrt_tb/dut/intercept
add wave -noupdate -expand -group {registered values} /sqrt_tb/dut/valid
add wave -noupdate -expand -group {mult signals} /sqrt_tb/dut/mul_done
add wave -noupdate -expand -group {mult signals} /sqrt_tb/dut/mul_start
add wave -noupdate -expand -group {mult signals} /sqrt_tb/dut/mul_a
add wave -noupdate -expand -group {mult signals} /sqrt_tb/dut/mul_b
add wave -noupdate -expand -group {mult signals} /sqrt_tb/dut/mul_out
add wave -noupdate -expand -group adder /sqrt_tb/dut/asif/port_a
add wave -noupdate -expand -group adder /sqrt_tb/dut/asif/port_b
add wave -noupdate -expand -group adder /sqrt_tb/dut/asif/out
add wave -noupdate -expand -group adder {/sqrt_tb/dut/adder_valid_shift[1]}
add wave -noupdate -expand -group adder /sqrt_tb/dut/adder_out_reg
add wave -noupdate -expand -group adder /sqrt_tb/dut/asif/enable
add wave -noupdate -expand -group {second mult} /sqrt_tb/dut/second_pass
add wave -noupdate -expand -group {second mult} /sqrt_tb/dut/mul_done
add wave -noupdate -expand -group {third mult} /sqrt_tb/dut/third_pass
add wave -noupdate -expand -group {third mult} /sqrt_tb/dut/second_mult_latched
add wave -noupdate -expand -group {third mult} /sqrt_tb/dut/exp_biased
add wave -noupdate -expand -group {third mult} /sqrt_tb/dut/mul_done
add wave -noupdate -expand -group {third mult} /sqrt_tb/dut/third_mult_result
add wave -noupdate -expand -group {output signals} /sqrt_tb/srif/output_val
add wave -noupdate -expand -group {output signals} /sqrt_tb/srif/valid_data_out
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {925000 ps} 0}
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
WaveRestoreZoom {0 ps} {1790250 ps}
