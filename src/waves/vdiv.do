onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /vdiv_tb/tb_test_case
add wave -noupdate /vdiv_tb/CLK
add wave -noupdate /vdiv_tb/nRST
add wave -noupdate -expand -group Inputs -color Cyan /vdiv_tb/divif/a
add wave -noupdate -expand -group Inputs -color Cyan /vdiv_tb/divif/b
add wave -noupdate -expand -group Inputs -color Cyan /vdiv_tb/divif/en
add wave -noupdate -expand -group Outputs -color Cyan /vdiv_tb/divif/done
add wave -noupdate -expand -group Outputs -color Cyan /vdiv_tb/divif/result
add wave -noupdate -expand -group {Expected Outputs} /vdiv_tb/expected_result
add wave -noupdate /vdiv_tb/errors
add wave -noupdate -expand -group {Internal Signals} -expand -group {Intermediate Results} -color Yellow /vdiv_tb/DUT/quotient
add wave -noupdate -expand -group {Internal Signals} -expand -group {Intermediate Results} -color Yellow /vdiv_tb/DUT/mant
add wave -noupdate -expand -group {Internal Signals} -expand -group {Intermediate Results} -color Yellow -radix decimal /vdiv_tb/DUT/exp
add wave -noupdate -expand -group {Internal Signals} -expand -group {Intermediate Results} -color Yellow /vdiv_tb/DUT/shift_amt
add wave -noupdate -expand -group {Internal Signals} -expand -group {Intermediate Results} -color Yellow /vdiv_tb/DUT/exp_norm
add wave -noupdate -expand -group {Internal Signals} -expand -group {Edge Case Signals} -color Magenta /vdiv_tb/DUT/is_ovf
add wave -noupdate -expand -group {Internal Signals} -expand -group {Edge Case Signals} -color Magenta /vdiv_tb/DUT/is_nan
add wave -noupdate -expand -group {Internal Signals} -expand -group {Edge Case Signals} -color Magenta /vdiv_tb/DUT/is_inf
add wave -noupdate -expand -group {Internal Signals} -expand -group {Edge Case Signals} -color Magenta /vdiv_tb/DUT/is_zero
add wave -noupdate /vdiv_tb/DUT/divider/n
add wave -noupdate /vdiv_tb/DUT/done_pulsed
add wave -noupdate /vdiv_tb/DUT/skip_divider
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {3400084 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 190
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
WaveRestoreZoom {3399953 ns} {3400301 ns}
