onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /vaddsub_tb/DUT/CLK
add wave -noupdate /vaddsub_tb/DUT/nRST
add wave -noupdate /vaddsub_tb/casenum
add wave -noupdate /vaddsub_tb/casename
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/fp1
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/fp2
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/sign_r
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/overflow
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/exp_a
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/exp_b
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/exp_r
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/exp_diff
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/frac_a_ext
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/frac_b_ext
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/frac_sum
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/sign_a
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix binary /vaddsub_tb/DUT/sign_b
add wave -noupdate -expand -group {VAddSub Signals} -color Yellow -radix binary /vaddsub_tb/vaddsubif/port_a
add wave -noupdate -expand -group {VAddSub Signals} -color Yellow -radix binary /vaddsub_tb/vaddsubif/port_b
add wave -noupdate -expand -group {VAddSub Signals} -color Yellow -radix binary /vaddsub_tb/vaddsubif/out
add wave -noupdate -expand -group {VAddSub Signals} -color Yellow -radix binary /vaddsub_tb/vaddsubif/sub
add wave -noupdate -expand -group {VAddSub Signals} -color Yellow -radix binary /vaddsub_tb/vaddsubif/enable
add wave -noupdate -expand -group {VAddSub Signals} -color Yellow -radix binary /vaddsub_tb/vaddsubif/overflow
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
quietly wave cursor active 0
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
