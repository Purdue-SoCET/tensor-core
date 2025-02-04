onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -color Salmon /fu_branch_tb/tb_test_case
add wave -noupdate -expand -group Inputs -color Cyan /fu_branch_tb/DUT/fubif/branch
add wave -noupdate -expand -group Inputs -color Cyan /fu_branch_tb/DUT/fubif/branch_gate_sel
add wave -noupdate -expand -group Inputs -color Cyan /fu_branch_tb/DUT/fubif/branch_type
add wave -noupdate -expand -group Inputs -color Cyan /fu_branch_tb/DUT/fubif/reg_a
add wave -noupdate -expand -group Inputs -color Cyan /fu_branch_tb/DUT/fubif/reg_b
add wave -noupdate -expand -group Inputs -color Cyan /fu_branch_tb/DUT/fubif/current_pc
add wave -noupdate -expand -group Inputs -color Cyan /fu_branch_tb/DUT/fubif/imm
add wave -noupdate -expand -group Outputs -color {Medium Slate Blue} /fu_branch_tb/DUT/fubif/branch_outcome
add wave -noupdate -expand -group Outputs -color {Medium Slate Blue} /fu_branch_tb/DUT/fubif/updated_pc
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {60400 ps} 0}
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
WaveRestoreZoom {55070 ps} {180260 ps}
