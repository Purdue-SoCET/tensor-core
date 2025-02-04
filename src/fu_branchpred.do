onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -color Salmon /fu_branchpred_tb/tb_test_case
add wave -noupdate -expand -group Inputs /fu_branchpred_tb/fubpif/pc
add wave -noupdate -expand -group Inputs /fu_branchpred_tb/fubpif/update_pc
add wave -noupdate -expand -group Inputs /fu_branchpred_tb/fubpif/update_btb
add wave -noupdate -expand -group Inputs /fu_branchpred_tb/fubpif/branch_outcome
add wave -noupdate -expand -group Inputs /fu_branchpred_tb/fubpif/branch_target
add wave -noupdate -expand -group Outputs /fu_branchpred_tb/fubpif/predicted_outcome
add wave -noupdate -expand -group Outputs /fu_branchpred_tb/fubpif/predicted_target
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {84880 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 142
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
WaveRestoreZoom {0 ps} {120390 ps}
