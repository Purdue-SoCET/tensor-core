onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /fu_branch_tb/tb_test_case
add wave -noupdate /fu_branch_tb/tb_clk
add wave -noupdate /fu_branch_tb/tb_nrst
add wave -noupdate /fu_branch_tb/fubif/branch
add wave -noupdate /fu_branch_tb/fubif/branch_gate_sel
add wave -noupdate /fu_branch_tb/fubif/branch_outcome
add wave -noupdate /fu_branch_tb/fubif/branch_type
add wave -noupdate /fu_branch_tb/fubif/reg_a
add wave -noupdate /fu_branch_tb/fubif/reg_b
add wave -noupdate /fu_branch_tb/fubif/current_pc
add wave -noupdate /fu_branch_tb/fubif/imm
add wave -noupdate /fu_branch_tb/fubif/updated_pc
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
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
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {1 ns}
