onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /fu_gemm_tb/casenum
add wave -noupdate /fu_gemm_tb/casename
add wave -noupdate /fu_gemm_tb/DUT/CLK
add wave -noupdate /fu_gemm_tb/DUT/nRST
add wave -noupdate -expand -group Inputs /fu_gemm_tb/DUT/fugif/gemm_enable
add wave -noupdate -expand -group Inputs /fu_gemm_tb/DUT/fugif/new_weight_in
add wave -noupdate -expand -group Inputs /fu_gemm_tb/DUT/fugif/rs1_in
add wave -noupdate -expand -group Inputs /fu_gemm_tb/DUT/fugif/rs2_in
add wave -noupdate -expand -group Inputs /fu_gemm_tb/DUT/fugif/rs3_in
add wave -noupdate -expand -group Inputs /fu_gemm_tb/DUT/fugif/rd_in
add wave -noupdate -expand -group Outputs /fu_gemm_tb/DUT/fugif/gemm_matrix_num
add wave -noupdate /fu_gemm_tb/DUT/fugif/new_weight_out
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {3360 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 250
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
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
WaveRestoreZoom {2850 ps} {8600 ps}
