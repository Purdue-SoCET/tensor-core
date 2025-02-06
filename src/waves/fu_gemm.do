onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /fu_gemm_tb/fugif/fetch_p
add wave -noupdate /fu_gemm_tb/fugif/rs1
add wave -noupdate /fu_gemm_tb/fugif/rs2
add wave -noupdate /fu_gemm_tb/fugif/rs3
add wave -noupdate /fu_gemm_tb/fugif/rd
add wave -noupdate /fu_gemm_tb/fugif/flush
add wave -noupdate /fu_gemm_tb/fugif/freeze
add wave -noupdate /fu_gemm_tb/DUT/next_reg1
add wave -noupdate /fu_gemm_tb/DUT/next_reg2
add wave -noupdate /fu_gemm_tb/DUT/next_reg3
add wave -noupdate /fu_gemm_tb/DUT/next_regd
add wave -noupdate /fu_gemm_tb/DUT/ready
add wave -noupdate /fu_gemm_tb/DUT/next_ready
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
configure wave -namecolwidth 150
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
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {1 ns}
