onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /vreduction_tb/CLK
add wave -noupdate /vreduction_tb/nRST
add wave -noupdate -expand -group {after tree before output} /vreduction_tb/dut/tree_data_out
add wave -noupdate -expand -group {after tree before output} /vreduction_tb/dut/tree_valid_out
add wave -noupdate -expand -group {after tree before output} /vreduction_tb/dut/imm_final
add wave -noupdate -expand -group {after tree before output} /vreduction_tb/dut/broadcast_final
add wave -noupdate -expand -group {after tree before output} /vreduction_tb/dut/clear_final
add wave -noupdate -expand -group {after tree before output} {/vreduction_tb/dut/vector_pipe[4]}
add wave -noupdate -expand -group {tree inputs} /vreduction_tb/vruif/lane_input
add wave -noupdate -expand -group {tree inputs} /vreduction_tb/vruif/input_valid
add wave -noupdate -expand -group {tree inputs} /vreduction_tb/dut/tree_data_in
add wave -noupdate -expand -group outputs /vreduction_tb/vruif/output_valid
add wave -noupdate -expand -group outputs /vreduction_tb/vruif/vector_output
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {35 ns} 0}
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
WaveRestoreZoom {19 ns} {99 ns}
