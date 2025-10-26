onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /gsau_control_unit_tb/dut/CLK
add wave -noupdate /gsau_control_unit_tb/dut/nRST
add wave -noupdate /gsau_control_unit_tb/test
add wave -noupdate -divider gsau_interface
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/veg_vdata1
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/veg_vdata2
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/veg_valid
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sb_ready
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sb_vdst
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sb_valid
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sb_weight
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/wb_psum
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/wb_wbdst
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/wb_valid
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/wb_output_ready
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sa_array_in
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sa_array_in_partials
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sa_input_en
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sa_weight_en
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sa_partial_en
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sa_array_output
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sa_fifo_has_space
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sa_output_ready
add wave -noupdate /gsau_control_unit_tb/dut/gsau_port/sa_out_valid
add wave -noupdate -divider DUT
add wave -noupdate /gsau_control_unit_tb/dut/VEGGIEREGS
add wave -noupdate /gsau_control_unit_tb/dut/FIFOSIZE
add wave -noupdate /gsau_control_unit_tb/dut/ENTRY_BITS
add wave -noupdate /gsau_control_unit_tb/dut/FIFO_DEPTH
add wave -noupdate /gsau_control_unit_tb/dut/CLK
add wave -noupdate /gsau_control_unit_tb/dut/nRST
add wave -noupdate /gsau_control_unit_tb/dut/fifo_wr
add wave -noupdate /gsau_control_unit_tb/dut/fifo_din
add wave -noupdate /gsau_control_unit_tb/dut/fifo_dout
add wave -noupdate /gsau_control_unit_tb/dut/fifo_empty
add wave -noupdate /gsau_control_unit_tb/dut/fifo_full
add wave -noupdate -divider {systolic model}
add wave -noupdate /gsau_control_unit_tb/systolic_array/valid
add wave -noupdate /gsau_control_unit_tb/systolic_array/data
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {318310 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 137
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
WaveRestoreZoom {70088 ps} {771061 ps}
