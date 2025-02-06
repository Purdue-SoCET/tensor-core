onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /fu_scalar_ls_tb/DUT/CLK
add wave -noupdate /fu_scalar_ls_tb/DUT/nRST
add wave -noupdate -divider {in and out}
add wave -noupdate /fu_scalar_ls_tb/slsif/imm
add wave -noupdate /fu_scalar_ls_tb/slsif/dmemload
add wave -noupdate /fu_scalar_ls_tb/slsif/dmemaddr
add wave -noupdate /fu_scalar_ls_tb/slsif/dmem_in
add wave -noupdate /fu_scalar_ls_tb/slsif/dmemstore
add wave -noupdate /fu_scalar_ls_tb/slsif/rs1
add wave -noupdate /fu_scalar_ls_tb/slsif/rs2
add wave -noupdate /fu_scalar_ls_tb/slsif/mem_type
add wave -noupdate /fu_scalar_ls_tb/slsif/dhit
add wave -noupdate /fu_scalar_ls_tb/slsif/dmemWEN
add wave -noupdate /fu_scalar_ls_tb/slsif/dmemREN
add wave -noupdate /fu_scalar_ls_tb/slsif/dhit_in
add wave -noupdate -divider dut
add wave -noupdate /fu_scalar_ls_tb/DUT/state
add wave -noupdate /fu_scalar_ls_tb/DUT/next_state
add wave -noupdate /fu_scalar_ls_tb/DUT/latched_dmemaddr
add wave -noupdate /fu_scalar_ls_tb/DUT/latched_dmemstore
add wave -noupdate /fu_scalar_ls_tb/DUT/addr
add wave -noupdate /fu_scalar_ls_tb/DUT/latched_dmemREN
add wave -noupdate /fu_scalar_ls_tb/DUT/latched_dmemWEN
add wave -noupdate /fu_scalar_ls_tb/DUT/write
add wave -noupdate /fu_scalar_ls_tb/DUT/read
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {51690 ps} 0}
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
WaveRestoreZoom {0 ps} {161270 ps}
