onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /command_FSM_tb/DUT/CLK
add wave -noupdate /command_FSM_tb/DUT/nRST
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/dREN
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/dWEN
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/init_done
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/init_req
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/tACT_done
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/tWR_done
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/tRD_done
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/tPRE_done
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/tREF_done
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/rf_req
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/row_stat
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/row_resolve
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/cmd_state
add wave -noupdate -expand -group cmd_if /command_FSM_tb/mycmd/ncmd_state
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {7553 ps} 0}
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
WaveRestoreZoom {0 ps} {18113 ps}
