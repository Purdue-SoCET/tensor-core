onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /dram_command_tb/CLK
add wave -noupdate /dram_command_tb/nRST
add wave -noupdate /dram_command_tb/DUT/state
add wave -noupdate /dram_command_tb/DUT/n_state
add wave -noupdate /dram_command_tb/DUT/rollover_value
add wave -noupdate -radix decimal /dram_command_tb/DUT/timing_count
add wave -noupdate -radix decimal /dram_command_tb/DUT/n_timing_count
add wave -noupdate /dram_command_tb/DUT/count_act
add wave -noupdate /dram_command_tb/DUT/n_count_act
add wave -noupdate /dram_command_tb/DUT/act_not_5
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/ACT_n
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/RAS_n_A16
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/CAS_n_A15
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/WE_n_A14
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/ALERT_n
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/PARITY
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/RESET_n
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/TEN
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/CS_n
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/CKE
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/ODT
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/C
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/BG
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/BA
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/ADDR
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/ADDR_17
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/DM_n
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/DQ
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/DQS_t
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/DQS_c
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/ZQ
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/PWR
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/VREF_CA
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/VREF_DQ
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/Ra0
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/Ra1
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/BA0
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/BA1
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/R0
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/R1
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/COL0
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/COL1
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/BG0
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/BG1
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/dREN_curr
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/dWEN_curr
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/dREN_ftrt
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/dWEN_ftrt
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/data_callback
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/write_data
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/request_done
add wave -noupdate -group Command_dut /dram_command_tb/dc_if/REFRESH
add wave -noupdate /dram_command_tb/DUT/cmd_addr
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/CK
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/CS_n
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/ACT_n
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/RAS_n_A16
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/CAS_n_A15
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/WE_n_A14
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/CKE
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/TEN
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/PARITY
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/ALERT_n
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/RESET_n
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/ZQ
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/PWR
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/VREF_CA
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/VREF_DQ
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/ODT
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/C
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/BG
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/BA
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/ADDR
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/ADDR_17
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/DM_n
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/DQ
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/DQS_t
add wave -noupdate -expand -group iDDR4 /dram_command_tb/iDDR4/DQS_c
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {193250 ps} 0}
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
WaveRestoreZoom {182400 ps} {247087 ps}
