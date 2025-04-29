onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /dram_cmd_dimm_tb/CLK
add wave -noupdate /dram_cmd_dimm_tb/CLKx2
add wave -noupdate /dram_cmd_dimm_tb/nRST
add wave -noupdate /dram_cmd_dimm_tb/task_name
add wave -noupdate /dram_cmd_dimm_tb/task_name
add wave -noupdate /dram_cmd_dimm_tb/ramaddr_phy
add wave -noupdate /dram_cmd_dimm_tb/ramaddr_phy_ft
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/CK
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/ACT_n
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/RAS_n_A16
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/CAS_n_A15
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/WE_n_A14
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/ALERT_n
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/PARITY
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/RESET_n
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/TEN
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/CS_n
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/CKE
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/ODT
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/C
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/BG
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/BA
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/ADDR
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/ADDR_17
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/DM_n
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/DQ
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/DQS_t
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/DQS_c
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/ZQ
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/PWR
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/VREF_CA
add wave -noupdate -group iDDR4_1 /dram_cmd_dimm_tb/iDDR4_1/VREF_DQ
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/CK
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/ACT_n
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/RAS_n_A16
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/CAS_n_A15
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/WE_n_A14
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/ALERT_n
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/PARITY
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/RESET_n
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/TEN
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/CS_n
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/CKE
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/ODT
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/C
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/BG
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/BA
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/ADDR
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/ADDR_17
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/DM_n
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/DQ
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/DQS_t
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/DQS_c
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/ZQ
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/PWR
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/VREF_CA
add wave -noupdate -group iDDR4_2 /dram_cmd_dimm_tb/iDDR4_2/VREF_DQ
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/CK
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/ACT_n
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/RAS_n_A16
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/CAS_n_A15
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/WE_n_A14
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/ALERT_n
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/PARITY
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/RESET_n
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/TEN
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/CS_n
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/CKE
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/ODT
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/C
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/BG
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/BA
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/ADDR
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/ADDR_17
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/DM_n
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/DQ
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/DQS_t
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/DQS_c
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/ZQ
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/PWR
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/VREF_CA
add wave -noupdate -group iDDR4_3 /dram_cmd_dimm_tb/iDDR4_3/VREF_DQ
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/CK
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/ACT_n
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/RAS_n_A16
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/CAS_n_A15
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/WE_n_A14
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/ALERT_n
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/PARITY
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/RESET_n
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/TEN
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/CS_n
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/CKE
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/ODT
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/C
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/BG
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/BA
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/ADDR
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/ADDR_17
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/DM_n
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/DQ
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/DQS_t
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/DQS_c
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/ZQ
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/PWR
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/VREF_CA
add wave -noupdate -expand -group iDDR4_4 /dram_cmd_dimm_tb/iDDR4_4/VREF_DQ
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/CK
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/ACT_n
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/RAS_n_A16
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/CAS_n_A15
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/WE_n_A14
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/ALERT_n
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/PARITY
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/RESET_n
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/TEN
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/CS_n
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/CKE
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/ODT
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/C
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/BG
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/BA
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/ADDR
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/ADDR_17
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/DM_n
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/DQ
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/DQS_t
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/DQS_c
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/ZQ
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/PWR
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/VREF_CA
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/VREF_DQ
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/Ra0
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/Ra1
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/BA0
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/BA1
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/R0
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/R1
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/COL0
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/COL1
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/BG0
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/BG1
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/ramREN_curr
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/ramWEN_curr
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/ramREN_ftrt
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/ramWEN_ftrt
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/data_callback
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/write_data
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/request_done
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/wr_en
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/rd_en
add wave -noupdate -expand -group DRAM_CMD -group dc_if /dram_cmd_dimm_tb/dc_if/REFRESH
add wave -noupdate -expand -group DRAM_CMD /dram_cmd_dimm_tb/DUT/state
add wave -noupdate -expand -group DRAM_CMD /dram_cmd_dimm_tb/DUT/n_state
add wave -noupdate -expand -group DRAM_CMD /dram_cmd_dimm_tb/DUT/rollover_value
add wave -noupdate -expand -group DRAM_CMD /dram_cmd_dimm_tb/DUT/timing_count
add wave -noupdate -expand -group DRAM_CMD /dram_cmd_dimm_tb/DUT/n_timing_count
add wave -noupdate -expand -group DRAM_CMD /dram_cmd_dimm_tb/DUT/cmd_addr
add wave -noupdate -expand -group DRAM_CMD /dram_cmd_dimm_tb/DUT/count_act
add wave -noupdate -expand -group DRAM_CMD /dram_cmd_dimm_tb/DUT/n_count_act
add wave -noupdate -expand -group DRAM_CMD /dram_cmd_dimm_tb/DUT/act_not_5
add wave -noupdate -expand -group DRAM_CMD /dram_cmd_dimm_tb/DUT/issue_cmd
add wave -noupdate -expand -group DRAM_CMD /dram_cmd_dimm_tb/DUT/time_bug
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/WORD_W
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/dREN
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/dWEN
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/request_done
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/ramaddr
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/memstore
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/ramaddr_rq
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/ramstore_rq
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/ramaddr_rq_ft
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/ramstore_rq_ft
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/memaddr_callback
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/iwait
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/dwait
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/ramREN_curr
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/ramREN_ftrt
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/ramWEN_curr
add wave -noupdate -expand -group Scheduler_buffer_if /dram_cmd_dimm_tb/sch_if/ramWEN_ftrt
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/dt_if/WORD_W
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/dt_if/wr_en
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/dt_if/rd_en
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/dt_if/clear
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/dt_if/DM_n
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/dt_if/memstore
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/dt_if/memload
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/dt_if/COL_choice
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/dt_if/DQ
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/dt_if/DQS_t
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/dt_if/DQS_c
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/DQ_up
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/count_burst
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/ncount_burst
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/cnt1
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/wr_en1
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/wr_en2
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/select_low
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/DQS_t_1
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/DQS_t_2
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/nDQS_t
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/edge_flag
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/COL_choice_tr
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/D_in
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/D_out
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/D_mux
add wave -noupdate -expand -group Data_transfer_if /dram_cmd_dimm_tb/DT/word_register
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {3414538 ps} 0}
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
WaveRestoreZoom {3403037 ps} {3427734 ps}
