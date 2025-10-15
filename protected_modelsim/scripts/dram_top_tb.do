onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /dram_top_tb/CLK
add wave -noupdate /dram_top_tb/nRST
add wave -noupdate /dram_top_tb/CLKx2
add wave -noupdate /dram_top_tb/task_name
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/CONFIGURED_DQ_BITS
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/CONFIGURED_DQS_BITS
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/CONFIGURED_DM_BITS
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/CK
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/ACT_n
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/RAS_n_A16
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/CAS_n_A15
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/WE_n_A14
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/ALERT_n
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/PARITY
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/RESET_n
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/TEN
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/CS_n
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/CKE
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/ODT
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/C
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/BG
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/BA
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/ADDR
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/ADDR_17
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/DM_n
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/DQ
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/DQS_t
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/DQS_c
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/ZQ
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/PWR
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/VREF_CA
add wave -noupdate -group DRAM_1 /dram_top_tb/iDDR4_1/VREF_DQ
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/CONFIGURED_DQ_BITS
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/CONFIGURED_DQS_BITS
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/CONFIGURED_DM_BITS
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/CK
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/ACT_n
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/RAS_n_A16
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/CAS_n_A15
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/WE_n_A14
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/ALERT_n
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/PARITY
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/RESET_n
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/TEN
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/CS_n
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/CKE
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/ODT
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/C
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/BG
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/BA
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/ADDR
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/ADDR_17
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/DM_n
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/DQ
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/DQS_t
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/DQS_c
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/ZQ
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/PWR
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/VREF_CA
add wave -noupdate -group DRAM_2 /dram_top_tb/iDDR4_2/VREF_DQ
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/CONFIGURED_DQ_BITS
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/CONFIGURED_DQS_BITS
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/CONFIGURED_DM_BITS
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/CK
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/ACT_n
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/RAS_n_A16
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/CAS_n_A15
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/WE_n_A14
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/ALERT_n
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/PARITY
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/RESET_n
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/TEN
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/CS_n
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/CKE
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/ODT
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/C
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/BG
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/BA
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/ADDR
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/ADDR_17
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/DM_n
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/DQ
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/DQS_t
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/DQS_c
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/ZQ
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/PWR
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/VREF_CA
add wave -noupdate -group DRAM_3 /dram_top_tb/iDDR4_3/VREF_DQ
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/CONFIGURED_DQ_BITS
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/CONFIGURED_DQS_BITS
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/CONFIGURED_DM_BITS
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/CK
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/ACT_n
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/RAS_n_A16
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/CAS_n_A15
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/WE_n_A14
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/ALERT_n
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/PARITY
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/RESET_n
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/TEN
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/CS_n
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/CKE
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/ODT
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/C
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/BG
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/BA
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/ADDR
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/ADDR_17
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/DM_n
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/DQ
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/DQS_t
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/DQS_c
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/ZQ
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/PWR
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/VREF_CA
add wave -noupdate -expand -group DRAM_4 /dram_top_tb/iDDR4_4/VREF_DQ
add wave -noupdate -expand -group control_arb /dram_top_tb/DUT/myctrl/dWEN
add wave -noupdate -expand -group control_arb /dram_top_tb/DUT/myctrl/dREN
add wave -noupdate -expand -group control_arb /dram_top_tb/DUT/myctrl/ram_wait
add wave -noupdate -expand -group control_arb /dram_top_tb/DUT/myctrl/ram_addr
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/address
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/configs
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/rank
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/BG
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/bank
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/row
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/col
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/offset
add wave -noupdate -group init_state /dram_top_tb/DUT/ctrl/myinit/init
add wave -noupdate -group init_state /dram_top_tb/DUT/ctrl/myinit/init_done
add wave -noupdate -group init_state /dram_top_tb/DUT/ctrl/myinit/init_state
add wave -noupdate -group init_state /dram_top_tb/DUT/ctrl/myinit/ninit_state
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/RA0
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/BG0
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/BA0
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/R0
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/C0
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/ACT_n
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/RAS_n_A16
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/CAS_n_A15
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/WE_n_A14
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/ALERT_n
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/PARITY
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/RESET_n
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/TEN
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/CS_n
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/CKE
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/ODT
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/ZQ
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/PWR
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/VREF_CA
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/VREF_DQ
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/C
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/BG
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/BA
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/ADDR
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/ADDR_17
add wave -noupdate -group signal_gen /dram_top_tb/DUT/sig_gen/cmd_addr
add wave -noupdate -group signal_gen /dram_top_tb/DUT/sig_gen/issue
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/ref_re
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/state
add wave -noupdate -group signal_gen /dram_top_tb/DUT/mysig/nstate
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/dREN
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/dWEN
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/init_done
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/init_req
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/tACT_done
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/tWR_done
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/tRD_done
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/tPRE_done
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/tREF_done
add wave -noupdate -group cmd_FSM -color Magenta /dram_top_tb/DUT/ctrl/mycmd/rf_req
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/row_stat
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/ram_wait
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/row_resolve
add wave -noupdate -group cmd_FSM /dram_top_tb/task_name
add wave -noupdate -group cmd_FSM -color Cyan /dram_top_tb/DUT/ctrl/mycmd/cmd_state
add wave -noupdate -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/ncmd_state
add wave -noupdate -group row_policy -color Orange /dram_top_tb/DUT/ctrl/myrow/row
add wave -noupdate -group row_policy -color Orange /dram_top_tb/DUT/ctrl/myrow/bank
add wave -noupdate -group row_policy -color Orange /dram_top_tb/DUT/ctrl/myrow/bank_group
add wave -noupdate -group row_policy -color Orange /dram_top_tb/DUT/ctrl/myrow/row_conflict
add wave -noupdate -group row_policy /dram_top_tb/DUT/ctrl/myrow/req_en
add wave -noupdate -group row_policy /dram_top_tb/DUT/ctrl/myrow/refresh
add wave -noupdate -group row_policy /dram_top_tb/DUT/ctrl/myrow/row_resolve
add wave -noupdate -group row_policy /dram_top_tb/DUT/ctrl/myrow/row_stat
add wave -noupdate -group row_policy /dram_top_tb/DUT/ctrl/u1/row_open_cnt
add wave -noupdate -group row_policy /dram_top_tb/DUT/ctrl/myrow/all_row_closed
add wave -noupdate /dram_top_tb/DUT/ctrl/u1/ptr
add wave -noupdate /dram_top_tb/DUT/ctrl/u1/reg_f
add wave -noupdate -group time_signal /dram_top_tb/DUT/ctrl/mytime/tACT_done
add wave -noupdate -group time_signal /dram_top_tb/DUT/ctrl/mytime/tWR_done
add wave -noupdate -group time_signal /dram_top_tb/DUT/ctrl/mytime/tRD_done
add wave -noupdate -group time_signal /dram_top_tb/DUT/ctrl/mytime/tPRE_done
add wave -noupdate -group time_signal -divider refresh
add wave -noupdate -group time_signal /dram_top_tb/DUT/ctrl/mytime/tREF_done
add wave -noupdate -group time_signal /dram_top_tb/DUT/ctrl/mytime/rf_req
add wave -noupdate -group time_signal -radix unsigned /dram_top_tb/DUT/ctrl/u4/refresh_limit
add wave -noupdate -group time_signal -radix decimal /dram_top_tb/DUT/ctrl/u4/refresh_count
add wave -noupdate -group time_signal -divider timing_trk
add wave -noupdate -group time_signal /dram_top_tb/DUT/ctrl/u4/time_load
add wave -noupdate -group time_signal -radix decimal /dram_top_tb/DUT/ctrl/u4/time_count
add wave -noupdate -group time_signal /dram_top_tb/DUT/ctrl/u4/time_counter_en
add wave -noupdate -group time_signal /dram_top_tb/DUT/ctrl/u4/time_count_done
add wave -noupdate -group Scheduler_buff /dram_top_tb/sch_if/dREN
add wave -noupdate -group Scheduler_buff /dram_top_tb/sch_if/dWEN
add wave -noupdate -group Scheduler_buff -radix binary /dram_top_tb/sch_if/ramaddr
add wave -noupdate -group Scheduler_buff /dram_top_tb/sch_if/ramaddr_rq
add wave -noupdate -group Scheduler_buff /dram_top_tb/sch_if/ramREN_curr
add wave -noupdate -group Scheduler_buff /dram_top_tb/sch_if/ramWEN_curr
add wave -noupdate -group Scheduler_buff /dram_top_tb/SCH_BUFF/fifo
add wave -noupdate -group Scheduler_buff /dram_top_tb/SCH_BUFF/wptr
add wave -noupdate -group Scheduler_buff /dram_top_tb/SCH_BUFF/rptr
add wave -noupdate -expand -group data_transfer /dram_top_tb/dt_if/wr_en
add wave -noupdate -expand -group data_transfer /dram_top_tb/dt_if/rd_en
add wave -noupdate -expand -group data_transfer /dram_top_tb/dt_if/COL_choice
add wave -noupdate -expand -group data_transfer /dram_top_tb/dt_if/DQ
add wave -noupdate -expand -group data_transfer /dram_top_tb/dt_if/DQS_t
add wave -noupdate -expand -group data_transfer /dram_top_tb/dt_if/DQS_c
add wave -noupdate -expand -group data_transfer /dram_top_tb/dt_if/DM_n
add wave -noupdate -expand -group data_transfer /dram_top_tb/DT/count_burst
add wave -noupdate -expand -group data_transfer /dram_top_tb/dt_if/edge_flag
add wave -noupdate -expand -group data_transfer /dram_top_tb/dt_if/memload
add wave -noupdate -expand -group data_transfer /dram_top_tb/dt_if/COL_choice
add wave -noupdate -expand -group cache_debug /dram_top_tb/CACHE/wr_en
add wave -noupdate -expand -group cache_debug /dram_top_tb/CACHE/rd_en
add wave -noupdate -expand -group cache_debug /dram_top_tb/CACHE/row_addr
add wave -noupdate -expand -group cache_debug /dram_top_tb/CACHE/offset
add wave -noupdate -expand -group cache_debug /dram_top_tb/CACHE/dmemstore
add wave -noupdate -expand -group cache_debug /dram_top_tb/dt_if/DQ
add wave -noupdate -expand -group cache_debug /dram_top_tb/CACHE/dmemload
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {3565061 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 369
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
WaveRestoreZoom {0 ps} {3851663 ps}
