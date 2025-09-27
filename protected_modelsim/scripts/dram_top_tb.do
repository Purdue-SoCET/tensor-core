onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /dram_top_tb/CLK
add wave -noupdate /dram_top_tb/nRST
add wave -noupdate /dram_top_tb/CLKx2
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/CONFIGURED_DQ_BITS
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/CONFIGURED_DQS_BITS
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/CONFIGURED_DM_BITS
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/CK
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/ACT_n
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/RAS_n_A16
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/CAS_n_A15
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/WE_n_A14
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/ALERT_n
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/PARITY
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/RESET_n
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/TEN
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/CS_n
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/CKE
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/ODT
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/C
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/BG
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/BA
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/ADDR
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/ADDR_17
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/DM_n
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/DQ
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/DQS_t
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/DQS_c
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/ZQ
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/PWR
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/VREF_CA
add wave -noupdate -expand -group DRAM_1 /dram_top_tb/iDDR4_1/VREF_DQ
add wave -noupdate -expand -group control_arb /dram_top_tb/DUT/myctrl/dWEN
add wave -noupdate -expand -group control_arb /dram_top_tb/DUT/myctrl/dREN
add wave -noupdate -expand -group control_arb /dram_top_tb/DUT/myctrl/ram_wait
add wave -noupdate -expand -group control_arb /dram_top_tb/DUT/myctrl/ram_addr
add wave -noupdate -expand -group control_arb /dram_top_tb/DUT/myctrl/ramload
add wave -noupdate -expand -group control_arb /dram_top_tb/DUT/myctrl/ramstore
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/address
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/configs
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/rank
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/BG
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/bank
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/row
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/col
add wave -noupdate -expand -group addr_map /dram_top_tb/DUT/ctrl/myaddr/offset
add wave -noupdate -expand -group init_state /dram_top_tb/DUT/ctrl/myinit/init
add wave -noupdate -expand -group init_state /dram_top_tb/DUT/ctrl/myinit/init_done
add wave -noupdate -expand -group init_state /dram_top_tb/DUT/ctrl/myinit/init_state
add wave -noupdate -expand -group init_state /dram_top_tb/DUT/ctrl/myinit/ninit_state
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/RA0
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/BG0
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/BA0
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/R0
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/C0
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/ACT_n
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/RAS_n_A16
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/CAS_n_A15
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/WE_n_A14
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/ALERT_n
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/PARITY
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/RESET_n
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/TEN
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/CS_n
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/CKE
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/ODT
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/ZQ
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/PWR
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/VREF_CA
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/VREF_DQ
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/C
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/BG
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/BA
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/ADDR
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/ADDR_17
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/sig_gen/cmd_addr
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/sig_gen/issue
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/ref_re
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/state
add wave -noupdate -expand -group signal_gen /dram_top_tb/DUT/mysig/nstate
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/dREN
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/dWEN
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/init_done
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/init_req
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/tACT_done
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/tWR_done
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/tRD_done
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/tPRE_done
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/tREF_done
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/rf_req
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/row_stat
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/ram_wait
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/row_resolve
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/cmd_state
add wave -noupdate -expand -group cmd_FSM /dram_top_tb/DUT/ctrl/mycmd/ncmd_state
add wave -noupdate -expand -group time_signal /dram_top_tb/DUT/ctrl/mytime/tACT_done
add wave -noupdate -expand -group time_signal /dram_top_tb/DUT/ctrl/mytime/tWR_done
add wave -noupdate -expand -group time_signal /dram_top_tb/DUT/ctrl/mytime/tRD_done
add wave -noupdate -expand -group time_signal /dram_top_tb/DUT/ctrl/mytime/tPRE_done
add wave -noupdate -expand -group time_signal -divider refresh
add wave -noupdate -expand -group time_signal /dram_top_tb/DUT/ctrl/mytime/tREF_done
add wave -noupdate -expand -group time_signal /dram_top_tb/DUT/ctrl/mytime/rf_req
add wave -noupdate -expand -group time_signal -radix unsigned /dram_top_tb/DUT/ctrl/u4/refresh_limit
add wave -noupdate -expand -group time_signal -radix decimal /dram_top_tb/DUT/ctrl/u4/refresh_count
add wave -noupdate -expand -group time_signal -divider timing_trk
add wave -noupdate -expand -group time_signal /dram_top_tb/DUT/ctrl/u4/time_load
add wave -noupdate -expand -group time_signal /dram_top_tb/DUT/ctrl/u4/time_count
add wave -noupdate -expand -group time_signal /dram_top_tb/DUT/ctrl/u4/time_counter_en
add wave -noupdate -expand -group time_signal /dram_top_tb/DUT/ctrl/u4/time_count_done
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {3483693 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 255
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
WaveRestoreZoom {3485209 ps} {3492535 ps}
