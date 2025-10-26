onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /dram_controller_top_tb/CLK
add wave -noupdate /dram_controller_top_tb/nRST
add wave -noupdate /dram_controller_top_tb/CLKx2
add wave -noupdate /dram_controller_top_tb/task_name
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/CK
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/ACT_n
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/RAS_n_A16
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/CAS_n_A15
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/WE_n_A14
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/ALERT_n
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/PARITY
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/RESET_n
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/TEN
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/CS_n
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/CKE
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/ODT
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/C
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/BG
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/BA
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/ADDR
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/ADDR_17
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/DM_n
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/DQ
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/DQS_t
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/DQS_c
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/ZQ
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/PWR
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/VREF_CA
add wave -noupdate -group iDDR4_1 /dram_controller_top_tb/iDDR4_1/VREF_DQ
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/CK
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/ACT_n
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/RAS_n_A16
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/CAS_n_A15
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/WE_n_A14
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/ALERT_n
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/PARITY
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/RESET_n
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/TEN
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/CS_n
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/CKE
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/ODT
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/C
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/BG
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/BA
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/ADDR
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/ADDR_17
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/DM_n
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/DQ
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/DQS_t
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/DQS_c
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/ZQ
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/PWR
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/VREF_CA
add wave -noupdate -group iDDR4_2 /dram_controller_top_tb/iDDR4_2/VREF_DQ
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/CK
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/ACT_n
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/RAS_n_A16
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/CAS_n_A15
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/WE_n_A14
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/ALERT_n
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/PARITY
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/RESET_n
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/TEN
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/CS_n
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/CKE
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/ODT
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/C
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/BG
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/BA
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/ADDR
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/ADDR_17
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/DM_n
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/DQ
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/DQS_t
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/DQS_c
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/ZQ
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/PWR
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/VREF_CA
add wave -noupdate -group iDDR4_3 /dram_controller_top_tb/iDDR4_3/VREF_DQ
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/CK
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/ACT_n
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/RAS_n_A16
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/CAS_n_A15
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/WE_n_A14
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/ALERT_n
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/PARITY
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/RESET_n
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/TEN
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/CS_n
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/CKE
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/ODT
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/C
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/BG
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/BA
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/ADDR
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/ADDR_17
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/DM_n
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/DQ
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/DQS_t
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/DQS_c
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/ZQ
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/PWR
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/VREF_CA
add wave -noupdate -group iDDR4_4 /dram_controller_top_tb/iDDR4_4/VREF_DQ
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/ref_re
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/ACT_n
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/RAS_n_A16
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/CAS_n_A15
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/WE_n_A14
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/ALERT_n
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/PARITY
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/RESET_n
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/TEN
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/CS_n
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/CKE
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/ODT
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/ZQ
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/PWR
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/VREF_CA
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/VREF_DQ
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/C
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/BG
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/BA
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/ADDR
add wave -noupdate -group {signal gen} /dram_controller_top_tb/sigif/ADDR_17
add wave -noupdate -group {address mapper} /dram_controller_top_tb/amif/address
add wave -noupdate -group {address mapper} /dram_controller_top_tb/amif/configs
add wave -noupdate -group {address mapper} /dram_controller_top_tb/amif/rank
add wave -noupdate -group {address mapper} /dram_controller_top_tb/amif/BG
add wave -noupdate -group {address mapper} /dram_controller_top_tb/amif/bank
add wave -noupdate -group {address mapper} /dram_controller_top_tb/amif/row
add wave -noupdate -group {address mapper} /dram_controller_top_tb/amif/col
add wave -noupdate -group {address mapper} /dram_controller_top_tb/amif/offset
add wave -noupdate -group {address mapper} /dram_controller_top_tb/amif/ignore
add wave -noupdate -group init /dram_controller_top_tb/initif/init
add wave -noupdate -group init /dram_controller_top_tb/initif/init_valid
add wave -noupdate -group init /dram_controller_top_tb/initif/init_state
add wave -noupdate -group init /dram_controller_top_tb/initif/n_init_state
add wave -noupdate -group {row policy} /dram_controller_top_tb/polif/row_conflict
add wave -noupdate -group {row policy} /dram_controller_top_tb/polif/req_en
add wave -noupdate -group {row policy} /dram_controller_top_tb/polif/refresh
add wave -noupdate -group {row policy} /dram_controller_top_tb/polif/row_resolve
add wave -noupdate -group {row policy} /dram_controller_top_tb/polif/row_stat
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/dREN
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/dWEN
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/init_done
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/init_req
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/tACT_done
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/tWR_done
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/tRD_done
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/tPRE_done
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/tREF_done
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/rf_req
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/row_resolve
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/ram_wait
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/cmd_state
add wave -noupdate -group {cmd fsm} /dram_controller_top_tb/cfsmif/ncmd_state
add wave -noupdate -group {timing control} /dram_controller_top_tb/timif/tACT_done
add wave -noupdate -group {timing control} /dram_controller_top_tb/timif/tWR_done
add wave -noupdate -group {timing control} /dram_controller_top_tb/timif/tRD_done
add wave -noupdate -group {timing control} /dram_controller_top_tb/timif/tPRE_done
add wave -noupdate -group {timing control} /dram_controller_top_tb/timif/tREF_done
add wave -noupdate -group {timing control} /dram_controller_top_tb/timif/rf_req
add wave -noupdate -group {timing control} /dram_controller_top_tb/timif/wr_en
add wave -noupdate -group {timing control} /dram_controller_top_tb/timif/rd_en
add wave -noupdate -group {timing control} /dram_controller_top_tb/timif/clear
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/dWEN
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/dREN
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/ram_wait
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/address
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/ramload
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/ramstore
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/state
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/nstate
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/init_done
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/init_req
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/tACT_done
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/tWR_done
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/tRD_done
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/tPRE_done
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/tREF_done
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/rf_req
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/rank
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/BG
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/bank
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/row
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/col
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/offset
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/wr_en
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/rd_en
add wave -noupdate -group {control unit} /dram_controller_top_tb/cuif/clear
add wave -noupdate -group {data transfer} /dram_controller_top_tb/dataif/wr_en
add wave -noupdate -group {data transfer} /dram_controller_top_tb/dataif/rd_en
add wave -noupdate -group {data transfer} /dram_controller_top_tb/dataif/clear
add wave -noupdate -group {data transfer} /dram_controller_top_tb/dataif/edge_flag
add wave -noupdate -group {data transfer} /dram_controller_top_tb/dataif/memstore
add wave -noupdate -group {data transfer} /dram_controller_top_tb/dataif/memload
add wave -noupdate -group {data transfer} /dram_controller_top_tb/dataif/COL_choice
add wave -noupdate -group {data transfer} /dram_controller_top_tb/dataif/DQ
add wave -noupdate -group {data transfer} /dram_controller_top_tb/dataif/DQS_t
add wave -noupdate -group {data transfer} /dram_controller_top_tb/dataif/DQS_c
add wave -noupdate -group {data transfer} /dram_controller_top_tb/dataif/DM_n
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/dREN
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/dWEN
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/request_done
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/ramaddr
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/memstore
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/ramaddr_rq
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/ramstore_rq
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/ramaddr_rq_ft
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/ramstore_rq_ft
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/memaddr_callback
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/iwait
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/dwait
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/ramREN_curr
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/ramREN_ftrt
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/ramWEN_curr
add wave -noupdate -group {scheduler if} /dram_controller_top_tb/sch_if/ramWEN_ftrt
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {3387750 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 292
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
WaveRestoreZoom {2760234 ps} {4084266 ps}
