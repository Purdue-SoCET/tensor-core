onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /init_addr_row_cmd_tb/tb_CLK
add wave -noupdate /init_addr_row_cmd_tb/tb_nRST
add wave -noupdate -group {TB signals} /init_addr_row_cmd_tb/tb_test_case
add wave -noupdate -group {TB signals} /init_addr_row_cmd_tb/tb_test_case_num
add wave -noupdate -group {TB signals} /init_addr_row_cmd_tb/tb_i
add wave -noupdate -group {TB signals} /init_addr_row_cmd_tb/tb_mismatch
add wave -noupdate -group {TB signals} /init_addr_row_cmd_tb/tb_check
add wave -noupdate -group {init FSM} /init_addr_row_cmd_tb/tb_initif/init
add wave -noupdate -group {init FSM} /init_addr_row_cmd_tb/tb_initif/init_valid
add wave -noupdate -group {init FSM} /init_addr_row_cmd_tb/tb_initif/init_state
add wave -noupdate -group {addr mapper} /init_addr_row_cmd_tb/tb_amif/address
add wave -noupdate -group {addr mapper} /init_addr_row_cmd_tb/tb_amif/configs
add wave -noupdate -group {addr mapper} /init_addr_row_cmd_tb/tb_amif/rank
add wave -noupdate -group {addr mapper} /init_addr_row_cmd_tb/tb_amif/BG
add wave -noupdate -group {addr mapper} /init_addr_row_cmd_tb/tb_amif/bank
add wave -noupdate -group {addr mapper} /init_addr_row_cmd_tb/tb_amif/row
add wave -noupdate -group {addr mapper} /init_addr_row_cmd_tb/tb_amif/col
add wave -noupdate -group {addr mapper} /init_addr_row_cmd_tb/tb_amif/offset
add wave -noupdate -group {addr mapper} /init_addr_row_cmd_tb/tb_amif/ignore
add wave -noupdate -group {row policy} /init_addr_row_cmd_tb/tb_polif/row_conflict
add wave -noupdate -group {row policy} /init_addr_row_cmd_tb/tb_polif/req_en
add wave -noupdate -group {row policy} /init_addr_row_cmd_tb/tb_polif/refresh
add wave -noupdate -group {row policy} /init_addr_row_cmd_tb/tb_polif/row_resolve
add wave -noupdate -group {row policy} /init_addr_row_cmd_tb/tb_polif/row_stat
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/dREN
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/dWEN
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/init_done
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/init_req
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/tACT_done
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/tWR_done
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/tRD_done
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/tPRE_done
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/tREF_done
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/rf_req
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/row_resolve
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/ram_wait
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/cmd_state
add wave -noupdate -group {command FSM} /init_addr_row_cmd_tb/tb_cfsmif/ncmd_state
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
configure wave -namecolwidth 253
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
WaveRestoreZoom {99978445 ps} {99999684 ps}
