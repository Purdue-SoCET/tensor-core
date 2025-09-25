onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /dram_top_tb/test_case
add wave -noupdate /dram_top_tb/CLK
add wave -noupdate /dram_top_tb/nRST
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/dWEN
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/dREN
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/ram_wait
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/ram_addr
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/ramload
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/ramstore
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/init_done
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/tACT_done
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/tWR_done
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/tRD_done
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/tPRE_done
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/tREF_done
add wave -noupdate -expand -group top_if /dram_top_tb/mycmd/rf_req
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/dREN
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/dWEN
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/init_done
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/init_req
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/tACT_done
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/tWR_done
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/tRD_done
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/tPRE_done
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/tREF_done
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/rf_req
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/row_stat
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/ram_wait
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/row_resolve
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/cmd_state
add wave -noupdate -expand -group cmd_if /dram_top_tb/DUT/mycmd/ncmd_state
add wave -noupdate -expand -group init_if /dram_top_tb/DUT/myinit/init
add wave -noupdate -expand -group init_if /dram_top_tb/DUT/myinit/init_valid
add wave -noupdate -expand -group init_if /dram_top_tb/DUT/myinit/init_state
add wave -noupdate -expand -group addr_if /dram_top_tb/DUT/myaddr/address
add wave -noupdate -expand -group addr_if /dram_top_tb/DUT/myaddr/configs
add wave -noupdate -expand -group addr_if /dram_top_tb/DUT/myaddr/rank
add wave -noupdate -expand -group addr_if /dram_top_tb/DUT/myaddr/BG
add wave -noupdate -expand -group addr_if /dram_top_tb/DUT/myaddr/bank
add wave -noupdate -expand -group addr_if /dram_top_tb/DUT/myaddr/row
add wave -noupdate -expand -group addr_if /dram_top_tb/DUT/myaddr/col
add wave -noupdate -expand -group addr_if /dram_top_tb/DUT/myaddr/offset
add wave -noupdate -expand -group row_open_if /dram_top_tb/DUT/myrow/row
add wave -noupdate -expand -group row_open_if /dram_top_tb/DUT/myrow/bank
add wave -noupdate -expand -group row_open_if /dram_top_tb/DUT/myrow/bank_group
add wave -noupdate -expand -group row_open_if /dram_top_tb/DUT/myrow/row_conflict
add wave -noupdate -expand -group row_open_if /dram_top_tb/DUT/myrow/req_en
add wave -noupdate -expand -group row_open_if /dram_top_tb/DUT/myrow/refresh
add wave -noupdate -expand -group row_open_if /dram_top_tb/DUT/myrow/row_resolve
add wave -noupdate -expand -group row_open_if /dram_top_tb/DUT/myrow/row_stat
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {165 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 142
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
WaveRestoreZoom {0 ps} {3281 ps}
