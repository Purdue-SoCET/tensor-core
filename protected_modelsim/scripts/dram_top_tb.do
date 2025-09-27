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
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {17489 ps} 0}
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
WaveRestoreZoom {0 ps} {33863 ps}
