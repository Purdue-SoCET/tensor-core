onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /memory_systolic_array_tb/#ublk#166743922#76/major_test_name
add wave -noupdate /memory_systolic_array_tb/#ublk#166743922#76/test_name
add wave -noupdate /memory_systolic_array_tb/CLK
add wave -noupdate /memory_systolic_array_tb/nRST
add wave -noupdate -expand -group Scheduler /memory_systolic_array_tb/spif/instrFIFO_WEN
add wave -noupdate -expand -group Scheduler /memory_systolic_array_tb/spif/instrFIFO_wdata
add wave -noupdate -expand -group {Systolic Array} /memory_systolic_array_tb/spif/psumout_en
add wave -noupdate -expand -group {Systolic Array} /memory_systolic_array_tb/spif/drained
add wave -noupdate -expand -group {Systolic Array} /memory_systolic_array_tb/spif/fifo_has_space
add wave -noupdate -expand -group {Systolic Array} /memory_systolic_array_tb/spif/psumout_row_sel_in
add wave -noupdate -expand -group {Systolic Array} /memory_systolic_array_tb/spif/psumout_data
add wave -noupdate -group Arb /memory_systolic_array_tb/spif/sLoad_hit
add wave -noupdate -group Arb /memory_systolic_array_tb/spif/sStore_hit
add wave -noupdate -group Arb /memory_systolic_array_tb/spif/sLoad_row
add wave -noupdate -group Arb /memory_systolic_array_tb/spif/load_data
add wave -noupdate -group Arb -divider {Internal Arbiter}
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/DUT/ARB/sp_hit
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/spif/sLoad_hit
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/spif/sStore_hit
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/dcif/imemREN
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/dcif/dmemREN
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/dcif/dmemWEN
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/DUT/ARB/load_count
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/DUT/ARB/next_load_count
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/DUT/ARB/sLoad_row_reg
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/DUT/ARB/next_sLoad_row_reg
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/DUT/ARB/sp_wait
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/DUT/ARB/arbiter_state
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/DUT/spif/load_addr
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/DUT/ARB/sp_load_addr
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/DUT/ARB/sp_load_data
add wave -noupdate -group Arb -expand -group Arb-Internal /memory_systolic_array_tb/DUT/ARB/load_data_reg
add wave -noupdate -group Arb -divider Outputs
add wave -noupdate -expand -group {Scheduler Out} /memory_systolic_array_tb/spif/instrFIFO_full
add wave -noupdate -expand -group {Scheduler Out} /memory_systolic_array_tb/spif/gemm_complete
add wave -noupdate -expand -group {Scheduler Out} /memory_systolic_array_tb/spif/load_complete
add wave -noupdate -expand -group {Scheduler Out} /memory_systolic_array_tb/DUT/spif/store_complete
add wave -noupdate -expand -group {Systolic Array Out} /memory_systolic_array_tb/spif/partial_enable
add wave -noupdate -expand -group {Systolic Array Out} /memory_systolic_array_tb/spif/weight_enable
add wave -noupdate -expand -group {Systolic Array Out} /memory_systolic_array_tb/spif/input_enable
add wave -noupdate -expand -group {Systolic Array Out} /memory_systolic_array_tb/spif/weight_input_data
add wave -noupdate -expand -group {Systolic Array Out} /memory_systolic_array_tb/spif/partial_sum_data
add wave -noupdate -expand -group {Systolic Array Out} /memory_systolic_array_tb/spif/weight_input_row_sel
add wave -noupdate -expand -group {Systolic Array Out} /memory_systolic_array_tb/spif/partial_sum_row_sel
add wave -noupdate -group {Arb Out} /memory_systolic_array_tb/spif/sLoad
add wave -noupdate -group {Arb Out} /memory_systolic_array_tb/spif/sStore
add wave -noupdate -group {Arb Out} /memory_systolic_array_tb/spif/store_data
add wave -noupdate -group {Arb Out} /memory_systolic_array_tb/spif/load_addr
add wave -noupdate -group {Arb Out} /memory_systolic_array_tb/spif/store_addr
add wave -noupdate -divider DCACHE
add wave -noupdate /memory_systolic_array_tb/DUT/DCACHE/dcache_state
add wave -noupdate /memory_systolic_array_tb/DUT/DCACHE/next_dcache_state
add wave -noupdate /memory_systolic_array_tb/DUT/DCACHE/dcache_format
add wave -noupdate -radix hexadecimal /memory_systolic_array_tb/DUT/DCACHE/dcache
add wave -noupdate -radix hexadecimal -childformat {{{/memory_systolic_array_tb/DUT/DCACHE/next_dcache[7]} -radix binary} {{/memory_systolic_array_tb/DUT/DCACHE/next_dcache[6]} -radix binary} {{/memory_systolic_array_tb/DUT/DCACHE/next_dcache[5]} -radix binary} {{/memory_systolic_array_tb/DUT/DCACHE/next_dcache[4]} -radix binary} {{/memory_systolic_array_tb/DUT/DCACHE/next_dcache[3]} -radix binary} {{/memory_systolic_array_tb/DUT/DCACHE/next_dcache[2]} -radix binary} {{/memory_systolic_array_tb/DUT/DCACHE/next_dcache[1]} -radix binary} {{/memory_systolic_array_tb/DUT/DCACHE/next_dcache[0]} -radix binary}} -subitemconfig {{/memory_systolic_array_tb/DUT/DCACHE/next_dcache[7]} {-height 16 -radix binary} {/memory_systolic_array_tb/DUT/DCACHE/next_dcache[6]} {-height 16 -radix binary} {/memory_systolic_array_tb/DUT/DCACHE/next_dcache[5]} {-height 16 -radix binary} {/memory_systolic_array_tb/DUT/DCACHE/next_dcache[4]} {-height 16 -radix binary} {/memory_systolic_array_tb/DUT/DCACHE/next_dcache[3]} {-height 16 -radix binary} {/memory_systolic_array_tb/DUT/DCACHE/next_dcache[2]} {-height 16 -radix binary} {/memory_systolic_array_tb/DUT/DCACHE/next_dcache[1]} {-height 16 -radix binary} {/memory_systolic_array_tb/DUT/DCACHE/next_dcache[0]} {-height 16 -radix binary}} /memory_systolic_array_tb/DUT/DCACHE/next_dcache
add wave -noupdate -group {datapath interface} /memory_systolic_array_tb/DUT/DCACHE/dcif/dhit
add wave -noupdate -group {datapath interface} /memory_systolic_array_tb/DUT/DCACHE/dcif/dmemREN
add wave -noupdate -group {datapath interface} /memory_systolic_array_tb/DUT/DCACHE/dcif/dmemWEN
add wave -noupdate -group {datapath interface} /memory_systolic_array_tb/DUT/DCACHE/dcif/dmemload
add wave -noupdate -group {datapath interface} /memory_systolic_array_tb/DUT/DCACHE/dcif/dmemstore
add wave -noupdate -group {datapath interface} /memory_systolic_array_tb/DUT/DCACHE/dcif/dmemaddr
add wave -noupdate -group {cache interface} /memory_systolic_array_tb/DUT/DCACHE/cif/dwait
add wave -noupdate -group {cache interface} /memory_systolic_array_tb/DUT/DCACHE/cif/dREN
add wave -noupdate -group {cache interface} /memory_systolic_array_tb/DUT/DCACHE/cif/dWEN
add wave -noupdate -group {cache interface} /memory_systolic_array_tb/DUT/DCACHE/cif/dload
add wave -noupdate -group {cache interface} /memory_systolic_array_tb/DUT/DCACHE/cif/dstore
add wave -noupdate -group {cache interface} /memory_systolic_array_tb/DUT/DCACHE/cif/daddr
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/mats
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb1/mats
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb2/mats
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb3/mats
add wave -noupdate -divider SCRATCHPAD
add wave -noupdate /memory_systolic_array_tb/DUT/SP/gemmFSM/PSFSM_state
add wave -noupdate /memory_systolic_array_tb/DUT/SP/gemmFSM/WIFSM_state
add wave -noupdate /memory_systolic_array_tb/DUT/SP/gemmFSM/weight_status
add wave -noupdate /memory_systolic_array_tb/DUT/SP/gfsmif/new_weight
add wave -noupdate /memory_systolic_array_tb/DUT/SP/new_instr
add wave -noupdate /memory_systolic_array_tb/DUT/SP/instrFIFO_rdata
add wave -noupdate /memory_systolic_array_tb/DUT/SP/instrFIFO_empty
add wave -noupdate /memory_systolic_array_tb/DUT/SP/instrFIFO_REN
add wave -noupdate /memory_systolic_array_tb/DUT/SP/gemm_mat
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/dramFIFO0_empty
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/dramFIFO1_empty
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/dramFIFO2_empty
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/dramFIFO3_empty
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/sStore_hit
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/dramFIFO0_REN
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/dramFIFO1_REN
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/dramFIFO2_REN
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/dramFIFO3_REN
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/sStore
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/s_Store
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/store_complete
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/store_addr
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/store_data
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/dramFIFO0_rdata
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/dramFIFO1_rdata
add wave -noupdate -group DFSM /memory_systolic_array_tb/DUT/SP/dfsmif/dramFIFO2_rdata
add wave -noupdate -group DFSM -expand /memory_systolic_array_tb/DUT/SP/dfsmif/dramFIFO3_rdata
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/WEN
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/REN
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/clear
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/wdata
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/full
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/empty
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/underrun
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/overrun
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/count
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/rdata
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/overrun_next
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/underrun_next
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/write_ptr
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/write_ptr_next
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/read_ptr
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/read_ptr_next
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/count_next
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/fifo
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/wFIFO/fifo_next
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/WEN
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/REN
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/clear
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/wdata
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/full
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/empty
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/underrun
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/overrun
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/count
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/rdata
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/overrun_next
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/underrun_next
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/write_ptr
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/write_ptr_next
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/read_ptr
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/read_ptr_next
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/count_next
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/fifo
add wave -noupdate /memory_systolic_array_tb/DUT/SP/spb0/rFIFO/fifo_next
add wave -noupdate /memory_systolic_array_tb/DUT/SP/bfsm0/state
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {2360000 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 140
configure wave -valuecolwidth 215
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
WaveRestoreZoom {1508710 ps} {4526148 ps}
