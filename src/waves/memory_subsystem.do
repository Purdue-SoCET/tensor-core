onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /memory_subsystem_tb/#ublk#264626690#74/test_name
add wave -noupdate /memory_subsystem_tb/CLK
add wave -noupdate /memory_subsystem_tb/nRST
add wave -noupdate -group Scheduler /memory_subsystem_tb/spif/instrFIFO_WEN
add wave -noupdate -group Scheduler /memory_subsystem_tb/spif/instrFIFO_wdata
add wave -noupdate -group {Systolic Array} /memory_subsystem_tb/spif/psumout_en
add wave -noupdate -group {Systolic Array} /memory_subsystem_tb/spif/drained
add wave -noupdate -group {Systolic Array} /memory_subsystem_tb/spif/fifo_has_space
add wave -noupdate -group {Systolic Array} /memory_subsystem_tb/spif/psumout_row_sel_in
add wave -noupdate -group {Systolic Array} /memory_subsystem_tb/spif/psumout_data
add wave -noupdate -expand -group Arb /memory_subsystem_tb/spif/sLoad_hit
add wave -noupdate -expand -group Arb /memory_subsystem_tb/spif/sStore_hit
add wave -noupdate -expand -group Arb /memory_subsystem_tb/spif/sLoad_row
add wave -noupdate -expand -group Arb /memory_subsystem_tb/spif/load_data
add wave -noupdate -expand -group Arb -divider {Internal Arbiter}
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/DUT/ARB/sp_hit
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/spif/sLoad_hit
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/spif/sStore_hit
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/dcif/imemREN
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/dcif/dmemREN
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/dcif/dmemWEN
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/DUT/ARB/load_count
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/DUT/ARB/next_load_count
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/DUT/ARB/sLoad_row_reg
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/DUT/ARB/next_sLoad_row_reg
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/DUT/ARB/sp_wait
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/DUT/ARB/arbiter_state
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/DUT/spif/load_addr
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/DUT/ARB/sp_load_addr
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/DUT/ARB/sp_load_data
add wave -noupdate -expand -group Arb -expand -group Arb-Internal /memory_subsystem_tb/DUT/ARB/load_data_reg
add wave -noupdate -expand -group Arb -divider Outputs
add wave -noupdate -group {Scheduler Out} /memory_subsystem_tb/spif/instrFIFO_full
add wave -noupdate -group {Scheduler Out} /memory_subsystem_tb/spif/gemm_complete
add wave -noupdate -group {Scheduler Out} /memory_subsystem_tb/spif/load_complete
add wave -noupdate -group {Systolic Array Out} /memory_subsystem_tb/spif/partial_enable
add wave -noupdate -group {Systolic Array Out} /memory_subsystem_tb/spif/weight_enable
add wave -noupdate -group {Systolic Array Out} /memory_subsystem_tb/spif/input_enable
add wave -noupdate -group {Systolic Array Out} /memory_subsystem_tb/spif/weight_input_data
add wave -noupdate -group {Systolic Array Out} /memory_subsystem_tb/spif/partial_sum_data
add wave -noupdate -group {Systolic Array Out} /memory_subsystem_tb/spif/weight_input_row_sel
add wave -noupdate -group {Systolic Array Out} /memory_subsystem_tb/spif/partial_sum_row_sel
add wave -noupdate -expand -group {Arb Out} /memory_subsystem_tb/spif/sLoad
add wave -noupdate -expand -group {Arb Out} /memory_subsystem_tb/spif/sStore
add wave -noupdate -expand -group {Arb Out} /memory_subsystem_tb/spif/store_data
add wave -noupdate -expand -group {Arb Out} /memory_subsystem_tb/spif/load_addr
add wave -noupdate -expand -group {Arb Out} /memory_subsystem_tb/spif/store_addr
add wave -noupdate -divider DCACHE
add wave -noupdate /memory_subsystem_tb/DUT/DCACHE/dcache_state
add wave -noupdate /memory_subsystem_tb/DUT/DCACHE/next_dcache_state
add wave -noupdate /memory_subsystem_tb/DUT/DCACHE/dcache_format
add wave -noupdate -radix hexadecimal /memory_subsystem_tb/DUT/DCACHE/dcache
add wave -noupdate -radix hexadecimal -childformat {{{/memory_subsystem_tb/DUT/DCACHE/next_dcache[7]} -radix binary} {{/memory_subsystem_tb/DUT/DCACHE/next_dcache[6]} -radix binary} {{/memory_subsystem_tb/DUT/DCACHE/next_dcache[5]} -radix binary} {{/memory_subsystem_tb/DUT/DCACHE/next_dcache[4]} -radix binary} {{/memory_subsystem_tb/DUT/DCACHE/next_dcache[3]} -radix binary} {{/memory_subsystem_tb/DUT/DCACHE/next_dcache[2]} -radix binary} {{/memory_subsystem_tb/DUT/DCACHE/next_dcache[1]} -radix binary} {{/memory_subsystem_tb/DUT/DCACHE/next_dcache[0]} -radix binary}} -subitemconfig {{/memory_subsystem_tb/DUT/DCACHE/next_dcache[7]} {-height 16 -radix binary} {/memory_subsystem_tb/DUT/DCACHE/next_dcache[6]} {-height 16 -radix binary} {/memory_subsystem_tb/DUT/DCACHE/next_dcache[5]} {-height 16 -radix binary} {/memory_subsystem_tb/DUT/DCACHE/next_dcache[4]} {-height 16 -radix binary} {/memory_subsystem_tb/DUT/DCACHE/next_dcache[3]} {-height 16 -radix binary} {/memory_subsystem_tb/DUT/DCACHE/next_dcache[2]} {-height 16 -radix binary} {/memory_subsystem_tb/DUT/DCACHE/next_dcache[1]} {-height 16 -radix binary} {/memory_subsystem_tb/DUT/DCACHE/next_dcache[0]} {-height 16 -radix binary}} /memory_subsystem_tb/DUT/DCACHE/next_dcache
add wave -noupdate -expand -group {datapath interface} /memory_subsystem_tb/DUT/DCACHE/dcif/dhit
add wave -noupdate -expand -group {datapath interface} /memory_subsystem_tb/DUT/DCACHE/dcif/dmemREN
add wave -noupdate -expand -group {datapath interface} /memory_subsystem_tb/DUT/DCACHE/dcif/dmemWEN
add wave -noupdate -expand -group {datapath interface} /memory_subsystem_tb/DUT/DCACHE/dcif/dmemload
add wave -noupdate -expand -group {datapath interface} /memory_subsystem_tb/DUT/DCACHE/dcif/dmemstore
add wave -noupdate -expand -group {datapath interface} /memory_subsystem_tb/DUT/DCACHE/dcif/dmemaddr
add wave -noupdate -expand -group {cache interface} /memory_subsystem_tb/DUT/DCACHE/cif/dwait
add wave -noupdate -expand -group {cache interface} /memory_subsystem_tb/DUT/DCACHE/cif/dREN
add wave -noupdate -expand -group {cache interface} /memory_subsystem_tb/DUT/DCACHE/cif/dWEN
add wave -noupdate -expand -group {cache interface} /memory_subsystem_tb/DUT/DCACHE/cif/dload
add wave -noupdate -expand -group {cache interface} /memory_subsystem_tb/DUT/DCACHE/cif/dstore
add wave -noupdate -expand -group {cache interface} /memory_subsystem_tb/DUT/DCACHE/cif/daddr
add wave -noupdate -expand -subitemconfig {{/memory_subsystem_tb/DUT/SP/spb0/mats[2]} -expand} /memory_subsystem_tb/DUT/SP/spb0/mats
add wave -noupdate /memory_subsystem_tb/DUT/SP/spb1/mats
add wave -noupdate /memory_subsystem_tb/DUT/SP/spb2/mats
add wave -noupdate /memory_subsystem_tb/DUT/SP/spb3/mats
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {978 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 191
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
WaveRestoreZoom {0 ns} {1529 ns}
