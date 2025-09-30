onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /memory_arbiter_basic_tb/CLK
add wave -noupdate /memory_arbiter_basic_tb/nRST
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/iwait
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/dwait
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/iREN
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/dREN
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/dWEN
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/iload
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/dload
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/dstore
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/iaddr
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/daddr
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/ramWEN
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/ramREN
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/ramstate
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/ramaddr
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/ramstore
add wave -noupdate -group acif /memory_arbiter_basic_tb/acif/ramload
add wave -noupdate -expand -group spif /memory_arbiter_basic_tb/spif/sLoad_hit
add wave -noupdate -expand -group spif /memory_arbiter_basic_tb/spif/sStore_hit
add wave -noupdate -expand -group spif /memory_arbiter_basic_tb/spif/sLoad_row
add wave -noupdate -expand -group spif /memory_arbiter_basic_tb/expected_load_data
add wave -noupdate -expand -group spif /memory_arbiter_basic_tb/spif/load_data
add wave -noupdate -expand -group spif /memory_arbiter_basic_tb/spif/sLoad
add wave -noupdate -expand -group spif /memory_arbiter_basic_tb/spif/sStore
add wave -noupdate -expand -group spif /memory_arbiter_basic_tb/expected_store_data
add wave -noupdate -expand -group spif /memory_arbiter_basic_tb/spif/store_data
add wave -noupdate -expand -group spif /memory_arbiter_basic_tb/spif/load_addr
add wave -noupdate -expand -group spif /memory_arbiter_basic_tb/spif/store_addr
add wave -noupdate -expand -group memory_arbiter /memory_arbiter_basic_tb/DUT/load_count
add wave -noupdate -expand -group memory_arbiter /memory_arbiter_basic_tb/DUT/next_load_count
add wave -noupdate -expand -group memory_arbiter /memory_arbiter_basic_tb/DUT/store_count
add wave -noupdate -expand -group memory_arbiter /memory_arbiter_basic_tb/DUT/next_store_count
add wave -noupdate -expand -group memory_arbiter /memory_arbiter_basic_tb/DUT/sLoad_row_reg
add wave -noupdate -expand -group memory_arbiter /memory_arbiter_basic_tb/DUT/next_sLoad_row_reg
add wave -noupdate -expand -group memory_arbiter /memory_arbiter_basic_tb/DUT/sp_wait
add wave -noupdate -expand -group memory_arbiter /memory_arbiter_basic_tb/check_state/expected_state
add wave -noupdate -expand -group memory_arbiter /memory_arbiter_basic_tb/DUT/arbiter_state
add wave -noupdate -expand -group memory_arbiter /memory_arbiter_basic_tb/DUT/next_arbiter_state
add wave -noupdate -expand -group memory_arbiter /memory_arbiter_basic_tb/DUT/load_data_reg
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {445 ns} 0}
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
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ns} {983 ns}
