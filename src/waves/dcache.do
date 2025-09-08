onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /dcache_tb/CLK
add wave -noupdate /dcache_tb/nRST
add wave -noupdate -expand -group {Datapath Cache} /dcache_tb/dcif/halt
add wave -noupdate -expand -group {Datapath Cache} /dcache_tb/dcif/dhit
add wave -noupdate -expand -group {Datapath Cache} /dcache_tb/dcif/dmemREN
add wave -noupdate -expand -group {Datapath Cache} /dcache_tb/dcif/dmemWEN
add wave -noupdate -expand -group {Datapath Cache} /dcache_tb/dcif/dmemload
add wave -noupdate -expand -group {Datapath Cache} /dcache_tb/dcif/dmemstore
add wave -noupdate -expand -group {Datapath Cache} /dcache_tb/dcif/dmemaddr
add wave -noupdate -expand -group Cache /dcache_tb/cif0/dwait
add wave -noupdate -expand -group Cache /dcache_tb/cif0/dREN
add wave -noupdate -expand -group Cache /dcache_tb/cif0/dWEN
add wave -noupdate -expand -group Cache /dcache_tb/cif0/dload
add wave -noupdate -expand -group Cache /dcache_tb/cif0/dstore
add wave -noupdate -expand -group Cache /dcache_tb/cif0/daddr
add wave -noupdate /dcache_tb/DUT_dcache/hit_way2_async
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/i
add wave -noupdate -expand -group {Dcache States} -radix unsigned /dcache_tb/DUT_dcache/flush_counter
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/hit_count
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/next_hit_count
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/miss
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/dirty_hit
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/finish_flush
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/hit_way1_async
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/hit_way2_async
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/load_way1_sync
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/load_way2_sync
add wave -noupdate -expand -group {Dcache States} -radix binary /dcache_tb/DUT_dcache/lru
add wave -noupdate -expand -group {Dcache States} -radix binary /dcache_tb/DUT_dcache/next_lru
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/flush_idx
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/next_flush_idx
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/dcache_format
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/dcache
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/next_dcache
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/dcache_state
add wave -noupdate -expand -group {Dcache States} /dcache_tb/DUT_dcache/next_dcache_state
add wave -noupdate -expand -group {Dcache States} -divider {New Divider}
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/i
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/hit_count
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/next_hit_count
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/miss
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/finish_flush
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/hit_way1_async
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/hit_way2_async
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/load_way1_sync
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/load_way2_sync
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/lru
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/next_lru
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/flush_idx
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/next_flush_idx
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/flush_counter
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/next_flush_counter
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/dcache_format
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/dcache
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/next_dcache
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/dcache_state
add wave -noupdate -expand -group {internal DUT} /dcache_tb/DUT_dcache/next_dcache_state
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1101 ns} 0}
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
WaveRestoreZoom {921 ns} {1335 ns}