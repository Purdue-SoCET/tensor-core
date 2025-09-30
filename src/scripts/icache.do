onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /icache_tb/PROG/CLK
add wave -noupdate /icache_tb/PROG/nrst
add wave -noupdate /icache_tb/PROG/test_num
add wave -noupdate -expand -group dcif /icache_tb/dcif/ihit
add wave -noupdate -expand -group dcif /icache_tb/dcif/imemREN
add wave -noupdate -expand -group dcif /icache_tb/dcif/imemload
add wave -noupdate -expand -group dcif /icache_tb/dcif/imemaddr
add wave -noupdate -expand -group cif0 /icache_tb/cif0/iwait
add wave -noupdate -expand -group cif0 /icache_tb/cif0/iREN
add wave -noupdate -expand -group cif0 /icache_tb/cif0/iload
add wave -noupdate -expand -group cif0 /icache_tb/cif0/iaddr
add wave -noupdate -expand -group icache /icache_tb/DUT_icache/icache_format
add wave -noupdate -expand -group icache /icache_tb/DUT_icache/icache
add wave -noupdate -expand -group icache /icache_tb/DUT_icache/nxt_icache
add wave -noupdate -expand -group icache /icache_tb/DUT_icache/icache_state
add wave -noupdate -expand -group icache /icache_tb/DUT_icache/nxt_icache_state
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {88 ns} 0}
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
WaveRestoreZoom {0 ns} {474 ns}
