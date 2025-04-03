onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /data_transfer_tb/DUT/CLK
add wave -noupdate /data_transfer_tb/DUT/nRST
add wave -noupdate -expand -group dt_if /data_transfer_tb/dtif/wr_en
add wave -noupdate -expand -group dt_if /data_transfer_tb/dtif/rd_en
add wave -noupdate -expand -group dt_if /data_transfer_tb/dtif/clear
add wave -noupdate -expand -group dt_if /data_transfer_tb/dtif/memstore
add wave -noupdate -expand -group dt_if /data_transfer_tb/dtif/memload
add wave -noupdate -expand -group dt_if /data_transfer_tb/dtif/DQ
add wave -noupdate -expand -group dt_if /data_transfer_tb/dtif/DQS_t
add wave -noupdate -expand -group dt_if /data_transfer_tb/dtif/DQS_c
add wave -noupdate -expand -group DUT /data_transfer_tb/DUT/count_burst
add wave -noupdate -expand -group DUT /data_transfer_tb/DUT/ncount_burst
add wave -noupdate -expand -group DUT /data_transfer_tb/DUT/DQ_latch
add wave -noupdate -expand -group DUT /data_transfer_tb/DUT/nDQ_latch
add wave -noupdate -expand -group DUT /data_transfer_tb/DUT/DQS_t_latch
add wave -noupdate -expand -group DUT /data_transfer_tb/DUT/nDQS_t_latch
add wave -noupdate -expand -group DUT /data_transfer_tb/DUT/DQS_c_latch
add wave -noupdate -expand -group DUT /data_transfer_tb/DUT/nDQS_c_latch
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {70083 ps} 0}
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
WaveRestoreZoom {0 ps} {141750 ps}
