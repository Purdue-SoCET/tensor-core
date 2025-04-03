onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -group FIFO /scheduler_buffer_tb/DUT/wptr
add wave -noupdate -group FIFO /scheduler_buffer_tb/DUT/rptr
add wave -noupdate -group FIFO /scheduler_buffer_tb/DUT/fifo
add wave -noupdate /scheduler_buffer_tb/DUT/clear
add wave -noupdate /scheduler_buffer_tb/DUT/flush
add wave -noupdate /scheduler_buffer_tb/DUT/full
add wave -noupdate -group Scheduler_if /scheduler_buffer_tb/scheduler_if/dREN
add wave -noupdate -group Scheduler_if /scheduler_buffer_tb/scheduler_if/dWEN
add wave -noupdate -group Scheduler_if /scheduler_buffer_tb/scheduler_if/request_done
add wave -noupdate -group Scheduler_if /scheduler_buffer_tb/scheduler_if/ramaddr
add wave -noupdate -group Scheduler_if /scheduler_buffer_tb/scheduler_if/memstore
add wave -noupdate -group Scheduler_if /scheduler_buffer_tb/scheduler_if/ramaddr_rq
add wave -noupdate -group Scheduler_if /scheduler_buffer_tb/scheduler_if/ramstore_rq
add wave -noupdate -group Scheduler_if /scheduler_buffer_tb/scheduler_if/ramaddr_rq_ft
add wave -noupdate -group Scheduler_if /scheduler_buffer_tb/scheduler_if/ramstore_rq_ft
add wave -noupdate -group Scheduler_if /scheduler_buffer_tb/scheduler_if/memaddr_callback
add wave -noupdate -expand -group Counter /scheduler_buffer_tb/DUT/write_count/NBITS
add wave -noupdate -expand -group Counter /scheduler_buffer_tb/DUT/write_count/CLK
add wave -noupdate -expand -group Counter /scheduler_buffer_tb/DUT/write_count/nRST
add wave -noupdate -expand -group Counter /scheduler_buffer_tb/DUT/write_count/clear
add wave -noupdate -expand -group Counter /scheduler_buffer_tb/DUT/write_count/count_enable
add wave -noupdate -expand -group Counter /scheduler_buffer_tb/DUT/write_count/overflow_val
add wave -noupdate -expand -group Counter /scheduler_buffer_tb/DUT/write_count/count_out
add wave -noupdate -expand -group Counter /scheduler_buffer_tb/DUT/write_count/overflow_flag
add wave -noupdate -expand -group Counter /scheduler_buffer_tb/DUT/write_count/count
add wave -noupdate -expand -group Counter /scheduler_buffer_tb/DUT/write_count/n_count
add wave -noupdate -expand -group Counter /scheduler_buffer_tb/DUT/write_count/of
add wave -noupdate -expand -group Counter /scheduler_buffer_tb/DUT/write_count/n_of
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {27321 ps} 0}
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
WaveRestoreZoom {0 ps} {95820 ps}
