onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group FIFO /scheduler_buffer_tb/DUT/wptr
add wave -noupdate -expand -group FIFO /scheduler_buffer_tb/DUT/rptr
add wave -noupdate -expand -group FIFO -subitemconfig {{/scheduler_buffer_tb/DUT/fifo[1]} -expand {/scheduler_buffer_tb/DUT/fifo[0]} -expand} /scheduler_buffer_tb/DUT/fifo
add wave -noupdate -expand -group sche_if /scheduler_buffer_tb/scheduler_if/dREN
add wave -noupdate -expand -group sche_if /scheduler_buffer_tb/scheduler_if/dWEN
add wave -noupdate -expand -group sche_if /scheduler_buffer_tb/scheduler_if/request_done
add wave -noupdate -expand -group sche_if /scheduler_buffer_tb/scheduler_if/ramaddr
add wave -noupdate -expand -group sche_if /scheduler_buffer_tb/scheduler_if/memstore
add wave -noupdate -expand -group sche_if /scheduler_buffer_tb/scheduler_if/ramaddr_rq
add wave -noupdate -expand -group sche_if /scheduler_buffer_tb/scheduler_if/ramstore_rq
add wave -noupdate -expand -group sche_if /scheduler_buffer_tb/scheduler_if/ramaddr_rq_ft
add wave -noupdate -expand -group sche_if /scheduler_buffer_tb/scheduler_if/ramstore_rq_ft
add wave -noupdate -expand -group sche_if /scheduler_buffer_tb/scheduler_if/memaddr_callback
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {54669 ps} 0}
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
WaveRestoreZoom {0 ps} {94500 ps}
