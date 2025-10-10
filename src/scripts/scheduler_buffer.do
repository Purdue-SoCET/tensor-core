onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /scheduler_buffer_tb/CLK
add wave -noupdate /scheduler_buffer_tb/nRST
add wave -noupdate /scheduler_buffer_tb/myif/WORD_W
add wave -noupdate /scheduler_buffer_tb/myif/dREN
add wave -noupdate /scheduler_buffer_tb/myif/dWEN
add wave -noupdate /scheduler_buffer_tb/myif/request_done
add wave -noupdate /scheduler_buffer_tb/myif/ramaddr
add wave -noupdate /scheduler_buffer_tb/myif/memstore
add wave -noupdate /scheduler_buffer_tb/myif/ramaddr_rq
add wave -noupdate /scheduler_buffer_tb/myif/ramstore_rq
add wave -noupdate /scheduler_buffer_tb/myif/ramaddr_rq_ft
add wave -noupdate /scheduler_buffer_tb/myif/ramstore_rq_ft
add wave -noupdate /scheduler_buffer_tb/myif/memaddr_callback
add wave -noupdate /scheduler_buffer_tb/myif/iwait
add wave -noupdate /scheduler_buffer_tb/myif/dwait
add wave -noupdate -expand /scheduler_buffer_tb/u0/fifo
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {43005 ps} 0}
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
WaveRestoreZoom {0 ps} {45374 ps}
