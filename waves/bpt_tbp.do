onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /bpt_tbp_tb/PERIOD
add wave -noupdate /bpt_tbp_tb/CLK
add wave -noupdate /bpt_tbp_tb/nRST
add wave -noupdate /bpt_tbp_tb/casenum
add wave -noupdate /bpt_tbp_tb/casename
add wave -noupdate -expand -group Input /bpt_tbp_tb/DUT/bpt_tbpif/pc_res
add wave -noupdate -expand -group Input /bpt_tbp_tb/DUT/bpt_tbpif/taken_res
add wave -noupdate -expand -group Input /bpt_tbp_tb/DUT/bpt_tbpif/enable_res
add wave -noupdate -expand -group Input /bpt_tbp_tb/DUT/bpt_tbpif/pc_fetch
add wave -noupdate -expand -group Output /bpt_tbp_tb/DUT/bpt_tbpif/pred_fetch
add wave -noupdate -expand -group Internal -radix binary /bpt_tbp_tb/DUT/curr_bpt_tbp
add wave -noupdate -expand -group Internal -radix binary /bpt_tbp_tb/DUT/nxt_bpt_tbp
add wave -noupdate -expand -group Internal -radix binary /bpt_tbp_tb/DUT/bpt_tbp
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {16384800 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 244
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
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
WaveRestoreZoom {16376400 ps} {16385160 ps}
