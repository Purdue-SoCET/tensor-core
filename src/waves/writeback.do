onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group Inputs -radix hexadecimal /writeback_tb/wbif/alu_out
add wave -noupdate -expand -group Inputs -radix hexadecimal /writeback_tb/wbif/dmemload
add wave -noupdate -expand -group Inputs -radix hexadecimal /writeback_tb/wbif/load_ready
add wave -noupdate -expand -group Inputs -radix hexadecimal /writeback_tb/wbif/alu_ready
add wave -noupdate -expand -group Inputs -radix hexadecimal /writeback_tb/wbif/reg_sel_alu
add wave -noupdate -expand -group Inputs -radix hexadecimal /writeback_tb/wbif/reg_sel_load
add wave -noupdate -expand -group Outputs -radix hexadecimal -childformat {{/writeback_tb/wbif/wb_out.s_rw_en -radix hexadecimal} {/writeback_tb/wbif/wb_out.s_rw -radix hexadecimal} {/writeback_tb/wbif/wb_out.s_wdata -radix hexadecimal} {/writeback_tb/wbif/wb_out.load_done -radix hexadecimal} {/writeback_tb/wbif/wb_out.alu_done -radix hexadecimal}} -expand -subitemconfig {/writeback_tb/wbif/wb_out.s_rw_en {-height 16 -radix hexadecimal} /writeback_tb/wbif/wb_out.s_rw {-height 16 -radix hexadecimal} /writeback_tb/wbif/wb_out.s_wdata {-height 16 -radix hexadecimal} /writeback_tb/wbif/wb_out.load_done {-height 16 -radix hexadecimal} /writeback_tb/wbif/wb_out.alu_done {-height 16 -radix hexadecimal}} /writeback_tb/wbif/wb_out
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {51169 ps} 0}
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
WaveRestoreZoom {0 ps} {84 ns}
