onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix decimal /writeback_tb/test_num
add wave -noupdate -expand -group Inputs -expand -group Inputs -radix unsigned /writeback_tb/wbif/alu_wdat
add wave -noupdate -expand -group Inputs -expand -group Inputs -radix unsigned /writeback_tb/wbif/alu_reg_sel
add wave -noupdate -expand -group Inputs -expand -group Inputs -radix unsigned /writeback_tb/wbif/alu_done
add wave -noupdate -expand -group Inputs -expand -group {Load Inputs} -radix unsigned /writeback_tb/wbif/load_wdat
add wave -noupdate -expand -group Inputs -expand -group {Load Inputs} -radix unsigned /writeback_tb/wbif/load_reg_sel
add wave -noupdate -expand -group Inputs -expand -group {Load Inputs} -radix unsigned /writeback_tb/wbif/load_done
add wave -noupdate -expand -group Inputs -expand -group Branch -radix unsigned /writeback_tb/wbif/branch_spec
add wave -noupdate -expand -group Inputs -expand -group Branch -radix unsigned /writeback_tb/wbif/branch_correct
add wave -noupdate -expand -group Inputs -expand -group Branch -radix unsigned /writeback_tb/wbif/branch_mispredict
add wave -noupdate -expand -group WriteBack -radix unsigned /writeback_tb/DUT/wb_sel
add wave -noupdate -expand -group WriteBack -childformat {{/writeback_tb/wbif/wb_out.reg_en -radix unsigned} {/writeback_tb/wbif/wb_out.reg_sel -radix unsigned} {/writeback_tb/wbif/wb_out.wdat -radix unsigned}} -expand -subitemconfig {/writeback_tb/wbif/wb_out.reg_en {-height 16 -radix unsigned} /writeback_tb/wbif/wb_out.reg_sel {-height 16 -radix unsigned} /writeback_tb/wbif/wb_out.wdat {-height 16 -radix unsigned}} /writeback_tb/wbif/wb_out
add wave -noupdate -expand -group {ALU Buffer} -childformat {{/writeback_tb/DUT/alu_din.reg_en -radix unsigned} {/writeback_tb/DUT/alu_din.reg_sel -radix unsigned} {/writeback_tb/DUT/alu_din.wdat -radix unsigned}} -expand -subitemconfig {/writeback_tb/DUT/alu_din.reg_en {-height 16 -radix unsigned} /writeback_tb/DUT/alu_din.reg_sel {-height 16 -radix unsigned} /writeback_tb/DUT/alu_din.wdat {-height 16 -radix unsigned}} /writeback_tb/DUT/alu_din
add wave -noupdate -expand -group {ALU Buffer} -childformat {{/writeback_tb/DUT/alu_dout.reg_en -radix unsigned} {/writeback_tb/DUT/alu_dout.reg_sel -radix unsigned} {/writeback_tb/DUT/alu_dout.wdat -radix unsigned}} -expand -subitemconfig {/writeback_tb/DUT/alu_dout.reg_en {-height 16 -radix unsigned} /writeback_tb/DUT/alu_dout.reg_sel {-height 16 -radix unsigned} /writeback_tb/DUT/alu_dout.wdat {-height 16 -radix unsigned}} /writeback_tb/DUT/alu_dout
add wave -noupdate -expand -group {ALU Buffer} -radix unsigned /writeback_tb/DUT/alu_wen
add wave -noupdate -expand -group {ALU Buffer} -radix unsigned /writeback_tb/DUT/alu_ren
add wave -noupdate -expand -group {ALU Buffer} -radix unsigned /writeback_tb/DUT/alu_wptr
add wave -noupdate -expand -group {ALU Buffer} -radix unsigned /writeback_tb/DUT/alu_rptr
add wave -noupdate -expand -group {ALU Buffer} -radix unsigned /writeback_tb/DUT/alu_count
add wave -noupdate -expand -group {ALU Buffer} -radix unsigned /writeback_tb/DUT/alu_full
add wave -noupdate -expand -group {ALU Buffer} -radix unsigned /writeback_tb/DUT/alu_empty
add wave -noupdate -expand -group {ALU Buffer} /writeback_tb/DUT/alu_buffer
add wave -noupdate -expand -group {Load Buffer} -childformat {{/writeback_tb/DUT/load_din.reg_en -radix unsigned} {/writeback_tb/DUT/load_din.reg_sel -radix unsigned} {/writeback_tb/DUT/load_din.wdat -radix unsigned}} -expand -subitemconfig {/writeback_tb/DUT/load_din.reg_en {-height 16 -radix unsigned} /writeback_tb/DUT/load_din.reg_sel {-height 16 -radix unsigned} /writeback_tb/DUT/load_din.wdat {-height 16 -radix unsigned}} /writeback_tb/DUT/load_din
add wave -noupdate -expand -group {Load Buffer} -childformat {{/writeback_tb/DUT/load_dout.reg_en -radix unsigned} {/writeback_tb/DUT/load_dout.reg_sel -radix unsigned} {/writeback_tb/DUT/load_dout.wdat -radix unsigned}} -expand -subitemconfig {/writeback_tb/DUT/load_dout.reg_en {-height 16 -radix unsigned} /writeback_tb/DUT/load_dout.reg_sel {-height 16 -radix unsigned} /writeback_tb/DUT/load_dout.wdat {-height 16 -radix unsigned}} /writeback_tb/DUT/load_dout
add wave -noupdate -expand -group {Load Buffer} -radix unsigned /writeback_tb/DUT/load_wen
add wave -noupdate -expand -group {Load Buffer} -radix unsigned /writeback_tb/DUT/load_ren
add wave -noupdate -expand -group {Load Buffer} -radix unsigned /writeback_tb/DUT/load_wptr
add wave -noupdate -expand -group {Load Buffer} -radix unsigned /writeback_tb/DUT/load_rptr
add wave -noupdate -expand -group {Load Buffer} -radix unsigned /writeback_tb/DUT/load_count
add wave -noupdate -expand -group {Load Buffer} -radix unsigned /writeback_tb/DUT/load_empty
add wave -noupdate -expand -group {Load Buffer} -radix unsigned /writeback_tb/DUT/load_full
add wave -noupdate -expand -group {Load Buffer} /writeback_tb/DUT/load_buffer
add wave -noupdate -expand -group Speculative -radix unsigned /writeback_tb/DUT/spec_alu_wptr
add wave -noupdate -expand -group Speculative -radix unsigned /writeback_tb/DUT/spec_alu_count
add wave -noupdate -expand -group Speculative -radix unsigned /writeback_tb/DUT/state
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {59433 ps} 0}
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
WaveRestoreZoom {59377 ps} {76659 ps}
