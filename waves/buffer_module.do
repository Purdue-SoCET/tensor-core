onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /buffer_module_tb/dut/CLK
add wave -noupdate /buffer_module_tb/dut/nRST
add wave -noupdate /buffer_module_tb/dut/BUFFER_WIDTH
add wave -noupdate /buffer_module_tb/dut/BUFFER_DEPTH
add wave -noupdate /buffer_module_tb/dut/write_en
add wave -noupdate /buffer_module_tb/dut/read_en
add wave -noupdate -radix decimal /buffer_module_tb/dut/din
add wave -noupdate -radix decimal /buffer_module_tb/dut/dout
add wave -noupdate /buffer_module_tb/dut/full
add wave -noupdate /buffer_module_tb/dut/empty
add wave -noupdate /buffer_module_tb/dut/read_idx
add wave -noupdate /buffer_module_tb/dut/write_idx
add wave -noupdate -childformat {{{/buffer_module_tb/dut/shift_reg[7]} -radix decimal} {{/buffer_module_tb/dut/shift_reg[6]} -radix decimal} {{/buffer_module_tb/dut/shift_reg[5]} -radix decimal} {{/buffer_module_tb/dut/shift_reg[4]} -radix decimal} {{/buffer_module_tb/dut/shift_reg[3]} -radix decimal} {{/buffer_module_tb/dut/shift_reg[2]} -radix decimal} {{/buffer_module_tb/dut/shift_reg[1]} -radix decimal} {{/buffer_module_tb/dut/shift_reg[0]} -radix decimal}} -expand -subitemconfig {{/buffer_module_tb/dut/shift_reg[7]} {-height 16 -radix decimal} {/buffer_module_tb/dut/shift_reg[6]} {-height 16 -radix decimal} {/buffer_module_tb/dut/shift_reg[5]} {-height 16 -radix decimal} {/buffer_module_tb/dut/shift_reg[4]} {-height 16 -radix decimal} {/buffer_module_tb/dut/shift_reg[3]} {-height 16 -radix decimal} {/buffer_module_tb/dut/shift_reg[2]} {-height 16 -radix decimal} {/buffer_module_tb/dut/shift_reg[1]} {-height 16 -radix decimal} {/buffer_module_tb/dut/shift_reg[0]} {-height 16 -radix decimal}} /buffer_module_tb/dut/shift_reg
add wave -noupdate /buffer_module_tb/dut/count
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {423046 ps} 0}
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
WaveRestoreZoom {0 ps} {714 ns}
