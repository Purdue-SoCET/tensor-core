onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -color Salmon /fu_alu_tb/tb_test_case
add wave -noupdate -expand -group Inputs -color Cyan /fu_alu_tb/aluif/aluop
add wave -noupdate -expand -group Inputs -color Cyan -radix hexadecimal /fu_alu_tb/aluif/port_a
add wave -noupdate -expand -group Inputs -color Cyan -radix hexadecimal /fu_alu_tb/aluif/port_b
add wave -noupdate -expand -group Outputs -color {Medium Slate Blue} -radix hexadecimal /fu_alu_tb/aluif/port_output
add wave -noupdate -expand -group Outputs -color {Medium Slate Blue} /fu_alu_tb/aluif/zero
add wave -noupdate -expand -group Outputs -color {Medium Slate Blue} /fu_alu_tb/aluif/negative
add wave -noupdate -expand -group Outputs -color {Medium Slate Blue} /fu_alu_tb/aluif/overflow
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {254 ns} 0}
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
WaveRestoreZoom {50 ns} {1050 ns}
