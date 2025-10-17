onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group {TB signals} /addr_mapper_tb/tb_CLK
add wave -noupdate -expand -group {TB signals} /addr_mapper_tb/tb_nRST
add wave -noupdate -expand -group {TB signals} /addr_mapper_tb/tb_test_case
add wave -noupdate -expand -group {TB signals} /addr_mapper_tb/tb_test_case_num
add wave -noupdate -expand -group {TB signals} /addr_mapper_tb/tb_i
add wave -noupdate -expand -group {TB signals} /addr_mapper_tb/tb_mismatch
add wave -noupdate -expand -group {TB signals} /addr_mapper_tb/tb_check
add wave -noupdate -expand -group {Address mapper if} /addr_mapper_tb/tb_amif/address
add wave -noupdate -expand -group {Address mapper if} /addr_mapper_tb/tb_amif/configs
add wave -noupdate -expand -group {Address mapper if} /addr_mapper_tb/tb_amif/rank
add wave -noupdate -expand -group {Address mapper if} /addr_mapper_tb/tb_amif/BG
add wave -noupdate -expand -group {Address mapper if} /addr_mapper_tb/tb_amif/bank
add wave -noupdate -expand -group {Address mapper if} /addr_mapper_tb/tb_amif/row
add wave -noupdate -expand -group {Address mapper if} /addr_mapper_tb/tb_amif/col
add wave -noupdate -expand -group {Address mapper if} /addr_mapper_tb/tb_amif/offset
add wave -noupdate -expand -group {Expected signals} /addr_mapper_tb/tb_expected_amif/address
add wave -noupdate -expand -group {Expected signals} /addr_mapper_tb/tb_expected_amif/configs
add wave -noupdate -expand -group {Expected signals} /addr_mapper_tb/tb_expected_amif/rank
add wave -noupdate -expand -group {Expected signals} /addr_mapper_tb/tb_expected_amif/BG
add wave -noupdate -expand -group {Expected signals} /addr_mapper_tb/tb_expected_amif/bank
add wave -noupdate -expand -group {Expected signals} /addr_mapper_tb/tb_expected_amif/row
add wave -noupdate -expand -group {Expected signals} /addr_mapper_tb/tb_expected_amif/col
add wave -noupdate -expand -group {Expected signals} /addr_mapper_tb/tb_expected_amif/offset
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
configure wave -namecolwidth 186
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
WaveRestoreZoom {99978445 ps} {100000628 ps}
