onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group Inputs /scratchpad_bank_tb/spif/wFIFO_WEN
add wave -noupdate -expand -group Inputs /scratchpad_bank_tb/spif/wFIFO_wdata
add wave -noupdate -expand -group Inputs /scratchpad_bank_tb/spif/rFIFO_WEN
add wave -noupdate -expand -group Inputs /scratchpad_bank_tb/spif/rFIFO_wdata
add wave -noupdate -expand -group Inputs /scratchpad_bank_tb/spif/dramFIFO_REN
add wave -noupdate -expand -group Inputs /scratchpad_bank_tb/spif/gemmFIFO_REN
add wave -noupdate -expand -group Outputs /scratchpad_bank_tb/spif/wFIFO_full
add wave -noupdate -expand -group Outputs /scratchpad_bank_tb/spif/rFIFO_full
add wave -noupdate -expand -group Outputs /scratchpad_bank_tb/spif/gemm_complete
add wave -noupdate -expand -group Outputs /scratchpad_bank_tb/spif/dramFIFO_rdata
add wave -noupdate -expand -group Outputs /scratchpad_bank_tb/spif/dramFIFO_empty
add wave -noupdate -expand -group Outputs /scratchpad_bank_tb/spif/gemmFIFO_rdata
add wave -noupdate -expand -group Outputs /scratchpad_bank_tb/spif/gemmFIFO_empty
add wave -noupdate -expand -group Outputs /scratchpad_bank_tb/spif/load_complete
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {219390 ps} 0}
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
WaveRestoreZoom {0 ps} {277080 ps}
