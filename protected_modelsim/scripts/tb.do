onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb/counter/CLK
add wave -noupdate /tb/counter/nRST
add wave -noupdate /tb/counter/clear
add wave -noupdate /tb/counter/count_enable
add wave -noupdate /tb/counter/overflow_val
add wave -noupdate -expand -group timing_trk -radix decimal /tb/counter/count_out
add wave -noupdate -expand -group timing_trk -radix decimal /tb/timing_trk
add wave -noupdate /tb/counter/overflow_flag
add wave -noupdate -group iDDR4 /tb/iDDR4/CONFIGURED_DQ_BITS
add wave -noupdate -group iDDR4 /tb/iDDR4/CONFIGURED_DQS_BITS
add wave -noupdate -group iDDR4 /tb/iDDR4/CONFIGURED_DM_BITS
add wave -noupdate -group iDDR4 /tb/iDDR4/CK
add wave -noupdate -group iDDR4 /tb/iDDR4/ACT_n
add wave -noupdate -group iDDR4 /tb/iDDR4/RAS_n_A16
add wave -noupdate -group iDDR4 /tb/iDDR4/CAS_n_A15
add wave -noupdate -group iDDR4 /tb/iDDR4/WE_n_A14
add wave -noupdate -group iDDR4 /tb/iDDR4/ALERT_n
add wave -noupdate -group iDDR4 /tb/iDDR4/PARITY
add wave -noupdate -group iDDR4 /tb/iDDR4/RESET_n
add wave -noupdate -group iDDR4 /tb/iDDR4/TEN
add wave -noupdate -group iDDR4 /tb/iDDR4/CS_n
add wave -noupdate -group iDDR4 /tb/iDDR4/CKE
add wave -noupdate -group iDDR4 /tb/iDDR4/ODT
add wave -noupdate -group iDDR4 /tb/iDDR4/C
add wave -noupdate -group iDDR4 /tb/iDDR4/BG
add wave -noupdate -group iDDR4 /tb/iDDR4/BA
add wave -noupdate -group iDDR4 /tb/iDDR4/ADDR
add wave -noupdate -group iDDR4 /tb/iDDR4/ADDR_17
add wave -noupdate -group iDDR4 /tb/iDDR4/DM_n
add wave -noupdate -group iDDR4 /tb/iDDR4/DQ
add wave -noupdate -group iDDR4 /tb/iDDR4/DQS_t
add wave -noupdate -group iDDR4 /tb/iDDR4/DQS_c
add wave -noupdate -group iDDR4 /tb/iDDR4/ZQ
add wave -noupdate -group iDDR4 /tb/iDDR4/PWR
add wave -noupdate -group iDDR4 /tb/iDDR4/VREF_CA
add wave -noupdate -group iDDR4 /tb/iDDR4/VREF_DQ
add wave -noupdate -expand -group Result /tb/dm_fifo
add wave -noupdate -expand -group Result /tb/dq_fifo
add wave -noupdate -expand -group Result /tb/q0
add wave -noupdate -expand -group Result /tb/q1
add wave -noupdate -expand -group Result /tb/q2
add wave -noupdate -expand -group Result /tb/q3
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {2902263 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 83
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
WaveRestoreZoom {2877755 ps} {2902315 ps}
