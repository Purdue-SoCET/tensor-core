onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /vreg_file_tb/vif/CLK
add wave -noupdate /vreg_file_tb/vif/nRST
add wave -noupdate /vreg_file_tb/#ublk#188361714#83/testname
add wave -noupdate -expand -group I/O /vreg_file_tb/vif/veggie_in
add wave -noupdate -expand -group I/O /vreg_file_tb/vif/veggie_out
add wave -noupdate -expand -group I/O /vreg_file_tb/vif/opbuff_out
add wave -noupdate -expand -group DBANK0 {/vreg_file_tb/dut/veggie/DATA_BANK_GEN[0]/DBANKi_db/mem}
add wave -noupdate -expand -group MBANK0 {/vreg_file_tb/dut/veggie/MASK_BANK_GEN[0]/MBANKi_mb/mem}
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/vs_bnum
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/vd_bnum
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/vms_bnum
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/vmd_bnum
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_rreqs
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_rpend
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_rpend_nxt
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_wreqs
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_wpend
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_wpend_nxt
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_mrreqs
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_mrpend
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_mrpend_nxt
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_mwreqs
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_mwpend
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_mwpend_nxt
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_in
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/bank_out
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/mbank_in
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/mbank_out
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/read_grants
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/mread_grants
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/conflict
add wave -noupdate -expand -group {Conflict Mgmt} /vreg_file_tb/dut/veggie/state
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {152 ns} 0}
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
WaveRestoreZoom {0 ns} {362 ns}
