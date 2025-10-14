onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -color {Light Steel Blue} /veggie_tb/#ublk#232778258#91/testname
add wave -noupdate -expand -group {IO Signals} -color White -expand -subitemconfig {/veggie_tb/vif/veggie_in.vd {-color White -height 16} /veggie_tb/vif/veggie_in.vdata {-color White -height 16} /veggie_tb/vif/veggie_in.WEN {-color White -height 16} /veggie_tb/vif/veggie_in.vs {-color White -height 16} /veggie_tb/vif/veggie_in.REN {-color White -height 16} /veggie_tb/vif/veggie_in.vmd {-color White -height 16} /veggie_tb/vif/veggie_in.mvdata {-color White -height 16} /veggie_tb/vif/veggie_in.MWEN {-color White -height 16} /veggie_tb/vif/veggie_in.vms {-color White -height 16} /veggie_tb/vif/veggie_in.MREN {-color White -height 16}} /veggie_tb/vif/veggie_in
add wave -noupdate -expand -group {IO Signals} -color White -expand -subitemconfig {/veggie_tb/vif/veggie_out.vreg {-color White -height 16 -expand} {/veggie_tb/vif/veggie_out.vreg[3]} {-color White} {/veggie_tb/vif/veggie_out.vreg[2]} {-color White} {/veggie_tb/vif/veggie_out.vreg[1]} {-color White} {/veggie_tb/vif/veggie_out.vreg[0]} {-color White} /veggie_tb/vif/veggie_out.vmask {-color White -height 16} /veggie_tb/vif/veggie_out.ready {-color White -height 16}} /veggie_tb/vif/veggie_out
add wave -noupdate -expand -group {IO Signals} -color White /veggie_tb/vif/CLK
add wave -noupdate -expand -group {IO Signals} -color White /veggie_tb/vif/nRST
add wave -noupdate -expand -group BankMap /veggie_tb/dut/vs_bnum
add wave -noupdate -expand -group BankMap /veggie_tb/dut/vd_bnum
add wave -noupdate -expand -group BankMap /veggie_tb/dut/vms_bnum
add wave -noupdate -expand -group BankMap /veggie_tb/dut/vmd_bnum
add wave -noupdate -expand -group {Request Tracking} /veggie_tb/dut/bank_rreqs
add wave -noupdate -expand -group {Request Tracking} -subitemconfig {{/veggie_tb/dut/bank_wreqs[0]} -expand} /veggie_tb/dut/bank_wreqs
add wave -noupdate -expand -group {Request Tracking} /veggie_tb/dut/bank_mrreqs
add wave -noupdate -expand -group {Request Tracking} /veggie_tb/dut/bank_mwreqs
add wave -noupdate -expand -group {Bank Input} -expand -subitemconfig {{/veggie_tb/dut/bank_in[2]} -expand} /veggie_tb/dut/bank_in
add wave -noupdate -expand -group {Bank Input} /veggie_tb/dut/mbank_in
add wave -noupdate -expand -group BANK0 {/veggie_tb/dut/DATA_BANK_GEN[0]/DBANKi_db/clk}
add wave -noupdate -expand -group BANK0 {/veggie_tb/dut/DATA_BANK_GEN[0]/DBANKi_db/ren}
add wave -noupdate -expand -group BANK0 {/veggie_tb/dut/DATA_BANK_GEN[0]/DBANKi_db/raddr}
add wave -noupdate -expand -group BANK0 {/veggie_tb/dut/DATA_BANK_GEN[0]/DBANKi_db/rdata}
add wave -noupdate -expand -group BANK0 {/veggie_tb/dut/DATA_BANK_GEN[0]/DBANKi_db/wen}
add wave -noupdate -expand -group BANK0 {/veggie_tb/dut/DATA_BANK_GEN[0]/DBANKi_db/waddr}
add wave -noupdate -expand -group BANK0 {/veggie_tb/dut/DATA_BANK_GEN[0]/DBANKi_db/wdata}
add wave -noupdate -expand -group BANK0 {/veggie_tb/dut/DATA_BANK_GEN[0]/DBANKi_db/wstrb}
add wave -noupdate -expand -group BANK0 -expand {/veggie_tb/dut/DATA_BANK_GEN[0]/DBANKi_db/mem}
add wave -noupdate -expand -group BANK1 {/veggie_tb/dut/DATA_BANK_GEN[1]/DBANKi_db/mem}
add wave -noupdate -expand -group BANK2 {/veggie_tb/dut/DATA_BANK_GEN[2]/DBANKi_db/mem}
add wave -noupdate -expand -group BANK3 {/veggie_tb/dut/DATA_BANK_GEN[3]/DBANKi_db/mem}
add wave -noupdate -expand -group MASK0 -expand {/veggie_tb/dut/MASK_BANK_GEN[0]/MBANKi_mb/mem}
add wave -noupdate -expand -group MASK1 {/veggie_tb/dut/MASK_BANK_GEN[1]/MBANKi_mb/mem}
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/vs_bnum
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/vd_bnum
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/vms_bnum
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/vmd_bnum
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_rreqs
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_rpend
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_rpend_nxt
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_wreqs
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_wpend
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_wpend_nxt
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_mrreqs
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_mrpend
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_mrpend_nxt
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_mwreqs
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_mwpend
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_mwpend_nxt
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_in
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/mbank_in
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_rdata
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/bank_mrdata
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/read_grants
add wave -noupdate -expand -group {CNTL SIGNALS} /veggie_tb/dut/mread_grants
add wave -noupdate -expand -group {State Logic} /veggie_tb/dut/d_conflict
add wave -noupdate -expand -group {State Logic} /veggie_tb/dut/m_conflict
add wave -noupdate -expand -group {State Logic} /veggie_tb/dut/state
add wave -noupdate -expand -group {State Logic} /veggie_tb/dut/state_nxt
add wave -noupdate -expand -group {State Logic} /veggie_tb/dut/conflict
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {590 ns} 0} {{Cursor 2} {186 ns} 0}
quietly wave cursor active 2
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
WaveRestoreZoom {183 ns} {251 ns}
