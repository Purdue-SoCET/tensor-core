onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /timing_control_tb/tb_CLK
add wave -noupdate /timing_control_tb/tb_nRST
add wave -noupdate -expand -group {TB Signals} /timing_control_tb/tb_test_case
add wave -noupdate -expand -group {TB Signals} /timing_control_tb/tb_test_case_num
add wave -noupdate -expand -group {TB Signals} /timing_control_tb/tb_i
add wave -noupdate -expand -group {TB Signals} /timing_control_tb/tb_mismatch
add wave -noupdate -expand -group {TB Signals} /timing_control_tb/tb_check
add wave -noupdate -expand -group {Command State} /timing_control_tb/tb_cfsmif/cmd_state
add wave -noupdate -expand -group {Time Signals} /timing_control_tb/tb_timif/tACT_done
add wave -noupdate -expand -group {Time Signals} /timing_control_tb/tb_timif/tWR_done
add wave -noupdate -expand -group {Time Signals} /timing_control_tb/tb_timif/tRD_done
add wave -noupdate -expand -group {Time Signals} /timing_control_tb/tb_timif/tPRE_done
add wave -noupdate -expand -group {Time Signals} /timing_control_tb/tb_timif/tREF_done
add wave -noupdate -expand -group {Time Signals} /timing_control_tb/DUT/wr_en
add wave -noupdate -expand -group {Time Signals} /timing_control_tb/tb_timif/rf_req
add wave -noupdate -expand -group {Expected Time Signals} /timing_control_tb/tb_expected_timif/tACT_done
add wave -noupdate -expand -group {Expected Time Signals} /timing_control_tb/tb_expected_timif/tWR_done
add wave -noupdate -expand -group {Expected Time Signals} /timing_control_tb/tb_expected_timif/tRD_done
add wave -noupdate -expand -group {Expected Time Signals} /timing_control_tb/tb_expected_timif/tPRE_done
add wave -noupdate -expand -group {Expected Time Signals} /timing_control_tb/tb_expected_timif/tREF_done
add wave -noupdate -expand -group {Expected Time Signals} /timing_control_tb/tb_expected_timif/rf_req
add wave -noupdate -expand -group {Counter Signals} /timing_control_tb/DUT/time_counter/enable
add wave -noupdate -expand -group {Counter Signals} /timing_control_tb/DUT/time_counter/count_load
add wave -noupdate -expand -group {Counter Signals} /timing_control_tb/DUT/time_counter/count
add wave -noupdate -expand -group {Counter Signals} /timing_control_tb/DUT/time_counter/count_done
add wave -noupdate -expand -group {Counter Signals} /timing_control_tb/DUT/time_counter/next_count
add wave -noupdate -expand -group {Refresh Counter Signals} -radix unsigned /timing_control_tb/DUT/refresh_limit
add wave -noupdate -expand -group {Refresh Counter Signals} -radix unsigned /timing_control_tb/DUT/next_refresh_limit
add wave -noupdate -expand -group {Refresh Counter Signals} -radix unsigned /timing_control_tb/DUT/refresh_count
add wave -noupdate -expand -group {Refresh Counter Signals} -radix unsigned /timing_control_tb/DUT/next_refresh_count
add wave -noupdate /dram_pkg::tREFI
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {15 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 325
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
WaveRestoreZoom {0 ns} {751 ns}
