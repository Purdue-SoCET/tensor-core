onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /vls_tb/DUT/CLK
add wave -noupdate /vls_tb/DUT/nRST
add wave -noupdate /vls_tb/casenum
add wave -noupdate /vls_tb/casename
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/valid
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/imm_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/imm_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/vd_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/vd_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/rs1_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/rs1_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/row_col_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/row_col_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/num_rows_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/num_rows_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/num_cols_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/num_cols_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/id_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/id_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/load_data_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/load_data_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/op
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/v2_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/v2_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/vec_res
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/ready_in
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_store_data_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_store_data_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_op
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_row_col_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_row_col_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_num_rows_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_num_rows_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_num_cols_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_num_cols_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_id_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_id_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_addr_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_addr_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_load_data_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/sp_load_data_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/wb_vd_a
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/wb_vd_b
add wave -noupdate -expand -group {VLS Signals} -color Cyan /vls_tb/vlsif/ready_out
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/fifo_full_a
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/fifo_empty_a
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/fifo_shift_a
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/fifo_wr_a
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/fifo_dout_a
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/fifo_full_b
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/fifo_empty_b
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/fifo_shift_b
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/fifo_wr_b
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/fifo_dout_b
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/can_issue_a
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/can_issue_b
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/any_outstanding
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/state
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/next_state
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/imm_a_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/imm_b_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/vd_a_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/vd_b_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/rs1_a_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/rs1_b_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/row_col_a_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/row_col_b_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/num_rows_a_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/num_rows_b_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/num_cols_a_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/num_cols_b_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/id_a_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/id_b_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/op_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/v2_a_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/v2_b_r
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/addr_a_n
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/addr_b_n
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/load_vec_a_packed
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/load_vec_b_packed
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/out_vec_a_packed
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/out_vec_b_packed
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/d_full_a
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/d_empty_a
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/d_shift_a
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/d_wr_a
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/d_dout_a
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/d_full_b
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/d_empty_b
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/d_shift_b
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/d_wr_b
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/d_dout_b
add wave -noupdate -expand -group {VLS Internal Signals} /vls_tb/DUT/stall
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/wr_en
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/shift
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/din
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/dout
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/empty
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/full
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/mem
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/wptr
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/rptr
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/wptr_n
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/rptr_n
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/do_write
add wave -noupdate -expand -group {VD Queue A} /vls_tb/DUT/qA/do_read
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/wr_en
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/shift
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/din
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/dout
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/empty
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/full
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/mem
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/wptr
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/rptr
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/wptr_n
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/rptr_n
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/do_write
add wave -noupdate -expand -group {VD Queue B} /vls_tb/DUT/qB/do_read
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {160 ns} 0}
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
WaveRestoreZoom {0 ns} {252 ns}
