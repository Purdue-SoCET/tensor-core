onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /backend_tb/PROG/bif/clk
add wave -noupdate /backend_tb/PROG/bif/n_rst
add wave -noupdate -expand -group Scheduler -color Magenta /backend_tb/DUT/bshif/sched_req
add wave -noupdate -expand -group Scheduler -color Magenta /backend_tb/DUT/bshif/sched_res
add wave -noupdate -expand -group Body /backend_tb/DUT/bshif/be_stall
add wave -noupdate -expand -group Body -expand -subitemconfig {{/backend_tb/DUT/bshif/be_req[0]} -expand} /backend_tb/DUT/bshif/be_req
add wave -noupdate -expand -group Body /backend_tb/DUT/bshif/be_res
add wave -noupdate -expand -group DRAM -color Yellow /backend_tb/DUT/bshif/dram_be_stall
add wave -noupdate -expand -group DRAM -color Yellow /backend_tb/DUT/bshif/be_dram_stall
add wave -noupdate -expand -group DRAM -color Yellow /backend_tb/DUT/bshif/be_dram_req
add wave -noupdate -expand -group DRAM -color Yellow -expand -subitemconfig {{/backend_tb/DUT/bshif/dram_be_res[0]} {-color Yellow -height 16 -expand} {/backend_tb/DUT/bshif/dram_be_res[0].valid} {-color Yellow -height 16} {/backend_tb/DUT/bshif/dram_be_res[0].write} {-color Yellow -height 16} {/backend_tb/DUT/bshif/dram_be_res[0].id} {-color Yellow -height 16} {/backend_tb/DUT/bshif/dram_be_res[0].rdata} {-color Yellow -height 16} {/backend_tb/DUT/bshif/dram_be_res[1]} {-color Yellow -height 16}} /backend_tb/DUT/bshif/dram_be_res
add wave -noupdate -expand -group Swizzle /backend_tb/DUT/swizzle_metadata/swizz/row_or_col
add wave -noupdate -expand -group Swizzle /backend_tb/DUT/swizzle_metadata/swizz/spad_addr
add wave -noupdate -expand -group Swizzle -radix unsigned /backend_tb/DUT/swizzle_metadata/swizz/num_rows
add wave -noupdate -expand -group Swizzle /backend_tb/DUT/swizzle_metadata/swizz/num_cols
add wave -noupdate -expand -group Swizzle /backend_tb/DUT/swizzle_metadata/swizz/row_id
add wave -noupdate -expand -group Swizzle /backend_tb/DUT/swizzle_metadata/swizz/col_id
add wave -noupdate -expand -group Swizzle -childformat {{/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask -radix unsigned -childformat {{{[31]} -radix unsigned} {{[30]} -radix unsigned} {{[29]} -radix unsigned} {{[28]} -radix unsigned} {{[27]} -radix unsigned} {{[26]} -radix unsigned} {{[25]} -radix unsigned} {{[24]} -radix unsigned} {{[23]} -radix unsigned} {{[22]} -radix unsigned} {{[21]} -radix unsigned} {{[20]} -radix unsigned} {{[19]} -radix unsigned} {{[18]} -radix unsigned} {{[17]} -radix unsigned} {{[16]} -radix unsigned} {{[15]} -radix unsigned} {{[14]} -radix unsigned} {{[13]} -radix unsigned} {{[12]} -radix unsigned} {{[11]} -radix unsigned} {{[10]} -radix unsigned} {{[9]} -radix unsigned} {{[8]} -radix unsigned} {{[7]} -radix unsigned} {{[6]} -radix unsigned} {{[5]} -radix unsigned} {{[4]} -radix unsigned} {{[3]} -radix unsigned} {{[2]} -radix unsigned} {{[1]} -radix unsigned} {{[0]} -radix unsigned}}}} -subitemconfig {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask {-height 16 -radix unsigned -childformat {{{[31]} -radix unsigned} {{[30]} -radix unsigned} {{[29]} -radix unsigned} {{[28]} -radix unsigned} {{[27]} -radix unsigned} {{[26]} -radix unsigned} {{[25]} -radix unsigned} {{[24]} -radix unsigned} {{[23]} -radix unsigned} {{[22]} -radix unsigned} {{[21]} -radix unsigned} {{[20]} -radix unsigned} {{[19]} -radix unsigned} {{[18]} -radix unsigned} {{[17]} -radix unsigned} {{[16]} -radix unsigned} {{[15]} -radix unsigned} {{[14]} -radix unsigned} {{[13]} -radix unsigned} {{[12]} -radix unsigned} {{[11]} -radix unsigned} {{[10]} -radix unsigned} {{[9]} -radix unsigned} {{[8]} -radix unsigned} {{[7]} -radix unsigned} {{[6]} -radix unsigned} {{[5]} -radix unsigned} {{[4]} -radix unsigned} {{[3]} -radix unsigned} {{[2]} -radix unsigned} {{[1]} -radix unsigned} {{[0]} -radix unsigned}}} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[31]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[30]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[29]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[28]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[27]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[26]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[25]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[24]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[23]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[22]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[21]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[20]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[19]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[18]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[17]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[16]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[15]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[14]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[13]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[12]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[11]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[10]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[9]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[8]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[7]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[6]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[5]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[4]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[3]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[2]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[1]} {-radix unsigned} {/backend_tb/DUT/swizzle_metadata/swizz/xbar_desc.shift_mask[0]} {-radix unsigned}} /backend_tb/DUT/swizzle_metadata/swizz/xbar_desc
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix unsigned /backend_tb/DUT/be_id
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix unsigned /backend_tb/DUT/uuid
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix unsigned /backend_tb/DUT/nxt_uuid
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix unsigned /backend_tb/DUT/sub_uuid
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix unsigned /backend_tb/DUT/nxt_sub_uuid
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix unsigned /backend_tb/DUT/num_request
add wave -noupdate -expand -group {Internal Signals} -color Cyan /backend_tb/DUT/initial_request_done
add wave -noupdate -expand -group {Internal Signals} -color Cyan /backend_tb/DUT/nxt_initial_request_done
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix unsigned /backend_tb/DUT/schedule_request_counter
add wave -noupdate -expand -group {Internal Signals} -color Cyan -radix unsigned /backend_tb/DUT/nxt_schedule_request_counter
add wave -noupdate -expand -group {Internal Signals} -color Cyan /backend_tb/DUT/nxt_sched_res_valid
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange /backend_tb/DUT/be_dr_req_q/dram_queue_full
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange /backend_tb/DUT/be_dr_req_q/num_request
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange /backend_tb/DUT/be_dr_req_q/burst_complete
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange /backend_tb/DUT/be_dr_req_q/transaction_complete
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange -radix unsigned /backend_tb/DUT/dr_rd_req_q/dram_req_latch_block
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange /backend_tb/DUT/dr_rd_req_q/nxt_dram_head_latch_set
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange /backend_tb/DUT/dr_rd_req_q/nxt_dram_tail_latch_set
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange -radix unsigned /backend_tb/DUT/dr_rd_req_q/fifo_head
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange -radix unsigned /backend_tb/DUT/dr_rd_req_q/nxt_fifo_head
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange -radix unsigned /backend_tb/DUT/dr_rd_req_q/fifo_tail
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange -radix unsigned /backend_tb/DUT/dr_rd_req_q/nxt_fifo_tail
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange -radix unsigned /backend_tb/DUT/dr_rd_req_q/request_completed_counter
add wave -noupdate -expand -group DRAM_REQUEST_QUEUE -color Orange -radix unsigned /backend_tb/DUT/dr_rd_req_q/nxt_request_completed_counter
add wave -noupdate -expand -group SRAM_WRITE_REQUEST_LATCH /backend_tb/DUT/sr_wr_l/num_request
add wave -noupdate -expand -group SRAM_WRITE_REQUEST_LATCH /backend_tb/DUT/sr_wr_l/sram_write_req_latched
add wave -noupdate -expand -group SRAM_WRITE_REQUEST_LATCH /backend_tb/DUT/be_sr_wr_latch/sram_write_latch
add wave -noupdate -expand -group SRAM_WRITE_REQUEST_LATCH /backend_tb/DUT/be_sr_wr_latch/nxt_sram_write_latch
add wave -noupdate -expand -group SRAM_WRITE_REQUEST_LATCH /backend_tb/DUT/be_sr_wr_latch/request_completed_counter
add wave -noupdate -expand -group SRAM_WRITE_REQUEST_LATCH /backend_tb/DUT/be_sr_wr_latch/nxt_request_completed_counter
add wave -noupdate -expand -group DRAM_WRITE_REQUEST_LATCH /backend_tb/DUT/dr_wr_l/num_request
add wave -noupdate -expand -group DRAM_WRITE_REQUEST_LATCH /backend_tb/DUT/dr_wr_l/dram_write_req_latched
add wave -noupdate -expand -group DRAM_WRITE_REQUEST_LATCH /backend_tb/DUT/dr_wr_latch/dram_write_latch
add wave -noupdate -expand -group DRAM_WRITE_REQUEST_LATCH /backend_tb/DUT/dr_wr_latch/nxt_dram_write_latch
add wave -noupdate -expand -group DRAM_WRITE_REQUEST_LATCH /backend_tb/DUT/dr_wr_latch/request_completed_counter
add wave -noupdate -expand -group DRAM_WRITE_REQUEST_LATCH /backend_tb/DUT/dr_wr_latch/nxt_request_completed_counter
add wave -noupdate /backend_tb/PROG/bif/sched_req
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {141 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 187
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
WaveRestoreZoom {19 ps} {445 ps}
