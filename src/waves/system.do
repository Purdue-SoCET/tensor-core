onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /system_tb/CLK
add wave -noupdate /system_tb/nRST
add wave -noupdate -divider {Instruction Operations}
add wave -noupdate -group icache /system_tb/DUT/MS/ICACHE/icache_format
add wave -noupdate -group icache /system_tb/DUT/MS/ICACHE/icache
add wave -noupdate -group icache /system_tb/DUT/MS/ICACHE/nxt_icache
add wave -noupdate -group icache /system_tb/DUT/MS/ICACHE/icache_state
add wave -noupdate -group icache /system_tb/DUT/MS/ICACHE/nxt_icache_state
add wave -noupdate -expand -group {datapath enables} /system_tb/DUT/DP/eif/bfu_enable
add wave -noupdate -expand -group {datapath enables} /system_tb/DUT/DP/eif/salu_enable
add wave -noupdate -expand -group {datapath enables} /system_tb/DUT/DP/eif/sls_enable
add wave -noupdate -expand -group {datapath enables} /system_tb/DUT/DP/eif/mls_enable
add wave -noupdate -expand -group {datapath enables} /system_tb/DUT/DP/eif/gemm_enable
add wave -noupdate -expand -group {datapath instr signals} -radix unsigned /system_tb/DUT/dcif/imemaddr
add wave -noupdate -expand -group {datapath instr signals} -radix hexadecimal /system_tb/DUT/dcif/imemload
add wave -noupdate -expand -group {datapath instr signals} /system_tb/DUT/dcif/imemREN
add wave -noupdate -expand -group {fetch if} /system_tb/DUT/DP/fif/imemREN
add wave -noupdate -expand -group {fetch if} /system_tb/DUT/DP/fif/imemload
add wave -noupdate -expand -group {fetch if} -radix unsigned /system_tb/DUT/DP/fif/imemaddr
add wave -noupdate -expand -group {fetch if} /system_tb/DUT/DP/fif/update_btb
add wave -noupdate -expand -group {fetch if} /system_tb/DUT/DP/fif/branch_outcome
add wave -noupdate -expand -group {fetch if} /system_tb/DUT/DP/fif/predicted_outcome
add wave -noupdate -expand -group {fetch if} -expand -group fetch /system_tb/DUT/DP/FETCH/fif/freeze
add wave -noupdate -expand -group {fetch if} -expand -group fetch /system_tb/DUT/DP/FETCH/fif/misprediction
add wave -noupdate -expand -group {fetch if} -expand -group fetch /system_tb/DUT/DP/FETCH/fif/imemREN
add wave -noupdate -expand -group {fetch if} -expand -group fetch /system_tb/DUT/DP/FETCH/fif/br_jump
add wave -noupdate -expand -group {fetch if} -expand -group fetch /system_tb/DUT/DP/FETCH/fetch_unit/ihit
add wave -noupdate -expand -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fif/imemload
add wave -noupdate -expand -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fif/pc_prediction
add wave -noupdate -expand -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fetch_unit/next_pc
add wave -noupdate -expand -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fetch_unit/pc_reg
add wave -noupdate -expand -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fif/pc
add wave -noupdate -expand -group {fetch if} -expand -group fetch -radix hexadecimal /system_tb/DUT/DP/FETCH/fif/instr
add wave -noupdate -expand -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fif/correct_pc
add wave -noupdate -expand -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fif/imemaddr
add wave -noupdate -expand -group {fetch if} -radix unsigned /system_tb/DUT/DP/fif/update_pc
add wave -noupdate -expand -group {fetch if} /system_tb/DUT/DP/fif/branch_target
add wave -noupdate -expand -group {fetch if} /system_tb/DUT/DP/FETCH/missed
add wave -noupdate -expand -group {fetch if} -radix unsigned /system_tb/DUT/DP/FETCH/save_pc
add wave -noupdate -expand -group {fetch if} /system_tb/DUT/DP/fif/freeze
add wave -noupdate -expand -group {fetch if} /system_tb/DUT/DP/fif/jump
add wave -noupdate -expand -group {fetch if} /system_tb/DUT/DP/fif/br_jump
add wave -noupdate -expand -group {fetch if} /system_tb/DUT/DP/fif/misprediction
add wave -noupdate -expand -group {fetch if} -radix unsigned /system_tb/DUT/DP/fif/correct_pc
add wave -noupdate -expand -group {fetch if} -radix unsigned /system_tb/DUT/DP/fif/pc
add wave -noupdate -expand -group {fetch if} /system_tb/DUT/DP/fif/instr
add wave -noupdate -expand -group {fif interface fetch} /system_tb/DUT/DP/FETCH/fif/instr
add wave -noupdate -expand -group {fif interface fetch} /system_tb/DUT/DP/FETCH/fif/imemREN
add wave -noupdate -expand -group {fif interface fetch} -radix unsigned /system_tb/DUT/DP/FETCH/fif/imemaddr
add wave -noupdate -expand -group {fif interface fetch} /system_tb/DUT/DP/FETCH/fif/imemload
add wave -noupdate -expand -group {fif interface fetch} -radix unsigned /system_tb/DUT/DP/FETCH/fif/pc
add wave -noupdate -expand -group {fif interface fetch} -radix unsigned /system_tb/DUT/DP/FETCH/fetch_unit/next_pc
add wave -noupdate -expand -group {fif interface fetch} /system_tb/DUT/DP/FETCH/fif/correct_pc
add wave -noupdate -expand -group icache-arbiter /system_tb/DUT/MS/ARB/acif/ramREN
add wave -noupdate -expand -group icache-arbiter -radix unsigned /system_tb/DUT/MS/ARB/acif/ramaddr
add wave -noupdate -expand -group icache-arbiter /system_tb/DUT/MS/ARB/icache_load
add wave -noupdate -divider {Scalar Operations}
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/enable
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/branch
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/branch_outcome
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/predicted_outcome
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/miss
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/update_btb
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/resolved
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/br_jump
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/branch_type
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/j_type
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/reg_a
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/reg_b
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/current_pc
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/imm
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/updated_pc
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/correct_pc
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/update_pc
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/branch_target
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/jump_dest
add wave -noupdate -expand -group branch_fu -expand -group fub_if /system_tb/DUT/DP/EXECUTE/fubif/jump_wdat
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/zero
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/actual_outcome
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/resolved
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/delay
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/temp_branch_outcome
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/temp_miss
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/temp_correct_pc
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/temp_branch_target
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/temp_update_btb
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/temp_update_pc
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/temp_resolved
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/temp_jump_dest
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/temp_jump_wdat
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/temp_br_jump
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/btb_updated
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/last_branch_pc
add wave -noupdate -expand -group branch_fu /system_tb/DUT/DP/EXECUTE/BFU/updated_pc
add wave -noupdate -childformat {{{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[31]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[30]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[24]} -radix hexadecimal} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[18]} -radix hexadecimal} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[16]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[13]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[12]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[9]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[7]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[6]} -radix hexadecimal} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[5]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[4]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[3]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[2]} -radix hexadecimal} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[1]} -radix unsigned}} -subitemconfig {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[31]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[30]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[24]} {-height 16 -radix hexadecimal} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[18]} {-height 16 -radix hexadecimal} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[16]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[13]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[12]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[9]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[7]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[6]} {-height 16 -radix hexadecimal} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[5]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[4]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[3]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[2]} {-height 16 -radix hexadecimal} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[1]} {-height 16 -radix unsigned}} /system_tb/DUT/DP/SCOREBOARD/IS/RF/register
add wave -noupdate -expand -group dispatch -childformat {{/system_tb/DUT/DP/SCOREBOARD/diif/fetch.br_pc -radix unsigned}} -expand -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/diif/fetch.br_pc {-height 16 -radix unsigned}} /system_tb/DUT/DP/SCOREBOARD/diif/fetch
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/DI/RSTS/status
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/branch_resolved
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/branch_miss
add wave -noupdate -expand -group dispatch -expand -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/diif/fust_s.busy -expand /system_tb/DUT/DP/SCOREBOARD/diif/fust_s.op -expand {/system_tb/DUT/DP/SCOREBOARD/diif/fust_s.op[2]} -expand {/system_tb/DUT/DP/SCOREBOARD/diif/fust_s.op[1]} -expand {/system_tb/DUT/DP/SCOREBOARD/diif/fust_s.op[0]} -expand} /system_tb/DUT/DP/SCOREBOARD/diif/fust_s
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/DI/jump
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/DI/n_jump
add wave -noupdate -expand -group dispatch -expand -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/diif/fust_m.op -expand} /system_tb/DUT/DP/SCOREBOARD/diif/fust_m
add wave -noupdate -expand -group dispatch -expand -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/diif/fust_g.op -expand} /system_tb/DUT/DP/SCOREBOARD/diif/fust_g
add wave -noupdate -expand -group dispatch -expand /system_tb/DUT/DP/SCOREBOARD/diif/fust_state
add wave -noupdate -expand -group dispatch -radix unsigned /system_tb/DUT/DP/SCOREBOARD/DI/m_rs1
add wave -noupdate -expand -group dispatch -radix unsigned /system_tb/DUT/DP/SCOREBOARD/DI/m_rs2
add wave -noupdate -expand -group dispatch -radix unsigned /system_tb/DUT/DP/SCOREBOARD/DI/m_rs3
add wave -noupdate -expand -group dispatch -childformat {{/system_tb/DUT/DP/SCOREBOARD/diif/wb.s_rw -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/diif/wb.load_done -radix unsigned}} -expand -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/diif/wb.s_rw {-height 16 -radix unsigned} /system_tb/DUT/DP/SCOREBOARD/diif/wb.load_done {-height 16 -radix unsigned}} /system_tb/DUT/DP/SCOREBOARD/diif/wb
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/fu_ex
add wave -noupdate -expand -group dispatch -radix unsigned /system_tb/DUT/DP/SCOREBOARD/DI/m_rd
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/DI/dispatch.fust_m.op.md
add wave -noupdate -expand -group dispatch -group rstmif /system_tb/DUT/DP/SCOREBOARD/DI/rstmif/di_sel
add wave -noupdate -expand -group dispatch -group rstmif /system_tb/DUT/DP/SCOREBOARD/DI/rstmif/di_write
add wave -noupdate -expand -group dispatch -group rstmif /system_tb/DUT/DP/SCOREBOARD/DI/rstmif/di_tag
add wave -noupdate -expand -group dispatch -group rstmif /system_tb/DUT/DP/SCOREBOARD/DI/rstmif/wb_sel
add wave -noupdate -expand -group dispatch -group rstmif /system_tb/DUT/DP/SCOREBOARD/DI/rstmif/wb_write
add wave -noupdate -expand -group dispatch -group rstmif /system_tb/DUT/DP/SCOREBOARD/DI/rstmif/status
add wave -noupdate -expand -group dispatch -group {scalar rst} -expand -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/DI/RSTS/status.idx -expand} /system_tb/DUT/DP/SCOREBOARD/DI/RSTS/status
add wave -noupdate -expand -group dispatch -group {matrix rst} -expand -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/DI/RSTM/status.idx -expand} /system_tb/DUT/DP/SCOREBOARD/DI/RSTM/status
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/DI/spec
add wave -noupdate -expand -group dispatch -childformat {{/system_tb/DUT/DP/SCOREBOARD/diif/out.n_br_pc -radix unsigned}} -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/diif/out.n_br_pc {-height 16 -radix unsigned}} /system_tb/DUT/DP/SCOREBOARD/diif/out
add wave -noupdate -expand -group dispatch -childformat {{/system_tb/DUT/DP/SCOREBOARD/diif/n_fust_s.rd -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/diif/n_fust_s.rs1 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/diif/n_fust_s.rs2 -radix unsigned}} -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/diif/n_fust_s.rd {-height 16 -radix unsigned} /system_tb/DUT/DP/SCOREBOARD/diif/n_fust_s.rs1 {-height 16 -radix unsigned} /system_tb/DUT/DP/SCOREBOARD/diif/n_fust_s.rs2 {-height 16 -radix unsigned}} /system_tb/DUT/DP/SCOREBOARD/diif/n_fust_s
add wave -noupdate -expand -group dispatch -expand /system_tb/DUT/DP/SCOREBOARD/diif/n_fust_m
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/n_fust_g
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/n_fu_s
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/n_fu_t
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/n_fust_s_en
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/n_fust_m_en
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/n_fust_g_en
add wave -noupdate -expand -group dispatch -radix unsigned /system_tb/DUT/DP/SCOREBOARD/DI/s_rs1
add wave -noupdate -expand -group dispatch -radix unsigned /system_tb/DUT/DP/SCOREBOARD/DI/s_rs2
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/n_t1
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/n_t2
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/n_gt1
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/n_gt2
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/n_gt3
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/alu_op
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/stride
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/halt
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/i_flag
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/m_reg_write
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/s_reg_write
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/jalr
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/jal
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/s_mem_type
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/branch_op
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/imm
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/instr
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/u_type
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/fu_s
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/fu_m
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/m_mem_type
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/matrix_rd
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/matrix_rs1
add wave -noupdate -expand -group dispatch -group cuif /system_tb/DUT/DP/SCOREBOARD/DI/cuif/fu_t
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/jump
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/freeze
add wave -noupdate /system_tb/DUT/DP/SCOREBOARD/DI/s_busy
add wave -noupdate /system_tb/DUT/DP/SCOREBOARD/DI/m_busy
add wave -noupdate /system_tb/DUT/DP/SCOREBOARD/DI/WAW
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/dispatch
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_fu_t
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_fust_s
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_fust_m
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_fust_g
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_fu_s
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_fust_s_en
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_fust_m_en
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_fust_g_en
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_t1
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_t2
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_gt1
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_gt2
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/n_gt3
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/branch_miss
add wave -noupdate -expand -group issue -expand /system_tb/DUT/DP/SCOREBOARD/isif/fu_ex
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/freeze
add wave -noupdate -expand -group issue -expand /system_tb/DUT/DP/SCOREBOARD/isif/wb
add wave -noupdate -expand -group issue -expand /system_tb/DUT/DP/SCOREBOARD/IS/fust_state
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/next_fust_state
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/oldest_rdy
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/age
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/incoming_instr
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/rdy
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/next_oldest_rdy
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/n_age
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/next_ready
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/fu_ready
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/next_single_ready
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/single_ready
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/n_rdy
add wave -noupdate -expand -group issue -childformat {{/system_tb/DUT/DP/SCOREBOARD/isif/out.rd -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/isif/out.rdat1 -radix decimal} {/system_tb/DUT/DP/SCOREBOARD/isif/out.rdat2 -radix hexadecimal} {/system_tb/DUT/DP/SCOREBOARD/isif/out.imm -radix hexadecimal} {/system_tb/DUT/DP/SCOREBOARD/isif/out.branch_pc -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/isif/out.md -radix unsigned}} -expand -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/isif/out.fu_en -expand /system_tb/DUT/DP/SCOREBOARD/isif/out.rd {-height 16 -radix unsigned} /system_tb/DUT/DP/SCOREBOARD/isif/out.rdat1 {-height 16 -radix decimal} /system_tb/DUT/DP/SCOREBOARD/isif/out.rdat2 {-height 16 -radix hexadecimal} /system_tb/DUT/DP/SCOREBOARD/isif/out.imm {-height 16 -radix hexadecimal} /system_tb/DUT/DP/SCOREBOARD/isif/out.branch_pc {-height 16 -radix unsigned} /system_tb/DUT/DP/SCOREBOARD/isif/out.md {-height 16 -radix unsigned}} /system_tb/DUT/DP/SCOREBOARD/isif/out
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/fust_s
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/fust_m
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/fust_g
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/fust_state
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/bfu_enable
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/bfu_j_type
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/bfu_predicted_outcome
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/bfu_branch_type
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/bfu_reg_a
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/bfu_reg_b
add wave -noupdate -group Execute -radix unsigned /system_tb/DUT/DP/EXECUTE/eif/bfu_current_pc
add wave -noupdate -group Execute -radix unsigned /system_tb/DUT/DP/EXECUTE/eif/bfu_imm
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/salu_port_a
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/salu_port_b
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/salu_aluop
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/salu_enable
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/sls_imm
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/sls_rs1
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/sls_rs2
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/sls_dmem_in
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/sls_dhit_in
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/sls_enable
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/sls_mem_type
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/mls_enable
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/mls_ls_in
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/mls_rd_in
add wave -noupdate -group Execute -radix unsigned /system_tb/DUT/DP/EXECUTE/eif/mls_rs_in
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/mls_imm_in
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/gemm_enable
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/gemm_new_weight_in
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/gemm_rs1_in
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/eif_output.bfu_resolved
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/gemm_rs2_in
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/gemm_rs3_in
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/gemm_rd_in
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/gemm_done
add wave -noupdate -group Execute -childformat {{/system_tb/DUT/DP/EXECUTE/eif/eif_output.jump_wdat -radix unsigned}} -expand -subitemconfig {/system_tb/DUT/DP/EXECUTE/eif/eif_output.jump_wdat {-height 16 -radix unsigned} /system_tb/DUT/DP/EXECUTE/eif/eif_output.sp_out {-height 16 -childformat {{ls_matrix_rd_gemm_new_weight -radix binary}} -expand} /system_tb/DUT/DP/EXECUTE/eif/eif_output.sp_out.ls_matrix_rd_gemm_new_weight {-radix binary}} /system_tb/DUT/DP/EXECUTE/eif/eif_output
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/halt
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/spec
add wave -noupdate -group Execute /system_tb/DUT/DP/EXECUTE/eif/rd
add wave -noupdate -group {matrix ls fu} /system_tb/DUT/DP/EXECUTE/mlsif/enable
add wave -noupdate -group {matrix ls fu} /system_tb/DUT/DP/EXECUTE/mlsif/ls_in
add wave -noupdate -group {matrix ls fu} /system_tb/DUT/DP/EXECUTE/mlsif/rd_in
add wave -noupdate -group {matrix ls fu} /system_tb/DUT/DP/EXECUTE/mlsif/rs_in
add wave -noupdate -group {matrix ls fu} /system_tb/DUT/DP/EXECUTE/mlsif/imm_in
add wave -noupdate -group {matrix ls fu} -expand /system_tb/DUT/DP/EXECUTE/mlsif/fu_matls_out
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/enable
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/branch_outcome
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/predicted_outcome
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/miss
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/update_btb
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/resolved
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/br_jump
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/branch_type
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/j_type
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/reg_a
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/reg_b
add wave -noupdate -group {branch fu } -radix unsigned /system_tb/DUT/DP/EXECUTE/fubif/current_pc
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/imm
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/correct_pc
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/update_pc
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/branch_target
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/jump_dest
add wave -noupdate -group {branch fu } /system_tb/DUT/DP/EXECUTE/fubif/jump_wdat
add wave -noupdate -group {Branch FU} /system_tb/DUT/DP/EXECUTE/BFU/CLK
add wave -noupdate -group {Branch FU} /system_tb/DUT/DP/EXECUTE/BFU/nRST
add wave -noupdate -group {Branch FU} /system_tb/DUT/DP/EXECUTE/BFU/zero
add wave -noupdate -group {Branch FU} /system_tb/DUT/DP/EXECUTE/BFU/actual_outcome
add wave -noupdate -group {Branch FU} /system_tb/DUT/DP/EXECUTE/BFU/btb_updated
add wave -noupdate -group {Branch FU} /system_tb/DUT/DP/fif/br_jump
add wave -noupdate -group {Branch FU} /system_tb/DUT/DP/EXECUTE/BFU/last_branch_pc
add wave -noupdate -group {Branch FU} -radix unsigned /system_tb/DUT/DP/FETCH/fif/correct_pc
add wave -noupdate -group {Branch FU} -radix unsigned /system_tb/DUT/DP/EXECUTE/BFU/updated_pc
add wave -noupdate -expand -group wbif -radix unsigned /system_tb/DUT/DP/wbif/alu_wdat
add wave -noupdate -expand -group wbif /system_tb/DUT/DP/wbif/load_wdat
add wave -noupdate -expand -group wbif /system_tb/DUT/DP/wbif/jump_wdat
add wave -noupdate -expand -group wbif /system_tb/DUT/DP/wbif/branch_mispredict
add wave -noupdate -expand -group wbif /system_tb/DUT/DP/wbif/branch_spec
add wave -noupdate -expand -group wbif /system_tb/DUT/DP/wbif/branch_correct
add wave -noupdate -expand -group wbif /system_tb/DUT/DP/wbif/alu_done
add wave -noupdate -expand -group wbif /system_tb/DUT/DP/wbif/load_done
add wave -noupdate -expand -group wbif /system_tb/DUT/DP/wbif/jump_done
add wave -noupdate -expand -group wbif -radix unsigned /system_tb/DUT/DP/wbif/alu_reg_sel
add wave -noupdate -expand -group wbif -radix unsigned /system_tb/DUT/DP/wbif/load_reg_sel
add wave -noupdate -expand -group wbif -radix unsigned /system_tb/DUT/DP/wbif/jump_reg_sel
add wave -noupdate -expand -group wbif -childformat {{/system_tb/DUT/DP/wbif/wb_out.reg_sel -radix unsigned} {/system_tb/DUT/DP/wbif/wb_out.wdat -radix unsigned}} -expand -subitemconfig {/system_tb/DUT/DP/wbif/wb_out.reg_sel {-height 16 -radix unsigned} /system_tb/DUT/DP/wbif/wb_out.wdat {-height 16 -radix unsigned}} /system_tb/DUT/DP/wbif/wb_out
add wave -noupdate /system_tb/DUT/DP/SCOREBOARD/DI/cuif/fu_s
add wave -noupdate -expand -group spif /system_tb/DUT/spif/instrFIFO_WEN
add wave -noupdate -expand -group spif /system_tb/DUT/spif/psumout_en
add wave -noupdate -expand -group spif /system_tb/DUT/spif/drained
add wave -noupdate -expand -group spif /system_tb/DUT/spif/fifo_has_space
add wave -noupdate -expand -group spif /system_tb/DUT/spif/sLoad_hit
add wave -noupdate -expand -group spif /system_tb/DUT/spif/sStore_hit
add wave -noupdate -expand -group spif /system_tb/DUT/spif/instrFIFO_wdata
add wave -noupdate -expand -group spif /system_tb/DUT/spif/psumout_row_sel_in
add wave -noupdate -expand -group spif /system_tb/DUT/spif/sLoad_row
add wave -noupdate -expand -group spif /system_tb/DUT/spif/psumout_data
add wave -noupdate -expand -group spif /system_tb/DUT/spif/load_data
add wave -noupdate -expand -group spif /system_tb/DUT/spif/instrFIFO_full
add wave -noupdate -expand -group spif /system_tb/DUT/spif/partial_enable
add wave -noupdate -expand -group spif /system_tb/DUT/spif/weight_enable
add wave -noupdate -expand -group spif /system_tb/DUT/spif/input_enable
add wave -noupdate -expand -group spif /system_tb/DUT/spif/sLoad
add wave -noupdate -expand -group spif /system_tb/DUT/spif/sStore
add wave -noupdate -expand -group spif /system_tb/DUT/spif/gemm_complete
add wave -noupdate -expand -group spif /system_tb/DUT/spif/load_complete
add wave -noupdate -expand -group spif /system_tb/DUT/spif/store_complete
add wave -noupdate -expand -group spif -radix unsigned /system_tb/DUT/spif/weight_input_data
add wave -noupdate -expand -group spif -radix unsigned /system_tb/DUT/spif/partial_sum_data
add wave -noupdate -expand -group spif -radix unsigned /system_tb/DUT/spif/store_data
add wave -noupdate -expand -group spif /system_tb/DUT/spif/weight_input_row_sel
add wave -noupdate -expand -group spif /system_tb/DUT/spif/partial_sum_row_sel
add wave -noupdate -expand -group spif -radix unsigned /system_tb/DUT/spif/load_addr
add wave -noupdate -expand -group spif /system_tb/DUT/spif/store_addr
add wave -noupdate -group {syst array} /system_tb/DUT/SYS/clk
add wave -noupdate -group {syst array} /system_tb/DUT/SYS/nRST
add wave -noupdate -group {syst array} /system_tb/DUT/SYS/MAC_inputs
add wave -noupdate -group {syst array} /system_tb/DUT/SYS/MAC_outputs
add wave -noupdate -group {syst array} -radix unsigned /system_tb/DUT/SYS/top_input
add wave -noupdate -group {syst array} -radix unsigned /system_tb/DUT/SYS/loadi
add wave -noupdate -group {syst array} -radix unsigned /system_tb/DUT/SYS/loadps
add wave -noupdate -group {syst array} /system_tb/DUT/SYS/start
add wave -noupdate -group {syst array} /system_tb/DUT/SYS/nxt_start
add wave -noupdate -group {syst array} /system_tb/DUT/SYS/nxt_drained
add wave -noupdate -group {syst array} /system_tb/DUT/SYS/z
add wave -noupdate -group {syst array} /system_tb/DUT/SYS/y
add wave -noupdate -group {syst array} /system_tb/DUT/SYS/row_out
add wave -noupdate -group {syst array} /system_tb/DUT/SYS/current_out
add wave -noupdate -group {syst array} /system_tb/DUT/SYS/q
add wave -noupdate -group dmem /system_tb/DUT/dcif/dhit
add wave -noupdate -group dmem /system_tb/DUT/dcif/dmemREN
add wave -noupdate -group dmem /system_tb/DUT/dcif/dmemWEN
add wave -noupdate -group dmem -radix hexadecimal /system_tb/DUT/dcif/dmemload
add wave -noupdate -group dmem -radix hexadecimal /system_tb/DUT/dcif/dmemstore
add wave -noupdate -group dmem -radix unsigned /system_tb/DUT/dcif/dmemaddr
add wave -noupdate -group dcache /system_tb/DUT/acif/dREN
add wave -noupdate -group dcache /system_tb/DUT/acif/dWEN
add wave -noupdate -group dcache /system_tb/DUT/acif/load_done
add wave -noupdate -group dcache /system_tb/DUT/acif/store_done
add wave -noupdate -group dcache /system_tb/DUT/acif/daddr
add wave -noupdate -group dcache /system_tb/DUT/acif/dload
add wave -noupdate -group dcache /system_tb/DUT/acif/dstore
add wave -noupdate -group dcache /system_tb/DUT/MS/DCACHE/dcache_format
add wave -noupdate -group dcache -expand -subitemconfig {{/system_tb/DUT/MS/DCACHE/dcache[1]} -expand {/system_tb/DUT/MS/DCACHE/dcache[0]} -expand} /system_tb/DUT/MS/DCACHE/dcache
add wave -noupdate -group dcache /system_tb/DUT/MS/DCACHE/next_dcache
add wave -noupdate -group dcache /system_tb/DUT/MS/DCACHE/dcache_state
add wave -noupdate -group dcache /system_tb/DUT/MS/DCACHE/next_dcache_state
add wave -noupdate -group arbiter /system_tb/DUT/acif/dREN
add wave -noupdate -group arbiter /system_tb/DUT/acif/dWEN
add wave -noupdate -group arbiter /system_tb/DUT/acif/daddr
add wave -noupdate -group arbiter /system_tb/DUT/acif/dload
add wave -noupdate -group arbiter /system_tb/DUT/acif/dstore
add wave -noupdate /system_tb/DUT/MS/ARB/arbiter_state
add wave -noupdate -group ram /system_tb/DUT/acif/ramWEN
add wave -noupdate -group ram /system_tb/DUT/acif/ramREN
add wave -noupdate -group ram /system_tb/DUT/acif/ramaddr
add wave -noupdate -group ram /system_tb/DUT/acif/ramstore
add wave -noupdate -group ram /system_tb/DUT/MS/ARB/dcache_load
add wave -noupdate -expand -group mmif /system_tb/DUT/MS/mmif/write_en
add wave -noupdate -expand -group mmif /system_tb/DUT/MS/mmif/addr
add wave -noupdate -expand -group mmif /system_tb/DUT/MS/mmif/data_in
add wave -noupdate -expand -group mmif /system_tb/DUT/MS/mmif/data_out
add wave -noupdate -expand -group mmif /system_tb/DUT/MS/mmif/busy
add wave -noupdate -expand -group mmif /system_tb/DUT/MS/mmif/enable
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/CLK
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/nRST
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/dcache_load
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/icache_load
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/local_addr_inc1
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/local_addr_inc2
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/load_count
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/next_load_count
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/sLoad_row_reg
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/next_sLoad_row_reg
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/sp_wait
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/dwait
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/iwait
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/arbiter_state
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/next_arbiter_state
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/load_data_reg
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/sp_load_addr
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/sp_load_data
add wave -noupdate -expand -group {arbiter inside} /system_tb/DUT/MS/ARB/sp_hit
add wave -noupdate /system_tb/DUT/MS/SP/spb0/mats
add wave -noupdate /system_tb/DUT/DP/SCOREBOARD/DI/RSTS/status
add wave -noupdate /system_tb/DUT/MS/DCACHE/dcache
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/alu_din
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/alu_dout
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/alu_write
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/alu_read
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/alu_wptr
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/alu_rptr
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_alu_wptr
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_alu_rptr
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/alu_count
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_alu_count
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/alu_buffer
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_alu_buffer
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/alu_full
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/alu_empty
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/load_din
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/load_dout
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/load_write
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/load_read
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/load_wptr
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/load_rptr
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_load_wptr
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_load_rptr
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/load_count
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_load_count
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/load_buffer
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_load_buffer
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/load_empty
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/load_full
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/jump_din
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/state
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_state
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_wbout
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/wb_sel
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_wb_sel
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/prev_spec
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/spec_alu_wptr
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_spec_alu_wptr
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/spec_write
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_spec_write
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/clean_count
add wave -noupdate -group writeback /system_tb/DUT/DP/WRITEBACK/next_clean_count
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/CLK
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/nRST
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/latched_dmemaddr
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/miss
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/finish_flush
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/lru
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/next_lru
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/flush_idx
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/next_flush_idx
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/flush_counter
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/next_flush_counter
add wave -noupdate -group dcache_top -expand /system_tb/DUT/MS/DCACHE/dcache
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/next_dcache
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/dcache_format
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/dcache_state
add wave -noupdate -group dcache_top /system_tb/DUT/MS/DCACHE/next_dcache_state
add wave -noupdate -group caches /system_tb/DUT/MS/cif/iwait
add wave -noupdate -group caches /system_tb/DUT/MS/cif/dwait
add wave -noupdate -group caches /system_tb/DUT/MS/cif/iREN
add wave -noupdate -group caches /system_tb/DUT/MS/cif/dREN
add wave -noupdate -group caches /system_tb/DUT/MS/cif/dWEN
add wave -noupdate -group caches /system_tb/DUT/MS/cif/iload
add wave -noupdate -group caches /system_tb/DUT/MS/cif/dload
add wave -noupdate -group caches /system_tb/DUT/MS/cif/dstore
add wave -noupdate -group caches /system_tb/DUT/MS/cif/iaddr
add wave -noupdate -group caches -radix decimal /system_tb/DUT/MS/cif/daddr
add wave -noupdate -group {sys array if} /system_tb/DUT/saif/weight_en
add wave -noupdate -group {sys array if} /system_tb/DUT/saif/input_en
add wave -noupdate -group {sys array if} /system_tb/DUT/saif/partial_en
add wave -noupdate -group {sys array if} /system_tb/DUT/saif/out_en
add wave -noupdate -group {sys array if} /system_tb/DUT/saif/drained
add wave -noupdate -group {sys array if} /system_tb/DUT/saif/fifo_has_space
add wave -noupdate -group {sys array if} /system_tb/DUT/saif/row_in_en
add wave -noupdate -group {sys array if} /system_tb/DUT/saif/row_ps_en
add wave -noupdate -group {sys array if} /system_tb/DUT/saif/row_out
add wave -noupdate -group {sys array if} -radix decimal /system_tb/DUT/saif/array_in
add wave -noupdate -group {sys array if} /system_tb/DUT/saif/array_in_partials
add wave -noupdate -group {sys array if} /system_tb/DUT/saif/array_output
add wave -noupdate -expand -group mem /system_tb/DUT/MS/MM/instr
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 7} {6764095 ps} 1} {{Cursor 2} {104053 ps} 1} {{Cursor 3} {5775426 ps} 1} {{Cursor 4} {1892105 ps} 0}
quietly wave cursor active 4
configure wave -namecolwidth 394
configure wave -valuecolwidth 143
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
WaveRestoreZoom {1704413 ps} {2096237 ps}
