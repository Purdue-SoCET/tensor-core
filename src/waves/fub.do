onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /system_tb/CLK
add wave -noupdate /system_tb/nRST
add wave -noupdate /system_tb/dcif/halt
add wave -noupdate /system_tb/dcif/flushed
add wave -noupdate -divider {Instruction Operations}
add wave -noupdate -group icache /system_tb/DUT/MS/ICACHE/icache_format
add wave -noupdate -group icache /system_tb/DUT/MS/ICACHE/icache
add wave -noupdate -group icache /system_tb/DUT/MS/ICACHE/nxt_icache
add wave -noupdate -group icache /system_tb/DUT/MS/ICACHE/icache_state
add wave -noupdate -group icache /system_tb/DUT/MS/ICACHE/nxt_icache_state
add wave -noupdate -group {datapath enables} /system_tb/DUT/DP/eif/bfu_enable
add wave -noupdate -group {datapath enables} /system_tb/DUT/DP/eif/salu_enable
add wave -noupdate -group {datapath enables} /system_tb/DUT/DP/eif/sls_enable
add wave -noupdate -group {datapath enables} /system_tb/DUT/DP/eif/mls_enable
add wave -noupdate -group {datapath enables} /system_tb/DUT/DP/eif/gemm_enable
add wave -noupdate -group {datapath instr signals} /system_tb/dcif/gemm_complete
add wave -noupdate -group {datapath instr signals} /system_tb/dcif/load_complete
add wave -noupdate -group {datapath instr signals} /system_tb/dcif/store_complete
add wave -noupdate -group {datapath instr signals} -radix unsigned /system_tb/DUT/dcif/imemaddr
add wave -noupdate -group {datapath instr signals} -radix hexadecimal /system_tb/DUT/dcif/imemload
add wave -noupdate -group {datapath instr signals} /system_tb/DUT/dcif/imemREN
add wave -noupdate -group {cif icache} /system_tb/cif/iwait
add wave -noupdate -group {cif icache} /system_tb/cif/iREN
add wave -noupdate -group {cif icache} /system_tb/cif/iload
add wave -noupdate -group {cif icache} -radix unsigned /system_tb/cif/iaddr
add wave -noupdate -group {fetch if} /system_tb/DUT/DP/fif/imemREN
add wave -noupdate -group {fetch if} /system_tb/DUT/DP/fif/imemload
add wave -noupdate -group {fetch if} -radix unsigned /system_tb/DUT/DP/fif/imemaddr
add wave -noupdate -group {fetch if} /system_tb/DUT/DP/fif/update_btb
add wave -noupdate -group {fetch if} /system_tb/DUT/DP/fif/branch_outcome
add wave -noupdate -group {fetch if} /system_tb/DUT/DP/fif/predicted_outcome
add wave -noupdate -group {fetch if} -expand -group fetch /system_tb/DUT/DP/FETCH/fif/freeze
add wave -noupdate -group {fetch if} -expand -group fetch /system_tb/DUT/DP/FETCH/fif/misprediction
add wave -noupdate -group {fetch if} -expand -group fetch /system_tb/DUT/DP/FETCH/fif/imemREN
add wave -noupdate -group {fetch if} -expand -group fetch /system_tb/DUT/DP/FETCH/fif/br_jump
add wave -noupdate -group {fetch if} -expand -group fetch /system_tb/DUT/DP/FETCH/fetch_unit/ihit
add wave -noupdate -group {fetch if} -expand -group fetch -radix hexadecimal /system_tb/DUT/DP/FETCH/fif/imemload
add wave -noupdate -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fif/pc_prediction
add wave -noupdate -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fetch_unit/next_pc
add wave -noupdate -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fetch_unit/pc_reg
add wave -noupdate -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fif/pc
add wave -noupdate -group {fetch if} -expand -group fetch -radix hexadecimal /system_tb/DUT/DP/FETCH/fif/instr
add wave -noupdate -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fif/correct_pc
add wave -noupdate -group {fetch if} -expand -group fetch -radix unsigned /system_tb/DUT/DP/FETCH/fif/imemaddr
add wave -noupdate -group {fetch if} -radix unsigned /system_tb/DUT/DP/fif/update_pc
add wave -noupdate -group {fetch if} /system_tb/DUT/DP/fif/branch_target
add wave -noupdate -group {fetch if} /system_tb/DUT/DP/FETCH/missed
add wave -noupdate -group {fetch if} -radix unsigned /system_tb/DUT/DP/FETCH/save_pc
add wave -noupdate -group {fetch if} /system_tb/DUT/DP/fif/freeze
add wave -noupdate -group {fetch if} /system_tb/DUT/DP/fif/jump
add wave -noupdate -group {fetch if} /system_tb/DUT/DP/fif/br_jump
add wave -noupdate -group {fetch if} /system_tb/DUT/DP/fif/misprediction
add wave -noupdate -group {fetch if} -radix unsigned /system_tb/DUT/DP/fif/correct_pc
add wave -noupdate -group {fetch if} -radix unsigned /system_tb/DUT/DP/fif/pc
add wave -noupdate -group {fetch if} /system_tb/DUT/DP/fif/instr
add wave -noupdate -group {fif interface fetch} /system_tb/DUT/DP/FETCH/fif/instr
add wave -noupdate -group {fif interface fetch} /system_tb/DUT/DP/FETCH/fif/imemREN
add wave -noupdate -group {fif interface fetch} -radix unsigned /system_tb/DUT/DP/FETCH/fif/imemaddr
add wave -noupdate -group {fif interface fetch} /system_tb/DUT/DP/FETCH/fif/imemload
add wave -noupdate -group {fif interface fetch} -radix unsigned /system_tb/DUT/DP/FETCH/fif/pc
add wave -noupdate -group {fif interface fetch} -radix unsigned /system_tb/DUT/DP/FETCH/fetch_unit/next_pc
add wave -noupdate -group {fif interface fetch} /system_tb/DUT/DP/FETCH/fif/correct_pc
add wave -noupdate -group icache-datapath /system_tb/dcif/ihit
add wave -noupdate -group icache-datapath /system_tb/dcif/imemREN
add wave -noupdate -group icache-datapath /system_tb/dcif/imemload
add wave -noupdate -group icache-datapath -radix unsigned /system_tb/dcif/imemaddr
add wave -noupdate -group icache-arbiter /system_tb/acif/iREN
add wave -noupdate -group icache-arbiter /system_tb/DUT/MS/ARB/acif/ramREN
add wave -noupdate -group icache-arbiter -radix unsigned /system_tb/DUT/MS/ARB/acif/ramaddr
add wave -noupdate -group icache-arbiter /system_tb/acif/iload
add wave -noupdate -group icache-arbiter /system_tb/DUT/MS/ARB/icache_load
add wave -noupdate -group icache-arbiter /system_tb/acif/iaddr
add wave -noupdate -divider {Scalar Operations}
add wave -noupdate -childformat {{{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[31]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[30]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[24]} -radix hexadecimal} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[18]} -radix hexadecimal} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[16]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[13]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[12]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[9]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[7]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[6]} -radix hexadecimal} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[5]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[4]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[3]} -radix unsigned} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[2]} -radix hexadecimal} {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[1]} -radix unsigned}} -subitemconfig {{/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[31]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[30]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[24]} {-height 16 -radix hexadecimal} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[18]} {-height 16 -radix hexadecimal} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[16]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[13]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[12]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[9]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[7]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[6]} {-height 16 -radix hexadecimal} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[5]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[4]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[3]} {-height 16 -radix unsigned} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[2]} {-height 16 -radix hexadecimal} {/system_tb/DUT/DP/SCOREBOARD/IS/RF/register[1]} {-height 16 -radix unsigned}} /system_tb/DUT/DP/SCOREBOARD/IS/RF/register
add wave -noupdate -expand -group dispatch -childformat {{/system_tb/DUT/DP/SCOREBOARD/diif/fetch.br_pc -radix hexadecimal}} -expand -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/diif/fetch.br_pc {-height 16 -radix hexadecimal}} /system_tb/DUT/DP/SCOREBOARD/diif/fetch
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/DI/CU/cu_if/instr
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/DI/CU/cu_if/halt
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/DI/dispatch.halt
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/DI/n_dispatch.halt
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/branch_miss
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/diif/out.halt
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/DI/spec
add wave -noupdate -expand -group dispatch /system_tb/DUT/DP/SCOREBOARD/DI/n_spec
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/branch_miss
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/isif/dispatch.halt
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/n_halt
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/halt
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/isif/n_fu_t
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/isif/n_fu_s
add wave -noupdate -expand -group issue -childformat {{/system_tb/DUT/DP/SCOREBOARD/IS/isif/n_fust_s.rs1 -radix binary} {/system_tb/DUT/DP/SCOREBOARD/IS/isif/n_fust_s.rs2 -radix binary}} -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/IS/isif/n_fust_s.rs1 {-height 16 -radix binary} /system_tb/DUT/DP/SCOREBOARD/IS/isif/n_fust_s.rs2 {-height 16 -radix binary}} /system_tb/DUT/DP/SCOREBOARD/IS/isif/n_fust_s
add wave -noupdate -expand -group issue -subitemconfig {/system_tb/DUT/DP/SCOREBOARD/IS/fusif/fust.op -expand {/system_tb/DUT/DP/SCOREBOARD/IS/fusif/fust.op[2]} -expand} /system_tb/DUT/DP/SCOREBOARD/IS/fusif/fust
add wave -noupdate -expand -group issue {/system_tb/DUT/DP/SCOREBOARD/IS/fust_state[2]}
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/n_rdy
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/next_oldest_rdy
add wave -noupdate -expand -group issue {/system_tb/DUT/DP/SCOREBOARD/IS/next_ready[2]}
add wave -noupdate -expand -group issue /system_tb/DUT/DP/SCOREBOARD/IS/next_single_ready
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/enable
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/branch
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/branch_type
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/j_type
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/reg_a
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/reg_b
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/current_pc
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/imm
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/predicted_outcome
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/branch_outcome
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/resolved
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/miss
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/update_btb
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/btb_updated
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/br_jump
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/updated_pc
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/update_pc
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/branch_target
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/correct_pc
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/jump_dest
add wave -noupdate -expand -group fubif /system_tb/DUT/DP/EXECUTE/BFU/fubif/jump_wdat
add wave -noupdate /system_tb/DUT/DP/fif/predicted_outcome
add wave -noupdate /system_tb/DUT/DP/fif/pc
add wave -noupdate /system_tb/DUT/DP/fif/instr
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 7} {6764095 ps} 1} {{Cursor 2} {104053 ps} 1} {{Cursor 3} {6895651 ps} 0}
quietly wave cursor active 3
configure wave -namecolwidth 243
configure wave -valuecolwidth 161
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
WaveRestoreZoom {6805404 ps} {6966401 ps}
