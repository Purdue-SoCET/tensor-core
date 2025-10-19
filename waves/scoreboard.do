onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider {SB Stimulus}
add wave -noupdate -color Gold -expand -subitemconfig {/scoreboard_tb/DUT/sbif/fetch.imemload {-color Gold -height 16} /scoreboard_tb/DUT/sbif/fetch.br_pc {-color Gold -height 16} /scoreboard_tb/DUT/sbif/fetch.br_pred {-color Gold -height 16}} /scoreboard_tb/DUT/sbif/fetch
add wave -noupdate -color Gold /scoreboard_tb/CLK
add wave -noupdate -color Gold /scoreboard_tb/nRST
add wave -noupdate -color Gold -subitemconfig {/scoreboard_tb/DUT/sbif/wb.s_rw_en {-color Gold} /scoreboard_tb/DUT/sbif/wb.s_rw {-color Gold} /scoreboard_tb/DUT/sbif/wb.s_wdata {-color Gold} /scoreboard_tb/DUT/sbif/wb.load_done {-color Gold} /scoreboard_tb/DUT/sbif/wb.alu_done {-color Gold}} /scoreboard_tb/DUT/sbif/wb
add wave -noupdate /scoreboard_tb/DUT/sbif/fu_ex
add wave -noupdate -color Gold -expand -subitemconfig {/scoreboard_tb/DUT/sbif/out.fu_en {-color Gold -height 16 -expand} {/scoreboard_tb/DUT/sbif/out.fu_en[4]} {-color Gold} {/scoreboard_tb/DUT/sbif/out.fu_en[3]} {-color Gold} {/scoreboard_tb/DUT/sbif/out.fu_en[2]} {-color Gold} {/scoreboard_tb/DUT/sbif/out.fu_en[1]} {-color Gold} {/scoreboard_tb/DUT/sbif/out.fu_en[0]} {-color Gold} /scoreboard_tb/DUT/sbif/out.rdat1 {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.rdat2 {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.imm {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.branch_type {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.branch_pc {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.branch_pred_pc {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.alu_op {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.ls_in {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.mem_type {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.md {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.ms1 {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.ms2 {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.ms3 {-color Gold -height 16} /scoreboard_tb/DUT/sbif/out.halt {-color Gold}} /scoreboard_tb/DUT/sbif/out
add wave -noupdate -divider {Control Unit}
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/alu_op
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/stride
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/halt
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/i_flag
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/m_reg_write
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/s_reg_write
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/jalr
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/jal
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/s_mem_type
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/branch_op
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/imm
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/instr
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/u_type
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/fu_s
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/fu_m
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/m_mem_type
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/matrix_rd
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/matrix_rs1
add wave -noupdate -group cuif /scoreboard_tb/DUT/DI/cuif/fu_t
add wave -noupdate -divider Dispatch
add wave -noupdate /scoreboard_tb/DUT/DI/WAW
add wave -noupdate /scoreboard_tb/DUT/DI/hazard
add wave -noupdate /scoreboard_tb/DUT/DI/s_busy
add wave -noupdate /scoreboard_tb/DUT/DI/m_busy
add wave -noupdate -expand -group diif /scoreboard_tb/DUT/diif/fetch
add wave -noupdate -expand -group diif /scoreboard_tb/DUT/diif/wb
add wave -noupdate -expand -group diif /scoreboard_tb/DUT/diif/out
add wave -noupdate -expand /scoreboard_tb/DUT/DI/diif/n_fust_s
add wave -noupdate -expand /scoreboard_tb/DUT/DI/diif/n_fust_m
add wave -noupdate -expand -subitemconfig {/scoreboard_tb/DUT/diif/fust_s.busy -expand /scoreboard_tb/DUT/diif/fust_s.op -expand} /scoreboard_tb/DUT/diif/fust_s
add wave -noupdate /scoreboard_tb/DUT/DI/diif/n_fust_g
add wave -noupdate /scoreboard_tb/DUT/DI/diif/n_fu_s
add wave -noupdate /scoreboard_tb/DUT/DI/diif/n_fust_s_en
add wave -noupdate /scoreboard_tb/DUT/DI/diif/n_fust_m_en
add wave -noupdate /scoreboard_tb/DUT/DI/diif/n_fust_g_en
add wave -noupdate -divider RST
add wave -noupdate -expand -group rstsif /scoreboard_tb/DUT/DI/rstsif/di_sel
add wave -noupdate -expand -group rstsif /scoreboard_tb/DUT/DI/rstsif/di_write
add wave -noupdate -expand -group rstsif /scoreboard_tb/DUT/DI/rstsif/di_tag
add wave -noupdate -expand -group rstsif /scoreboard_tb/DUT/DI/rstsif/spec
add wave -noupdate -expand -group rstsif /scoreboard_tb/DUT/DI/rstsif/wb_sel
add wave -noupdate -expand -group rstsif /scoreboard_tb/DUT/DI/rstsif/wb_write
add wave -noupdate -expand -group rstsif /scoreboard_tb/DUT/DI/rstsif/status
add wave -noupdate /scoreboard_tb/DUT/DI/rstsif/status
add wave -noupdate -divider FUST
add wave -noupdate -group fuif /scoreboard_tb/DUT/IS/FS/fuif/en
add wave -noupdate -group fuif /scoreboard_tb/DUT/IS/FS/fuif/fu
add wave -noupdate -group fuif /scoreboard_tb/DUT/IS/FS/fuif/fust_row
add wave -noupdate /scoreboard_tb/PROG/sbif/branch_miss
add wave -noupdate /scoreboard_tb/PROG/sbif/branch_resolved
add wave -noupdate -radix unsigned -childformat {{/scoreboard_tb/DUT/IS/FS/fuif/fust.busy -radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.t1 -radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.t2 -radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op -radix unsigned -childformat {{{[2]} -radix unsigned -childformat {{rd -radix unsigned} {rs1 -radix unsigned} {rs2 -radix unsigned} {imm -radix unsigned} {spec -radix unsigned} {op_type -radix unsigned} {mem_type -radix unsigned}}} {{[1]} -radix unsigned -childformat {{rd -radix unsigned} {rs1 -radix unsigned} {rs2 -radix unsigned} {imm -radix unsigned} {spec -radix unsigned} {op_type -radix unsigned} {mem_type -radix unsigned}}} {{[0]} -radix unsigned -childformat {{rd -radix unsigned} {rs1 -radix unsigned} {rs2 -radix unsigned} {imm -radix unsigned} {spec -radix unsigned} {op_type -radix unsigned} {mem_type -radix unsigned}}}}}} -expand -subitemconfig {/scoreboard_tb/DUT/IS/FS/fuif/fust.busy {-height 16 -radix unsigned} /scoreboard_tb/DUT/IS/FS/fuif/fust.t1 {-height 16 -radix unsigned} /scoreboard_tb/DUT/IS/FS/fuif/fust.t2 {-height 16 -radix unsigned} /scoreboard_tb/DUT/IS/FS/fuif/fust.op {-height 16 -radix unsigned -childformat {{{[2]} -radix unsigned -childformat {{rd -radix unsigned} {rs1 -radix unsigned} {rs2 -radix unsigned} {imm -radix unsigned} {spec -radix unsigned} {op_type -radix unsigned} {mem_type -radix unsigned}}} {{[1]} -radix unsigned -childformat {{rd -radix unsigned} {rs1 -radix unsigned} {rs2 -radix unsigned} {imm -radix unsigned} {spec -radix unsigned} {op_type -radix unsigned} {mem_type -radix unsigned}}} {{[0]} -radix unsigned -childformat {{rd -radix unsigned} {rs1 -radix unsigned} {rs2 -radix unsigned} {imm -radix unsigned} {spec -radix unsigned} {op_type -radix unsigned} {mem_type -radix unsigned}}}} -expand} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[2]} {-radix unsigned -childformat {{rd -radix unsigned} {rs1 -radix unsigned} {rs2 -radix unsigned} {imm -radix unsigned} {spec -radix unsigned} {op_type -radix unsigned} {mem_type -radix unsigned}}} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[2].rd} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[2].rs1} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[2].rs2} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[2].imm} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[2].spec} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[2].op_type} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[2].mem_type} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[1]} {-radix unsigned -childformat {{rd -radix unsigned} {rs1 -radix unsigned} {rs2 -radix unsigned} {imm -radix unsigned} {spec -radix unsigned} {op_type -radix unsigned} {mem_type -radix unsigned}}} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[1].rd} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[1].rs1} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[1].rs2} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[1].imm} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[1].spec} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[1].op_type} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[1].mem_type} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[0]} {-radix unsigned -childformat {{rd -radix unsigned} {rs1 -radix unsigned} {rs2 -radix unsigned} {imm -radix unsigned} {spec -radix unsigned} {op_type -radix unsigned} {mem_type -radix unsigned}}} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[0].rd} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[0].rs1} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[0].rs2} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[0].imm} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[0].spec} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[0].op_type} {-radix unsigned} {/scoreboard_tb/DUT/IS/FS/fuif/fust.op[0].mem_type} {-radix unsigned}} /scoreboard_tb/DUT/IS/FS/fuif/fust
add wave -noupdate -divider Issue
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/isif/dispatch
add wave -noupdate -expand -group isif -expand /scoreboard_tb/DUT/IS/age
add wave -noupdate -expand -group isif -expand /scoreboard_tb/DUT/IS/n_age
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/IS/rdy
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/IS/n_rdy
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/IS/oldest_rdy
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/IS/next_oldest_rdy
add wave -noupdate -expand -group isif -childformat {{/scoreboard_tb/DUT/isif/n_fust_s.rd -radix decimal} {/scoreboard_tb/DUT/isif/n_fust_s.rs1 -radix decimal} {/scoreboard_tb/DUT/isif/n_fust_s.rs2 -radix decimal}} -subitemconfig {/scoreboard_tb/DUT/isif/n_fust_s.rd {-height 16 -radix decimal} /scoreboard_tb/DUT/isif/n_fust_s.rs1 {-height 16 -radix decimal} /scoreboard_tb/DUT/isif/n_fust_s.rs2 {-height 16 -radix decimal}} /scoreboard_tb/DUT/isif/n_fust_s
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/isif/n_fust_m
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/isif/n_fust_g
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/isif/n_fu_s
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/isif/n_fust_s_en
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/isif/n_fust_m_en
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/isif/n_fust_g_en
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/isif/wb
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/isif/out
add wave -noupdate -expand -group isif /scoreboard_tb/DUT/isif/fust_s
add wave -noupdate -expand /scoreboard_tb/DUT/IS/fust_state
add wave -noupdate /scoreboard_tb/DUT/IS/incoming_instr
add wave -noupdate /scoreboard_tb/DUT/sbif/wb
add wave -noupdate /scoreboard_tb/DUT/sbif/wb_ctrl
add wave -noupdate /scoreboard_tb/CLK
add wave -noupdate -expand -group regfile /scoreboard_tb/DUT/IS/rfif/WEN
add wave -noupdate -expand -group regfile /scoreboard_tb/DUT/IS/rfif/wsel
add wave -noupdate -expand -group regfile -radix unsigned /scoreboard_tb/DUT/IS/rfif/rsel1
add wave -noupdate -expand -group regfile -radix unsigned /scoreboard_tb/DUT/IS/rfif/rsel2
add wave -noupdate -expand -group regfile -radix unsigned /scoreboard_tb/DUT/IS/rfif/wdata
add wave -noupdate -expand -group regfile /scoreboard_tb/DUT/IS/rfif/rdat1
add wave -noupdate -expand -group regfile /scoreboard_tb/DUT/IS/rfif/rdat2
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 3} {79910 ps} 1} {{Cursor 4} {114000 ps} 0}
quietly wave cursor active 2
configure wave -namecolwidth 150
configure wave -valuecolwidth 209
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
WaveRestoreZoom {21320 ps} {234680 ps}
