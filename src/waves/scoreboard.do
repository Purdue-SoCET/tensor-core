onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider {SB Stimulus}
add wave -noupdate -color Gold /scoreboard_tb/DUT/sbif/fetch
add wave -noupdate -color Gold /scoreboard_tb/CLK
add wave -noupdate -color Gold /scoreboard_tb/nRST
add wave -noupdate -color Gold /scoreboard_tb/DUT/sbif/wb
add wave -noupdate -color Gold /scoreboard_tb/DUT/sbif/out
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
add wave -noupdate -group diif /scoreboard_tb/DUT/diif/fetch
add wave -noupdate -group diif /scoreboard_tb/DUT/diif/wb
add wave -noupdate -group diif /scoreboard_tb/DUT/diif/out
add wave -noupdate -divider RST
add wave -noupdate -group rstif /scoreboard_tb/DUT/DI/WAW
add wave -noupdate -group rstif /scoreboard_tb/DUT/DI/flush
add wave -noupdate -group rstif /scoreboard_tb/DUT/DI/rstsif/di_sel
add wave -noupdate -group rstif /scoreboard_tb/DUT/DI/rstsif/di_write
add wave -noupdate -group rstif /scoreboard_tb/DUT/DI/rstsif/di_tag
add wave -noupdate -group rstif /scoreboard_tb/DUT/DI/rstsif/wb_sel
add wave -noupdate -group rstif /scoreboard_tb/DUT/DI/rstsif/wb_write
add wave -noupdate /scoreboard_tb/DUT/DI/rstsif/status
add wave -noupdate -divider FUST
add wave -noupdate -group fuif /scoreboard_tb/DUT/IS/FS/fuif/en
add wave -noupdate -group fuif /scoreboard_tb/DUT/IS/FS/fuif/fu
add wave -noupdate -group fuif /scoreboard_tb/DUT/IS/FS/fuif/fust_row
add wave -noupdate /scoreboard_tb/DUT/IS/FS/fuif/fust
add wave -noupdate -divider Issue
add wave -noupdate -group isif /scoreboard_tb/DUT/isif/dispatch
add wave -noupdate -group isif -childformat {{/scoreboard_tb/DUT/isif/n_fust_s.rd -radix decimal} {/scoreboard_tb/DUT/isif/n_fust_s.rs1 -radix decimal} {/scoreboard_tb/DUT/isif/n_fust_s.rs2 -radix decimal}} -expand -subitemconfig {/scoreboard_tb/DUT/isif/n_fust_s.rd {-height 16 -radix decimal} /scoreboard_tb/DUT/isif/n_fust_s.rs1 {-height 16 -radix decimal} /scoreboard_tb/DUT/isif/n_fust_s.rs2 {-height 16 -radix decimal}} /scoreboard_tb/DUT/isif/n_fust_s
add wave -noupdate -group isif /scoreboard_tb/DUT/isif/n_fust_m
add wave -noupdate -group isif /scoreboard_tb/DUT/isif/n_fust_g
add wave -noupdate -group isif /scoreboard_tb/DUT/isif/n_fu_s
add wave -noupdate -group isif /scoreboard_tb/DUT/isif/n_fust_s_en
add wave -noupdate -group isif /scoreboard_tb/DUT/isif/n_fust_m_en
add wave -noupdate -group isif /scoreboard_tb/DUT/isif/n_fust_g_en
add wave -noupdate -group isif /scoreboard_tb/DUT/isif/flush
add wave -noupdate -group isif /scoreboard_tb/DUT/isif/freeze
add wave -noupdate -group isif /scoreboard_tb/DUT/isif/wb
add wave -noupdate -group isif /scoreboard_tb/DUT/isif/out
add wave -noupdate -group isif /scoreboard_tb/DUT/isif/fust_s
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
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
WaveRestoreZoom {0 ps} {110250 ps}
