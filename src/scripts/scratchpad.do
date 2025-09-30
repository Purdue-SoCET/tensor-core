onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /scratchpad_tb/PROG/CLK
add wave -noupdate /scratchpad_tb/PROG/nRST
add wave -noupdate /scratchpad_tb/PROG/#ublk#502948#32/test_name
add wave -noupdate -expand -group Inputs -expand -group SchedulerIn /scratchpad_tb/spif/instrFIFO_WEN
add wave -noupdate -expand -group Inputs -expand -group SchedulerIn /scratchpad_tb/spif/instrFIFO_wdata
add wave -noupdate -expand -group Inputs -expand -group {Systolic Array} /scratchpad_tb/spif/psumout_en
add wave -noupdate -expand -group Inputs -expand -group {Systolic Array} /scratchpad_tb/spif/drained
add wave -noupdate -expand -group Inputs -expand -group {Systolic Array} /scratchpad_tb/spif/fifo_has_space
add wave -noupdate -expand -group Inputs -expand -group {Systolic Array} /scratchpad_tb/spif/psumout_row_sel_in
add wave -noupdate -expand -group Inputs -expand -group {Systolic Array} /scratchpad_tb/spif/psumout_data
add wave -noupdate -expand -group Inputs -expand -group {Memory Control} /scratchpad_tb/spif/sLoad_hit
add wave -noupdate -expand -group Inputs -expand -group {Memory Control} /scratchpad_tb/spif/sStore_hit
add wave -noupdate -expand -group Inputs -expand -group {Memory Control} /scratchpad_tb/spif/sLoad_row
add wave -noupdate -expand -group Inputs -expand -group {Memory Control} /scratchpad_tb/spif/load_data
add wave -noupdate -expand -group Outputs -expand -group Scheduler /scratchpad_tb/spif/instrFIFO_full
add wave -noupdate -expand -group Outputs -expand -group Scheduler /scratchpad_tb/spif/gemm_complete
add wave -noupdate -expand -group Outputs -expand -group Scheduler /scratchpad_tb/spif/load_complete
add wave -noupdate -expand -group Outputs -expand -group {Systolic Array} /scratchpad_tb/spif/partial_enable
add wave -noupdate -expand -group Outputs -expand -group {Systolic Array} /scratchpad_tb/spif/weight_enable
add wave -noupdate -expand -group Outputs -expand -group {Systolic Array} /scratchpad_tb/spif/input_enable
add wave -noupdate -expand -group Outputs -expand -group {Systolic Array} /scratchpad_tb/spif/weight_input_data
add wave -noupdate -expand -group Outputs -expand -group {Systolic Array} /scratchpad_tb/spif/partial_sum_data
add wave -noupdate -expand -group Outputs -expand -group {Systolic Array} /scratchpad_tb/spif/weight_input_row_sel
add wave -noupdate -expand -group Outputs -expand -group {Systolic Array} /scratchpad_tb/spif/partial_sum_row_sel
add wave -noupdate -expand -group Outputs -expand -group {Memory Control} /scratchpad_tb/spif/sLoad
add wave -noupdate -expand -group Outputs -expand -group {Memory Control} /scratchpad_tb/spif/sStore
add wave -noupdate -expand -group Outputs -expand -group {Memory Control} /scratchpad_tb/spif/store_data
add wave -noupdate -expand -group Outputs -expand -group {Memory Control} /scratchpad_tb/spif/load_addr
add wave -noupdate -expand -group Outputs -expand -group {Memory Control} /scratchpad_tb/spif/store_addr
add wave -noupdate -expand /scratchpad_tb/DUT/spb0/mats
add wave -noupdate /scratchpad_tb/DUT/spb1/mats
add wave -noupdate /scratchpad_tb/DUT/spb2/mats
add wave -noupdate /scratchpad_tb/DUT/spb3/mats
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/sLoad_hit
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/wFIFO_full
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/instrFIFO_empty
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/rFIFO_full
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/psumoutFIFO_empty
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/new_instr
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/sLoad_row
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/load_data
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/instrFIFO_rdata
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/psumoutFIFO_rdata
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/gemm_mat
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/instrFIFO_REN
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/psumoutFIFO_REN
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/sLoad
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/wFIFO_WEN
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/rFIFO_WEN
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/load_addr
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/wFIFO_wdata
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsmif0/rFIFO_wdata
add wave -noupdate -group BFSM0 /scratchpad_tb/DUT/bfsm0/state
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/sLoad_hit
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/wFIFO_full
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/instrFIFO_empty
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/rFIFO_full
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/psumoutFIFO_empty
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/new_instr
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/sLoad_row
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/load_data
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/instrFIFO_rdata
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/psumoutFIFO_rdata
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/gemm_mat
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/instrFIFO_REN
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/psumoutFIFO_REN
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/sLoad
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/wFIFO_WEN
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/rFIFO_WEN
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/load_addr
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/wFIFO_wdata
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsmif1/rFIFO_wdata
add wave -noupdate -expand -group BFSM1 /scratchpad_tb/DUT/bfsm1/state
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/sLoad_hit
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/wFIFO_full
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/instrFIFO_empty
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/rFIFO_full
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/psumoutFIFO_empty
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/new_instr
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/sLoad_row
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/load_data
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/instrFIFO_rdata
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/psumoutFIFO_rdata
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/gemm_mat
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/instrFIFO_REN
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/psumoutFIFO_REN
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/sLoad
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/wFIFO_WEN
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/rFIFO_WEN
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/load_addr
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/wFIFO_wdata
add wave -noupdate -group BFSM2 /scratchpad_tb/DUT/bfsmif2/rFIFO_wdata
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/sLoad_hit
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/wFIFO_full
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/instrFIFO_empty
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/rFIFO_full
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/psumoutFIFO_empty
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/new_instr
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/sLoad_row
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/load_data
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/instrFIFO_rdata
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/psumoutFIFO_rdata
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/gemm_mat
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/instrFIFO_REN
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/psumoutFIFO_REN
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/sLoad
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/wFIFO_WEN
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/rFIFO_WEN
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/load_addr
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/wFIFO_wdata
add wave -noupdate -group BFSM3 /scratchpad_tb/DUT/bfsmif3/rFIFO_wdata
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {59 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 332
configure wave -valuecolwidth 295
configure wave -justifyvalue left
configure wave -signalnamewidth 0
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
WaveRestoreZoom {0 ns} {702 ns}
