vlib work
vlog -work work +acc -l vcs.log -sv +define+DDR4_4G_X8 arch_defines.v dimm.vh dram_command.sv arch_package.sv proj_package.sv interface.sv ddr4_model.svp dram_cmd_dimm_tb.sv scheduler_buffer.sv data_transfer.sv socetlib_counter.sv edge_det.sv edge_det_if.vh
vsim -do ./scripts/dram_sim_dimm.do dram_cmd_dimm_tb
run -all