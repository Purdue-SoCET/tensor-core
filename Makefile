fc:
	vlog -sv ./src/testbench/flex_counter_tb.sv ./src/modules/flex_counter.sv
	vsim -voptargs="+acc" work.flex_counter_tb

alu:
	vlog -sv +incdir+./src/include ./src/testbench/fu_alu_tb.sv ./src/modules/fu_alu.sv
	vsim -voptargs="+acc" work.fu_alu_tb

branch:
	vlog -sv +incdir+./src/include ./src/testbench/fu_branch_tb.sv ./src/modules/fu_branch.sv
	vsim -voptargs="+acc" work.fu_branch_tb

bp:
	vlog -sv +incdir+./src/include ./src/testbench/fu_branch_predictor_tb.sv ./src/modules/fu_branch_predictor.sv
	vsim -voptargs="+acc" work.fu_branch_predictor_tb

%:
	vlog -sv ./src/testbench/$*_tb.sv ./src/modules/* +incdir+./src/include/
	vsim -voptargs="+acc" work.$*_tb
