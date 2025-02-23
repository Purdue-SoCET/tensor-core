fc:
	vlog -sv ./src/testbench/flex_counter_tb.sv ./src/modules/flex_counter.sv
	vsim -voptargs="+acc" work.flex_counter_tb

mls:
	vlog -sv +incdir+./src/include ./src/testbench/fu_matrix_ls_tb.sv ./src/modules/fu_matrix_ls.sv
	vsim -voptargs="+acc" work.fu_matrix_ls_tb

wb:
	vlog -sv +incdir+./src/include ./src/testbench/writeback_tb.sv ./src/modules/writeback.sv
	vsim -voptargs="+acc" work.writeback_tb -do "do ./src/waves/writeback.do; run -all"


%:
	vlog -sv ./src/testbench/$*_tb.sv ./src/modules/$*.sv +incdir+./src/include/ 
	vsim -voptargs="+acc" work.$*_tb -do "view objects; do ./src/waves/$*.do; run -all;" -onfinish stop

# ./src/waves/$*.do 
%_vlint:
	verilator --lint-only src/modules/$*.sv -Isrc/include -Isrc/modules

vlog: 
	vlog ./src/modules/fu_branch.sv ./src/modules/fu_branch_predictor.sv ./src/modules/fetch_branch.sv ./src/testbench/fetch_branch_tb.sv