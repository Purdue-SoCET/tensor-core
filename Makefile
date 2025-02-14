fc:
	vlog -sv ./src/testbench/fu_gemm_tb.sv ./src/modules/fu_gemm.sv
	vsim -voptargs="+acc" work.fu_gemm_tb

alu:
	vlog -sv +incdir+./src/include ./src/testbench/fu_alu_tb.sv ./src/modules/fu_alu.sv
	vsim -voptargs="+acc" work.fu_alu_tb

mls:
	vlog -sv +incdir+./src/include ./src/testbench/fu_matrix_ls_tb.sv ./src/modules/fu_matrix_ls.sv
	vsim -voptargs="+acc" work.fu_matrix_ls_tb

%:
	vlog -sv ./src/testbench/$*_tb.sv ./src/modules/$*.sv +incdir+./src/include/
	vsim -voptargs="+acc" work.$*_tb
	# verilator --sc ./src/testbench/$*_tb.sv ./src/modules/$*.sv -Isrc/include/

# dispatch:
# 	vlog -sv ./src/testbench/dispatch_tb.sv ./src/modules/dispatch.sv ./src/modules/rst_m.sv ./src/modules/rst_s.sv +incdir+./src/include/
# 	vsim -voptargs="+acc" work.$*_tb