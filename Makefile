# SCRDIR = /home/asicfab/a/saha56/tensor-core/src/waves
SCRDIR = /home/asicfab/a/mill3131/tensor-core/src/scripts
# SCRDIR = /home/asicfab/a/wong371/william_pr/tensor-core/src/scripts

SOURCE_FILES = \
	./src/modules/system.sv \
	./src/modules/ram.sv \
	./src/modules/scheduler_core.sv \
	./src/modules/sc_datapath.sv \
	./src/modules/memory_control.sv \
	./src/modules/caches.sv \
	./src/modules/icache.sv \
	./src/modules/dcache.sv \
	./src/modules/scoreboard.sv \
	./src/modules/fetch.sv \
	./src/modules/fetch_stage.sv \
	./src/modules/execute.sv \
	./src/modules/fetch_branch.sv \
	./src/modules/dispatch.sv \
	./src/modules/issue.sv \
	./src/modules/scoreboard.sv \
	./src/modules/fu_alu.sv \
	./src/modules/fu_scalar_ls.sv \
	./src/modules/fu_matrix_ls.sv \
	./src/modules/fu_gemm.sv \
	./src/modules/fu_branch_predictor.sv \
	./src/modules/fu_branch.sv \
	./src/modules/writeback.sv \
	./src/modules/memory_arbiter_basic.sv \
	./src/modules/fust_g.sv \
	./src/modules/fust_m.sv \
	./src/modules/fust_s.sv \
	./src/modules/rst_m.sv \
	./src/modules/rst_s.sv \
	./src/modules/bpt_tbp.sv \
	./src/modules/bpt.sv \
	./src/modules/btb.sv \
	./src/modules/nbit_stp_shiftreg.sv \
	./src/modules/fetch_tbp.sv \
	./src/modules/memory_subsystem.sv \
	./src/modules/scratchpad.sv \


# SCRDIR = ./tensor-core/src/waves
SIMTIME = 100us             # Default simulation run time

# modelsim viewing options
ifneq (0,$(words $(filter %.wav,$(MAKECMDGOALS))))
#     # view waveform in graphical mode and load do file if there is one
	DOFILES = $(notdir $(basename $(wildcard $(shell find . -name "*.do"))))  # Search for all .do files in the project
	DOFILE = $(filter $(MAKECMDGOALS:%.wav=%) $(MAKECMDGOALS:%_tb.wav=%), $(DOFILES))
	ifeq (1, $(words $(DOFILE)))
	WAVDO = do $(firstword $(shell find . -name $(DOFILE).do))  # Load the .do file from anywhere in the project
	else
	WAVDO = add wave *
	endif
	SIMDO = "view objects; $(WAVDO); run $(SIMTIME);"
else
	# view text output in cmdline mode
	SIMTERM = -c
	SIMDO = "run $(SIMTIME);"
endif

memory_subsystem.wav:
	vlog -sv +incdir+./src/include ./src/include/*.vh ./src/testbench/memory_subsystem_tb.sv ./src/modules/*.sv
	vsim -voptargs="+acc" work.memory_subsystem_tb -sv_lib memory -do "do $(SCRDIR)/memory_subsystem.do; run $(SIMTIME);" -suppress 2275

system.wav:
	vlog -sv +incdir+./src/include ./src/include/*.vh ./src/testbench/system_tb.sv ./src/modules/*.sv
	vsim -voptargs="+acc" work.system_tb -sv_lib memory -do "do ./src/waves/system.do; run -a;" -suppress 2275

system:
	vlog -sv +incdir+./src/include ./src/include/*.vh \
	./src/testbench/system_tb.sv ./src/modules/*.sv
	vsim -c -voptargs="+acc" work.system_tb -sv_lib memory -do $(SIMDO)

test_memory_wav:
	vlog -sv +incdir+./src/include ./src/include/*.vh ./src/testbench/memory_subsystem_tb.sv ./src/modules/*.sv
	vsim -voptargs="+acc" work.memory_subsystem_tb -sv_lib memory -do "do $(SCRDIR)/memory_subsystem.do; run $(SIMTIME);" -suppress 2275

fc:
	vlog -sv ./src/testbench/flex_counter_tb.sv ./src/modules/flex_counter.sv
	vsim $(SIMTERM) -voptargs="+acc" work.flex_counter_tb -do $(SIMDO)

icache:
	vlog -sv +incdir+./src/include ./src/testbench/icache_tb.sv ./src/modules/icache.sv
	vsim $(SIMTERM) -voptargs="+acc" work.icache_tb -do $(SIMDO)

mls:
	vlog -sv +incdir+./src/include ./src/testbench/fu_matrix_ls_tb.sv ./src/modules/fu_matrix_ls.sv
	vsim -voptargs="+acc" work.fu_matrix_ls_tb

wb:
	pwd
	ls ./src/waves/
	vlog -sv +incdir+./src/include ./src/testbench/writeback_tb.sv ./src/modules/writeback.sv
	vsim -voptargs="+acc" work.writeback_tb -do "do $(abspath ./src/waves/writeback.do); run -all"

source:
	vlog -sv $(SOURCE_FILES) +incdir+./src/include/ 

%:
	vlog -sv ./src/modules/*.sv +incdir+./src/include/ 
	vlog -sv ./src/testbench/$*_tb.sv +incdir+./src/include/
	vsim -voptargs="+acc" work.$*_tb -do "view objects; do ./src/waves/$*.do; run -all;" -onfinish stop

%.wav:
	vlog -sv +incdir+./src/include ./src/testbench/$*_tb.sv ./src/modules/$*.sv
	vsim -voptargs="+acc" work.$*_tb -do "do $(abspath $(SCRDIR)/$*.do); run $(SIMTIME);" -suppress 2275

%_vlint:
	verilator --lint-only src/modules/$*.sv -Isrc/include -Isrc/modules

vlog: 
	vlog ./src/modules/fu_branch.sv ./src/modules/fu_branch_predictor.sv ./src/modules/fetch_branch.sv ./src/testbench/fetch_branch_tb.sv
	vlog -sv +incdir+./src/include ./src/testbench/$*_tb.sv ./src/modules/$*.sv
	vsim $(SIMTERM) -voptargs="+acc" work.$*_tb -do $(SIMDO)

%.wav:
	vlog -sv +incdir+./src/include ./src/testbench/$*_tb.sv ./src/modules/*.sv
	vsim -voptargs="+acc" work.$*_tb -sv_lib memory -do "do $(SCRDIR)/$*.do; run $(SIMTIME);" -suppress 2275

%.sim:
	vlog -sv +incdir+./src/include ./src/modules/$*.sv
	

# These three rules are bricked after porting to this new makefile	
# memory_arbiter_basic:
# 	vlog -sv +incdir+./src/include ./src/include/caches_pkg.vh ./src/include/types_pkg.vh \
# 	./src/testbench/memory_arbiter_basic_tb.sv ./src/modules/memory_arbiter_basic.sv
# 	vsim $(SIMTERM) -voptargs="+acc" work.memory_arbiter_basic_tb -do $(SIMDO)

# memory_subsystem:
# 	vlog -sv +incdir+./src/include ./src/include/*.vh \
# 	./src/testbench/memory_subsystem_tb.sv ./src/modules/*.sv
# 	vsim -c -voptargs="+acc" work.memory_subsystem_tb -sv_lib memory -do $(SIMDO)

# memory_subsystem.wav:
# 	vlog -sv +incdir+./src/include ./src/include/*.vh ./src/testbench/memory_subsystem_tb.sv ./src/modules/*.sv
# 	vsim -voptargs="+acc" work.memory_subsystem_tb -sv_lib memory -do "do $(SCRDIR)/memory_subsystem.do; run $(SIMTIME);" -suppress 2275

clean:
	rm -rf work transcript vsim.wlf *.log *.jou *.vstf *.vcd
