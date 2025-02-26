SOURCE_FILES = \
	./src/modules/system.sv \
	./src/modules/ram.sv \
	./src/modules/scheduler_core.sv \
	./src/modules/memory_control.sv \
	./src/modules/caches.sv \
	./src/modules/icache.sv \
	./src/modules/dcache.sv \
	./src/modules/scoreboard.sv \
	./src/modules/fetch.sv \
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
	./src/modules/rst_s.sv


SCRDIR = /home/asicfab/a/wong371/william_wk/tensor-core/src/scripts
SIMTIME = 100us             # Default simulation run time

# modelsim viewing options
ifneq (0,$(words $(filter %.wav,$(MAKECMDGOALS))))
    # view waveform in graphical mode and load do file if there is one
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
	vlog -sv +incdir+./src/include ./src/testbench/writeback_tb.sv ./src/modules/writeback.sv
	vsim -voptargs="+acc" work.writeback_tb -do "do ./src/waves/writeback.do; run -all"


source:
	vlog -sv $(SOURCE_FILES) +incdir+./src/include/ 

%:
	vlog -sv $(SOURCE_FILES) +incdir+./src/include/ 
	vlog -sv ./src/testbench/$*_tb.sv +incdir+./src/include/
	vsim -voptargs="+acc" work.$*_tb -do "view objects; do ./src/waves/$*.do; run -all;" -onfinish stop

%_vlint:
	verilator --lint-only src/modules/$*.sv -Isrc/include -Isrc/modules

vlog: 
	vlog ./src/modules/fu_branch.sv ./src/modules/fu_branch_predictor.sv ./src/modules/fetch_branch.sv ./src/testbench/fetch_branch_tb.sv
	vlog -sv +incdir+./src/include ./src/testbench/$*_tb.sv ./src/modules/$*.sv
	vsim $(SIMTERM) -voptargs="+acc" work.$*_tb -do $(SIMDO)

%.wav:
	vlog -sv +incdir+./src/include ./src/testbench/$*_tb.sv ./src/modules/$*.sv
	vsim -voptargs="+acc" work.$*_tb -do "do $(SCRDIR)/$*.do; run $(SIMTIME);" -suppress 2275

%.sim:
	vlog -sv +incdir+./src/include ./src/modules/$*.sv


clean:
	rm -rf work transcript vsim.wlf *.log *.jou *.vstf *.vcd
