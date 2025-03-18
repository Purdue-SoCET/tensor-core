# SCRDIR = /home/asicfab/a/vvaidya/seniordesign/tensor-core/src/scripts
SCRDIR = /home/asicfab/a/wong371/memory_subsystem/tensor-core/src/scripts

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


scratchpad:
	vlog -sv +incdir+./src/include ./src/testbench/scratchpad_tb.sv \
        ./src/modules/scratchpad.sv \
        ./src/modules/scratchpad_bank.sv \
        ./src/modules/load_FSM.sv \
        ./src/modules/gemm_FSM.sv \
        ./src/modules/dramstore_FSM.sv \
        ./src/modules/socetlib_fifo.sv
	vsim -voptargs="+acc" work.scratchpad_tb \
        -do "do /home/asicfab/a/vvaidya/seniordesign/tensor-core/src/scripts/scratchpad.do; run 100us;" \
        -suppress 2275

fc:
	vlog -sv ./src/testbench/flex_counter_tb.sv ./src/modules/flex_counter.sv
	vsim $(SIMTERM) -voptargs="+acc" work.flex_counter_tb -do $(SIMDO)

icache:
	vlog -sv +incdir+./src/include ./src/testbench/icache_tb.sv ./src/modules/icache.sv
	vsim $(SIMTERM) -voptargs="+acc" work.icache_tb -do $(SIMDO)

%:
	vlog -sv +incdir+./src/include ./src/testbench/$*_tb.sv ./src/modules/$*.sv
	vsim $(SIMTERM) -voptargs="+acc" work.$*_tb -do $(SIMDO)

%.wav:
	vlog -sv +incdir+./src/include ./src/testbench/$*_tb.sv ./src/modules/$*.sv
	vsim -voptargs="+acc" work.$*_tb -do "do $(SCRDIR)/$*.do; run $(SIMTIME);" -suppress 2275

memory_arbiter_basic:
	vlog -sv +incdir+./src/include ./src/include/caches_pkg.vh ./src/include/types_pkg.vh \
        ./src/testbench/memory_arbiter_basic_tb.sv ./src/modules/memory_arbiter_basic.sv
	vsim $(SIMTERM) -voptargs="+acc" work.memory_arbiter_basic_tb -do $(SIMDO)

clean:
	rm -rf work transcript vsim.wlf *.log *.jou *.vstf *.vcd
#-do "do $(SCRDIR)/$*.do; run $(SIMTIME);"
