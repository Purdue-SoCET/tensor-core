SCRDIR = /home/asicfab/a/vvaidya/seniordesign/tensor-core/src/scripts
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
	vlog -sv +incdir+./src/include ./src/testbench/scratchpad_tb.sv ./src/modules/scratchpad.sv ./src/modules/scratchpad_bank.sv \
     ./src/modules/load_FSM.sv \
     ./src/modules/gemm_FSM.sv \
     ./src/modules/dramstore_FSM.sv \
     ./src/modules/socetlib_fifo.sv \
	vsim work.scratchpad_tb 

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

clean:
	rm -rf work transcript vsim.wlf *.log *.jou *.vstf *.vcd
#-do "do $(SCRDIR)/$*.do; run $(SIMTIME);"
