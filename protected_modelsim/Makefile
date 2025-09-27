SCRDIR = /home/asicfab/a/than0/tensor-core/src/scripts
SIMTIME = 100us             # Default simulation run time

SCRDIR = ./src

EXTRA_dram_top = $(wildcard $(SCRDIR)/*.sv)

DRAM_define = ./arch_defines.v ./dimm.vh ./arch_package.sv ./proj_package.sv ./interface.sv ./ddr4_model.svp

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

dram_top:
	vlib work
	vlog -work work +acc -l vcs.log -sv +incdir+./include +define+DDR4_4G_X8 $(DRAM_define) $(EXTRA_dram_top) ./tb/dram_top_tb.sv
	vsim -do ./scripts/dram_top_tb.do dram_top_tb
	run -all

%:
	vlog -sv +incdir+./src/include ./src/testbench/$*_tb.sv  ./src/modules/$*.sv $(EXTRA_dram_top)
	vsim $(SIMTERM) -voptargs="+acc" work.$*_tb -do $(SIMDO)

%.wav:
	vlog -sv +incdir+./src/include ./src/testbench/$*_tb.sv  ./src/modules/edge_det.sv ./src/modules/$*.sv $(EXTRA_dram_top)
	vsim -voptargs="+acc" work.$*_tb -do "do ./src/scripts/$*.do; run $(SIMTIME);" -suppress 2275


clean:
	rm -rf work transcript vsim.wlf *.log *.jou *.vstf *.vcd
