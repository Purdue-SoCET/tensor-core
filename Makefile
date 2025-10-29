SCRDIR = /home/asicfab/a/khatri12/tensor-core/src/scripts
SIMTIME = 100us             # Default simulation run time

DRAM_define = ./protected_modelsim/arch_defines.v ./protected_modelsim/dimm.vh ./protected_modelsim/arch_package.sv ./protected_modelsim/proj_package.sv ./protected_modelsim/interface.sv ./protected_modelsim/ddr4_model.svp
MODULES = ./src/modules/flex_counter.sv ./src/modules/init_state.sv ./src/modules/addr_mapper.sv ./src/modules/row_open.sv ./src/modules/command_FSM.sv ./src/modules/socetlib_counter.sv ./src/modules/timing_control.sv ./src/modules/control_unit.sv ./src/modules/signal_gen.sv ./src/modules/data_transfer.sv ./src/modules/scheduler_buffer.sv ./src/modules/edge_det.sv

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
    #SIMDO = "run $(SIMTIME);"
    SIMDO = "run -all;"
endif

fc:
	vlog -sv ./src/testbench/flex_counter_tb.sv ./src/modules/flex_counter.sv
	vsim $(SIMTERM) -voptargs="+acc" work.flex_counter_tb -do $(SIMDO)

icache:
	vlog -sv +incdir+./src/include ./src/testbench/icache_tb.sv ./src/modules/icache.sv
	vsim $(SIMTERM) -voptargs="+acc" work.icache_tb -do $(SIMDO)

# dram_controller_top:
#     vlog -work work +acc -l vcs.log -sv +define+DDR4_4G_X8 $(DRAM_define)
#     vsim tb
#     run -all

%:
	vlog -sv +incdir+./src/include +incdir+./src/modules ./src/testbench/$*_tb.sv ./src/modules/$*.sv ./src/modules/flex_counter.sv
	vsim $(SIMTERM) -voptargs="+acc" work.$*_tb -do $(SIMDO)

%.wav:
	vlog -sv +cover +define+DDR4_4G_X8 +define+MODEL_DEBUG_CMDS +incdir+./src/include +incdir+./protected_modelsim $(DRAM_define) ./src/testbench/$*_tb.sv ./src/modules/$*.sv $(MODULES)
	vsim -coverage -voptargs="+acc" work.$*_tb -do "do $(SCRDIR)/$*.do; run -all;" -suppress 2275


clean:
	rm -rf work transcript vsim.wlf *.log *.jou *.vstf *.vcd
