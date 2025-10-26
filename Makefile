# Dir structure
MKDIR = $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRC_DIR = $(MKDIR)/src
MODULE_DIR = $(SRC_DIR)/modules
TB_DIR = $(SRC_DIR)/testbench
INCLUDE_DIR = $(SRC_DIR)/include
WAVES_DIR = $(SRC_DIR)/waves
SCRIPTS_DIR = $(SRC_DIR)/scripts
MEMORY_DIR = $(MKDIR)/memory

# Memory config
MEMINIT ?= $(MEMORY_DIR)/meminit.hex
MEMDUMP ?= $(MEMORY_DIR)/memdump.hex
MEMARGS = +meminit=$(MEMINIT) +memdump=$(MEMDUMP) -sv_lib memory 

# Questa
VLOG = vlog
VSIM = vsim
WARNINGS_IGNORE = -suppress 3015 -suppress 2275 # ignore port mismatch and ignore non-synth
VLOG_FLAGS = -sv +incdir+./src/include
VSIM_FLAGS = -voptargs="+acc" $(WARNINGS_IGNORE)

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
	SIMDO = "view objects; $(WAVDO); run -all;"
else
	# view text output in cmdline mode
	SIMTERM = -c
	SIMDO = "run -all;"
endif

help:
	@echo "  source              - Compile all source files"
	@echo "  <module>            - Run simulation"
	@echo "  <module>.wav        - Run qsim GUI simulation"
	@echo "  <module>_vlint      - Lint specific module"
	@echo "  clean               - Clean"
	@echo ""

# Generic make targets
%:
	$(VLOG) $(VLOG_FLAGS) $(TB_DIR)/$*_tb.sv $(MODULE_DIR)/*.sv
	$(VSIM) $(VSIM_FLAGS) -c work.$*_tb -do "run -all;"

%.wav:
	$(VLOG) $(VLOG_FLAGS) $(TB_DIR)/$*_tb.sv $(MODULE_DIR)/$*.sv
	$(VSIM) $(VSIM_FLAGS) work.$*_tb -do $(SIMDO) -onfinish stop 

%_vlint:
	verilator --lint-only src/modules/$*.sv +incdir+$(INCLUDE_DIR) +incdir+$(MODULE_DIR)

clean:
	rm -rf work transcript vsim.wlf *.log *.jou *.vstf *.vcd

# Unique targets
memory_subsystem.wav:
	$(VLOG) $(VLOG_FLAGS) ./src/include/*.vh ./src/testbench/memory_subsystem_tb.sv ./src/modules/*.sv
	$(VSIM) $(VSIM_FLAGS) work.memory_subsystem_tb -sv_lib memory -do "do $(WAVES_DIR)/memory_subsystem.do; run $(SIMTIME);"

system.wav:
	touch $(MEMDUMP)
	$(VLOG) $(VLOG_FLAGS) ./src/include/*.vh ./src/testbench/system_tb.sv ./src/modules/*.sv
	$(VSIM) $(VSIM_FLAGS) work.system_tb $(MEMARGS) -do "do $(WAVES_DIR)/system.do; run -a;" -suppress 2275

system:
	touch $(MEMDUMP)
	$(VLOG) $(VLOG_FLAGS) ./src/include/*.vh ./src/testbench/system_tb.sv ./src/modules/*.sv
	$(VSIM) $(VSIM_FLAGS)  -c $(MEMARGS) work.system_tb -sv_lib memory -do $(SIMDO)

test_memory_wav:
	$(VLOG) $(VLOG_FLAGS) ./src/include/*.vh ./src/testbench/memory_subsystem_tb.sv ./src/modules/*.sv
	$(VSIM) $(VSIM_FLAGS) work.memory_subsystem_tb -sv_lib memory -do "do $(WAVES_DIR)/memory_subsystem.do; run $(SIMTIME);" -suppress 2275

icache:
	$(VLOG) $(VLOG_FLAGS) ./src/testbench/icache_tb.sv ./src/modules/icache.sv
	$(VSIM) $(SIMTERM) $(VSIM_FLAGS) work.icache_tb -do $(SIMDO)

mls:
	$(VLOG) $(VLOG_FLAGS) ./src/testbench/fu_matrix_ls_tb.sv ./src/modules/fu_matrix_ls.sv
	$(VSIM) $(VSIM_FLAGS) work.fu_matrix_ls_tb

wb:
	pwd
	ls ./src/waves/
	$(VLOG) $(VLOG_FLAGS) ./src/testbench/writeback_tb.sv ./src/modules/writeback.sv
	$(VSIM) $(VSIM_FLAGS) work.writeback_tb -do "do $(abspath ./src/waves/writeback.do); run -all"

gsau:
	$(VLOG) $(VLOG_FLAGS) ./src/modules/simple_systolic_model.sv ./src/include/gsau_control_unit_if.vh ./src/testbench/gsau_control_unit_tb.sv ./src/modules/gsau_control_unit.sv ./src/modules/sync_fifo.sv
    #$(VSIM) $(VSIM_FLAGS) work.gsau_control_unit_tb -do $(SIMDO) -onfinish stop 
	vsim -coverage -voptargs="+acc" work.gsau_control_unit_tb -do "view objects; do ./src/waves/gsau_control_unit_tb.do; run -all;" -onfinish stop
#$(VSIM) $(VSIM_FLAGS) work._tb -do $(SIMDO) -onfinish stop 
#$(VSIM) $(VSIM_FLAGS) work.gsau_control_unit_tb -do $(SIMDO)