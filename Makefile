SHELL := /bin/bash

SIMTIME    ?= 100us
TOPDIR     := .
INCDIRROOT := $(TOPDIR)/src/include
MODROOT    := $(TOPDIR)/src/modules
TBROOT     := $(TOPDIR)/src/testbench
WORK       := work

# Include directories
INCFLAGS := $(shell find $(INCDIRROOT) -type d -print0 2>/dev/null | xargs -0 -I{} echo +incdir+{})

# Package sources
PKG_SRCS := $(shell find $(TOPDIR)/src -type f \( -name "*_pkg.sv" -o -name "pkg_*.sv" \) 2>/dev/null | sort)

# All RTL sources excluding packages
RTL_SRCS := $(shell find $(INCDIRROOT) $(MODROOT) -type f -name "*.sv" ! -name "*_pkg.sv" ! -name "pkg_*.sv" 2>/dev/null | sort)

# Determine make target
TARGET := $(firstword $(filter %.wav %_vlint %,$(MAKECMDGOALS)))

# Strip suffixes to get module name
MODULE := $(TARGET)
MODULE := $(patsubst %.wav,%,$(MODULE))
MODULE := $(patsubst %_vlint,%,$(MODULE))
MODULE := $(strip $(MODULE))

# Find RTL source recursively in modules
SRC_FILE := $(shell find $(MODROOT) -type f -name "$(MODULE).sv" 2>/dev/null | head -n1)
TB_FILE  := $(TBROOT)/$(MODULE)_tb.sv

# Detect headless (no $DISPLAY)
ifeq ($(DISPLAY),)
SIMTERM = -c
else
SIMTERM =
endif

# Simulation command
SIMDO = "run $(SIMTIME);"

.PHONY: all build clean show lint

all: build

# Show info
show:
	@echo "Module    = '$(MODULE)'"
	@echo "SRC_FILE  = '$(SRC_FILE)'"
	@echo "TB_FILE   = '$(TB_FILE)'"
	@echo "PKG_SRCS  = $(words $(PKG_SRCS)) files"
	@echo "RTL_SRCS  = $(words $(RTL_SRCS)) files"

# Create work library
$(WORK):
	@vlib $(WORK) 2>/dev/null || true
	@vmap work $(WORK) 2>/dev/null || true

# Build only requested module + packages
build: $(WORK)
	@if [ -z "$(SRC_FILE)" ]; then \
	  echo "[error] source '$(MODULE).sv' not found in $(MODROOT)"; exit 2; \
	fi
	@if [ -n "$(PKG_SRCS)" ]; then \
	  echo "[vlog] packages: $(words $(PKG_SRCS))"; \
	  vlog -sv $(INCFLAGS) $(PKG_SRCS); \
	fi
	@echo "[vlog] rtl: $(SRC_FILE)"; \
	vlog -sv $(INCFLAGS) "$(SRC_FILE)"
	@echo "[build] done"

# Run simulation (.wav)
%.wav: build
	@if [ ! -f "$(TB_FILE)" ]; then echo "[error] testbench '$(TB_FILE)' not found"; exit 2; fi
	@echo "[vlog] compiling testbench $(TB_FILE)"; \
	vlog -sv $(INCFLAGS) "$(TB_FILE)"
	@echo "[vsim] running $(MODULE)_tb"; \
	vsim $(SIMTERM) -voptargs="+acc" work.$(MODULE)_tb -do $(SIMDO) -suppress 2275

# Lint a single module (_vlint)
%_vlint:
	@if [ -z "$(SRC_FILE)" ]; then echo "[error] source '$(MODULE).sv' not found in $(MODROOT)"; exit 2; fi
	@echo "[verilator] linting $(MODULE)"; \
	verilator --lint-only "$(SRC_FILE)" -I$(INCDIRROOT) -I$(MODROOT)

# Clean all generated files
clean:
	rm -rf $(WORK) transcript vsim.wlf *.log *.jou *.vstf *.vcd
	@echo "[clean] done"