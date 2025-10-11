SHELL := /bin/bash

SIMTIME    ?= 100us
TOPDIR     := .
INCDIRROOT := $(TOPDIR)/rtl/include
MODROOT    := $(TOPDIR)/rtl/modules
TBROOT     := $(TOPDIR)/rtl/tests
WORK       := work

INCFLAGS := $(shell find $(INCDIRROOT) -type d -print0 2>/dev/null | xargs -0 -I{} echo +incdir+{})

PKG_SRCS := $(shell find $(TOPDIR)/rtl -type f \( -name "*_pkg.sv" -o -name "pkg_*.sv" \) 2>/dev/null | sort)

RTL_SRCS := $(shell \
  find $(INCDIRROOT) $(MODROOT) -type f -name "*.sv" \
    ! -name "*_pkg.sv" ! -name "pkg_*.sv" 2>/dev/null | sort)

ifneq (0,$(words $(filter %.wav,$(MAKECMDGOALS))))
    DOFILES = $(notdir $(basename $(wildcard $(shell find . -name "*.do"))))
    DOFILE  = $(filter $(MAKECMDGOALS:%.wav=%) $(MAKECMDGOALS:%_tb.wav=%), $(DOFILES))
    ifeq (1,$(words $(DOFILE)))
        WAVDO = do $(firstword $(shell find . -name $(DOFILE).do))
    else
        WAVDO = add wave *
    endif
    SIMDO = "view objects; $(WAVDO); run $(SIMTIME);"
else
    SIMTERM = -c
    SIMDO   = "run $(SIMTIME);"
endif

.PHONY: all build run clean show lint

all: build

show:
	@echo "INCFLAGS  = $(INCFLAGS)"
	@echo "PKG_SRCS  = $(words $(PKG_SRCS)) files"
	@echo "RTL_SRCS  = $(words $(RTL_SRCS)) files"

$(WORK):
	@vlib $(WORK) 2>/dev/null || true
	@vmap work $(WORK)        2>/dev/null || true

build: $(WORK)
	@echo "[vlog] packages: $(words $(PKG_SRCS))"
	@if [ -n "$(PKG_SRCS)" ]; then \
	  vlog -sv $(INCFLAGS) $(PKG_SRCS); \
	fi
	@echo "[vlog] rtl+if:   $(words $(RTL_SRCS))"
	@if [ -n "$(RTL_SRCS)" ]; then \
	  vlog -sv $(INCFLAGS) $(RTL_SRCS); \
	fi
	@echo "[build] done"

source: build

%: build
	@tb="$(TBROOT)/$@_tb.sv"; \
	if [ ! -f "$$tb" ]; then \
	  echo "[error] testbench $$tb not found"; exit 2; \
	fi; \
	echo "[vlog] $$tb"; \
	vlog -sv $(INCFLAGS) "$$tb"; \
	echo "[vsim] $@_tb"; \
	vsim $(SIMTERM) -voptargs="+acc" work.$@_tb -do $(SIMDO)

%_vlint:
	@echo "[verilator] lint $*"
	@verilator --lint-only $(MODROOT)/$*.sv -I$(INCDIRROOT) -I$(MODROOT)

%.wav: build
	@tb="$(TBROOT)/$*_tb.sv"; \
	if [ ! -f "$$tb" ]; then echo "[error] $$tb not found"; exit 2; fi; \
	vlog -sv $(INCFLAGS) "$$tb"; \
	vsim -voptargs="+acc" work.$*_tb -do "run $(SIMTIME);" -suppress 2275

clean:
	rm -rf $(WORK) transcript vsim.wlf *.log *.jou *.vstf *.vcd
