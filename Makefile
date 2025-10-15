.SILENT: verify
.ONESHELL: verify

SHELL := /bin/bash

TOPDIR     := .
INCDIRROOT := $(TOPDIR)/rtl/include
SCRIPTROOT := $(TOPDIR)/scripts
MODROOT    := $(TOPDIR)/rtl/modules
TBROOT     := $(TOPDIR)/tb
UVMTESTROOT  := $(TBROOT)/tb/uvm
UNITTESTROOT := $(TBROOT)/tb/unit
SCRATCH       := work

INCFLAGS := $(shell find $(INCDIRROOT) -type d -print0 2>/dev/null | xargs -0 -I{} echo +incdir+{})

PKG_SRCS := $(shell find $(TOPDIR)/rtl -type f \( -name "*_pkg.sv" -o -name "pkg_*.sv" \) 2>/dev/null | sort)

RTL_SRCS := $(shell \
  find $(INCDIRROOT) $(MODROOT) -type f -name "*.sv" \
    ! -name "*_pkg.sv" ! -name "pkg_*.sv" 2>/dev/null | sort)

VLIB ?= vlib
VLOG ?= vlog
VSIM ?= vsim

.PHONY: all setup verify clean_lib

all: setup verify

setup:
	mkdir -p $(SCRATCH)
	python3 scripts/setup.py
	@echo "[setup] done"

# Usage: make verify folder=/sub/dir [file=name.sv[,name2.sv,...]] [include=/foo/bar,/baz/qux ...]
## Example: 
##  make verify folder=/memory/scratchpad 
### 	-> `vlogs` all the files under rtl/include/memory/scratchpad and rtl/modules/memory/scratchpad
##  make verify folder=/memory/scratchpad include=/network/xbar 
### 	-> `vlogs` all the files under rtl/include/memory/scratchpad and rtl/modules/memory/scratchpad, and adds all the include paths under rtl/modules/network/xbar and rtl/include/network/xbar
##  make verify folder=/memory/scratchpad file=scpad_cntrl.sv,tail.sv 
### 	-> `vlogs` the files under rtl/include/memory/scratchpad and only the specified files under it
verify:
	@if [ -z "$(folder)" ]; then 
	  echo "Usage: make verify folder=/sub/dir [file=name.sv[,name2.sv,...]] [include=/foo/bar,/baz/qux ...]"; exit 1; 
	fi; 

	SEARCH_FIRST_IN_INCLUDE="$(INCDIRROOT)$(folder)"; 
	[ -d "$$SEARCH_FIRST_IN_INCLUDE" ] || { echo "[verify] SEARCH_FIRST_IN_INCLUDE not found: $$SEARCH_FIRST_IN_INCLUDE"; exit 2; }; 

	SRCS=$$(find "$$SEARCH_FIRST_IN_INCLUDE" -type f -name '*.sv' -print 2>/dev/null | sort); 
	[ -n "$$SRCS" ] || { echo "[verify] No .sv files under $$SEARCH_FIRST_IN_INCLUDE"; exit 4; }; 

	NOW_SEARCH_IN_MODULES="$(MODROOT)$(folder)"; 

	[ -d "$$NOW_SEARCH_IN_MODULES" ] || { echo "[verify] NOW_SEARCH_IN_MODULES not found: $$NOW_SEARCH_IN_MODULES"; exit 2; }; 

	if [ -n "$(file)" ]; then
	  for f in $$(echo "$(file)" | tr ',' ' '); do 
	    P="$$NOW_SEARCH_IN_MODULES/$$f"; 
	    [ -f "$$P" ] || { echo "[verify] Not found: $$P"; exit 3; }; 
	    SRCS="$$SRCS $$P"; 
	  done; 
	else 
	  SRCS=$$(find "$$NOW_SEARCH_IN_MODULES" -type f -name '*.sv' -print 2>/dev/null | sort); 
	  [ -n "$$SRCS" ] || { echo "[verify] No .sv files under $$NOW_SEARCH_IN_MODULES"; exit 4; }; 
	fi; 

	PKGS=$$(printf '%s\n' $$SRCS | grep -E '_pkg\.sv$$' || true); 
	OTHERS=$$(printf '%s\n' $$SRCS | grep -Ev '_pkg\.sv$$' || true); 

	BASE_INCS="+incdir+$(INCDIRROOT)"; 
	MOD_INCS=$$(find "$$BASE_DIR" -type d -print 2>/dev/null | sed 's/^/+incdir+/'); 
	INC_INCS=$$(find "$(INCDIRROOT)$(folder)" -type d -print 2>/dev/null | sed 's/^/+incdir+/'); 

	EXTRA_INCS=""; 
	if [ -n "$(include)" ]; then 
	  for p in $$(echo "$(include)" | tr ',' ' '); do 
	    [ -d "$(MODROOT)$$p" ] && EXTRA_INCS="$$EXTRA_INCS $$(find "$(MODROOT)$$p" -type d -print 2>/dev/null | sed 's/^/+incdir+/')"; 
	    [ -d "$(INCDIRROOT)$$p" ] && EXTRA_INCS="$$EXTRA_INCS $$(find "$(INCDIRROOT)$$p" -type d -print 2>/dev/null | sed 's/^/+incdir+/')"; 
	  done; 
	fi; 

	ORDERED_SRCS="$$PKGS $$OTHERS"; 
	INCFLAGS="$$BASE_INCS $$MOD_INCS $$INC_INCS $$EXTRA_INCS"; 
	
	echo "[verify] compiling (in-order):"; 
	printf '  %s\n' $$ORDERED_SRCS; 
	
	$(VLOG) -sv -mfcu -work work +acc $$INCFLAGS $$ORDERED_SRCS; 
	echo "[verify] done"

clean_lib:
	rm -rf $(SCRATCH) transcript vsim.wlf work modelsim.ini

