.SILENT: lint test
.ONESHELL: lint test

SHELL := /bin/bash

TOPDIR     := .
INCDIRROOT := $(TOPDIR)/rtl/include
SCRIPTROOT := $(TOPDIR)/scripts
WAVEROOT := $(TOPDIR)/waves
MODROOT    := $(TOPDIR)/rtl/modules
TBROOT     := $(TOPDIR)/tb
UVMTESTROOT  := $(TBROOT)/uvm
UNITTESTROOT := $(TBROOT)/unit
SCRATCH       := work

INCFLAGS := $(shell find $(INCDIRROOT) -type d -print0 2>/dev/null | xargs -0 -I{} echo +incdir+{})

PKG_SRCS := $(shell find $(TOPDIR)/rtl -type f \( -name "*_pkg.sv" -o -name "pkg_*.sv" \) 2>/dev/null | sort)

RTL_SRCS := $(shell \
  find $(INCDIRROOT) $(MODROOT) -type f -name "*.sv" \
    ! -name "*_pkg.sv" ! -name "pkg_*.sv" 2>/dev/null | sort)

VLIB ?= vlib
VLOG ?= vlog
VSIM ?= vsim
GUI ?= OFF

.PHONY: setup lint test clean_lib

setup:
	mkdir -p $(SCRATCH)
	python3 scripts/setup.py
	@echo "[setup] done"

# Usage: make lint folder=/sub/dir [file=name.sv[,name2.sv,...]] [include=/foo/bar,/baz/qux ...]
## Example: 
##  make lint folder=/memory/scratchpad 
### 	-> `vlogs` all the files under rtl/include/memory/scratchpad and rtl/modules/memory/scratchpad
##  make lint folder=/memory/scratchpad include=/network/xbar 
### 	-> `vlogs` all the files under rtl/include/memory/scratchpad and rtl/modules/memory/scratchpad, and adds all the include paths under rtl/modules/network/xbar and rtl/include/network/xbar
##  make lint folder=/memory/scratchpad file=scpad_cntrl.sv,tail.sv 
### 	-> `vlogs` the files under rtl/include/memory/scratchpad and only the specified files under it
lint:
	@if [ -z "$(folder)" ]; then 
	  echo "Usage: make lint folder=/sub/dir [file=name.sv[,name2.sv,...]] [include=/foo/bar,/baz/qux ...]"; exit 1; 
	fi; 

	SEARCH_FIRST_IN_INCLUDE="$(INCDIRROOT)$(folder)"; 
	[ -d "$$SEARCH_FIRST_IN_INCLUDE" ] || { echo "[lint] SEARCH_FIRST_IN_INCLUDE not found: $$SEARCH_FIRST_IN_INCLUDE"; exit 2; }; 

	SRCS=$$(find "$$SEARCH_FIRST_IN_INCLUDE" -type f -name '*.sv' -print 2>/dev/null | sort); 
	[ -n "$$SRCS" ] || { echo "[lint] No .sv files under $$SEARCH_FIRST_IN_INCLUDE"; exit 4; }; 

	NOW_SEARCH_IN_MODULES="$(MODROOT)$(folder)"; 

	[ -d "$$NOW_SEARCH_IN_MODULES" ] || { echo "[lint] NOW_SEARCH_IN_MODULES not found: $$NOW_SEARCH_IN_MODULES"; exit 2; }; 

	if [ -n "$(file)" ]; then
	  for f in $$(echo "$(file)" | tr ',' ' '); do 
	    P="$$NOW_SEARCH_IN_MODULES/$$f"; 
	    [ -f "$$P" ] || { echo "[lint] Not found: $$P"; exit 3; }; 
	    SRCS="$$SRCS $$P"; 
	  done; 
	else 
	  SRCS=$$(find "$$NOW_SEARCH_IN_MODULES" -type f -name '*.sv' -print 2>/dev/null | sort); 
	  [ -n "$$SRCS" ] || { echo "[lint] No .sv files under $$NOW_SEARCH_IN_MODULES"; exit 4; }; 
	fi; 

	PKGS=$$(printf '%s\n' $$SRCS | grep -E '_pkg\.sv$$' || true); 
	OTHERS=$$(printf '%s\n' $$SRCS | grep -Ev '_pkg\.sv$$' || true); 

	BASE_INCS="+incdir+$(INCDIRROOT)"; 
	MOD_INCS=$$(find "$$NOW_SEARCH_IN_MODULES" -type d -print 2>/dev/null | sed 's/^/+incdir+/'); 
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
	
	echo "[lint] compiling (in-order):"; 
	printf '  %s\n' $$ORDERED_SRCS; 
	
	$(VLOG) -sv -mfcu -work work +acc $$INCFLAGS $$ORDERED_SRCS; 
	echo "[lint] done"

# Similar to above! 
## Example: 
##  make test folder=/common/xbar tb_file=batcher_xbar_tb.sv
test:
	@if [ -z "$(folder)" ] || [ -z "$(tb_file)" ]; then \
	  echo "Usage: make $@ folder=/sub/dir tb_file=tb_top.sv [include=/foo,/bar]"; exit 1; \
	fi; \
	
	[ -d "$(INCDIRROOT)$(folder)" ] || { echo "[$@] Not found: $(INCDIRROOT)$(folder)"; exit 2; }; \
	[ -d "$(MODROOT)$(folder)" ]   || { echo "[$@] Not found: $(MODROOT)$(folder)"; exit 2; }; \
	[ -d "$(UNITTESTROOT)$(folder)" ]    || { echo "[$@] Not found: $(UNITTESTROOT)$(folder)"; exit 2; }; \
	\
	INCSRCS=$$(find "$(INCDIRROOT)$(folder)" -type f -name '*.sv' -print 2>/dev/null | sort); \

	MODSRCS=$$(if [ -n "$(file)" ]; then \
	  SR=""; \
	  for f in $$(echo "$(file)" | tr ',' ' '); do \
	    P="$(MODROOT)$(folder)/$$f"; [ -f "$$P" ] || { echo "[$@] Not found: $$P"; exit 3; }; SR="$$SR $$P"; \
	  done; echo "$$SR"; \
	else \
	  find "$(MODROOT)$(folder)" -type f -name '*.sv' -print 2>/dev/null | sort; \
	fi); \
	TBSRCS=$$(find "$(UNITTESTROOT)$(folder)" -type f -name '*.sv' -print 2>/dev/null | sort); \
	[ -n "$$INCSRCS" ] || { echo "[$@] No .sv under $(INCDIRROOT)$(folder)"; exit 4; }; \
	[ -n "$$MODSRCS" ] || { echo "[$@] No .sv under $(MODROOT)$(folder)"; exit 4; }; \
	[ -n "$$TBSRCS"  ] || { echo "[$@] No .sv under $(UNITTESTROOT)$(folder)"; exit 4; }; \
	\

	ALLSRCS="$$INCSRCS $$MODSRCS $$TBSRCS"; \
	PKGS=$$(printf '%s\n' $$ALLSRCS | grep -E '_pkg\.sv$$' || true); \
	OTHERS=$$(printf '%s\n' $$ALLSRCS | grep -Ev '_pkg\.sv$$' || true); \
	ORDERED_SRCS="$$PKGS $$OTHERS"; \

	BASE_INCS="+incdir+$(INCDIRROOT) +incdir+$(MODROOT) +incdir+$(UNITTESTROOT)"; \
	INCDIRS_INC=$$(find "$(INCDIRROOT)$(folder)" -type d -print 2>/dev/null | sed 's/^/+incdir+/'); \
	INCDIRS_MOD=$$(find "$(MODROOT)$(folder)"   -type d -print 2>/dev/null | sed 's/^/+incdir+/'); \
	INCDIRS_TB=$$(find "$(UNITTESTROOT)$(folder)"     -type d -print 2>/dev/null | sed 's/^/+incdir+/'); \

	EXTRA_INCS=""; \
	if [ -n "$(include)" ]; then \
	  for p in $$(echo "$(include)" | tr ',' ' '); do \
	    [ -d "$(INCDIRROOT)$$p" ] && EXTRA_INCS="$$EXTRA_INCS $$(find "$(INCDIRROOT)$$p" -type d -print 2>/dev/null | sed 's/^/+incdir+/')"; \
	    [ -d "$(MODROOT)$$p" ]    && EXTRA_INCS="$$EXTRA_INCS $$(find "$(MODROOT)$$p"    -type d -print 2>/dev/null | sed 's/^/+incdir+/')"; \
	    [ -d "$(UNITTESTROOT)$$p" ]     && EXTRA_INCS="$$EXTRA_INCS $$(find "$(UNITTESTROOT)$$p"     -type d -print 2>/dev/null | sed 's/^/+incdir+/')"; \
	  done; \
	fi; \
	INCFLAGS="$$BASE_INCS $$INCDIRS_INC $$INCDIRS_MOD $$INCDIRS_TB $$EXTRA_INCS"; \

	TB_CAND="$(UNITTESTROOT)$(folder)/$(tb_file)"; \
	[ -f "$$TB_CAND" ] || { echo "[$@] tb_file not found: $$TB_CAND"; exit 3; }; \
	TB_BASENAME=$$(basename "$$TB_CAND"); \
	TB_TOP="$${TB_BASENAME%.*}"; \

	[ -d work ] || $(VLIB) work; \
	echo "[$@] compiling (in-order):"; printf '  %s\n' $$ORDERED_SRCS; \
	$(VLOG) -sv -mfcu -work work +acc $$INCFLAGS $$ORDERED_SRCS; \

	@if [ "$(GUI)" = "ON" ]; then \
		echo "[$@] launching vsim GUI on work.$$TB_TOP"; \
		$(VSIM) -coverage -voptargs="+acc" work.$$TB_TOP -do "view objects; do $$WAVEROOT/$$TB_TOP.do; run -all;" -onfinish stop; \
	else \
		echo "[$@] launching vsim on work.$$TB_TOP"; \
		$(VSIM) -coverage -c -voptargs="+acc"  work.$$TB_TOP -do "run -all"; \
	fi 

clean:
	rm -rf $(SCRATCH) transcript vsim.wlf work modelsim.ini

