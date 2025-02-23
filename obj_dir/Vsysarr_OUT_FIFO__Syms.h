// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef VERILATED_VSYSARR_OUT_FIFO__SYMS_H_
#define VERILATED_VSYSARR_OUT_FIFO__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODEL CLASS

#include "Vsysarr_OUT_FIFO.h"

// INCLUDE MODULE CLASSES
#include "Vsysarr_OUT_FIFO___024root.h"
#include "Vsysarr_OUT_FIFO_systolic_array_OUT_FIFO_if.h"

// SYMS CLASS (contains all model state)
class alignas(VL_CACHE_LINE_BYTES)Vsysarr_OUT_FIFO__Syms final : public VerilatedSyms {
  public:
    // INTERNAL STATE
    Vsysarr_OUT_FIFO* const __Vm_modelp;
    VlDeleter __Vm_deleter;
    bool __Vm_didInit = false;

    // MODULE INSTANCE STATE
    Vsysarr_OUT_FIFO___024root     TOP;
    Vsysarr_OUT_FIFO_systolic_array_OUT_FIFO_if TOP__sysarr_OUT_FIFO_tb__DOT__fifo_if;

    // CONSTRUCTORS
    Vsysarr_OUT_FIFO__Syms(VerilatedContext* contextp, const char* namep, Vsysarr_OUT_FIFO* modelp);
    ~Vsysarr_OUT_FIFO__Syms();

    // METHODS
    const char* name() { return TOP.name(); }
};

#endif  // guard
