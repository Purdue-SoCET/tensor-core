// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vsystolic_array_tb.h for the primary calling header

#include "Vsystolic_array_tb__pch.h"
#include "Vsystolic_array_tb_systolic_array_add_if.h"

VL_ATTR_COLD void Vsystolic_array_tb_systolic_array_add_if___ctor_var_reset(Vsystolic_array_tb_systolic_array_add_if* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vsystolic_array_tb_systolic_array_add_if___ctor_var_reset\n"); );
    Vsystolic_array_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelf->__PVT__count = VL_RAND_RESET_I(1);
}
