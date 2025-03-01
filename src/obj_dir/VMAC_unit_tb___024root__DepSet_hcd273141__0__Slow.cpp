// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VMAC_unit_tb.h for the primary calling header

#include "VMAC_unit_tb__pch.h"
#include "VMAC_unit_tb__Syms.h"
#include "VMAC_unit_tb___024root.h"

#ifdef VL_DEBUG
VL_ATTR_COLD void VMAC_unit_tb___024root___dump_triggers__stl(VMAC_unit_tb___024root* vlSelf);
#endif  // VL_DEBUG

VL_ATTR_COLD void VMAC_unit_tb___024root___eval_triggers__stl(VMAC_unit_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VMAC_unit_tb___024root___eval_triggers__stl\n"); );
    VMAC_unit_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.__VstlTriggered.set(0U, (IData)(vlSelfRef.__VstlFirstIteration));
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VMAC_unit_tb___024root___dump_triggers__stl(vlSelf);
    }
#endif
}

VL_ATTR_COLD void VMAC_unit_tb___024root___stl_sequent__TOP__0(VMAC_unit_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VMAC_unit_tb___024root___stl_sequent__TOP__0\n"); );
    VMAC_unit_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__run = ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__run_latched) 
                                                 | (IData)(vlSymsp->TOP__MAC_unit_tb__DOT__mac_if.start));
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__ovf = 0U;
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul1__DOT__MUL__DOT__frac_out_26b 
        = (0x3ffffffU & ((0x1000U | (0xffcU & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__input_x) 
                                               << 2U))) 
                         * (0x1000U | (0xffcU & ((IData)(vlSymsp->TOP__MAC_unit_tb__DOT__mac_if.weight) 
                                                 << 2U)))));
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__nxt_input_x 
        = vlSelfRef.MAC_unit_tb__DOT__dut__DOT__input_x;
    if (vlSymsp->TOP__MAC_unit_tb__DOT__mac_if.MAC_shift) {
        vlSelfRef.MAC_unit_tb__DOT__dut__DOT__nxt_input_x 
            = vlSymsp->TOP__MAC_unit_tb__DOT__mac_if.in_value;
    }
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul2__DOT__add_EXPs__DOT__r_exp1 
        = (0x1fU & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_exp1_in) 
                    - (IData)(0x10U)));
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul2__DOT__add_EXPs__DOT__r_exp2 
        = (0x1fU & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_exp2_in) 
                    - (IData)(0x10U)));
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul2__DOT__add_EXPs__DOT__r_sum 
        = (0x1fU & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul2__DOT__add_EXPs__DOT__r_exp1) 
                    + (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul2__DOT__add_EXPs__DOT__r_exp2)));
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__shifted_frac 
        = (((((((((0x800U == (0x1800U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in))) 
                  | (0x400U == (0x1c00U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))) 
                 | (0x200U == (0x1e00U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))) 
                | (0x100U == (0x1f00U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))) 
               | (0x80U == (0x1f80U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))) 
              | (0x40U == (0x1fc0U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))) 
             | (0x20U == (0x1fe0U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))) 
            | (0x10U == (0x1ff0U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in))))
            ? ((0x800U == (0x1800U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                ? (0x1ffeU & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                              << 1U)) : ((0x400U == 
                                          (0x1c00U 
                                           & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                          ? (0x1ffcU 
                                             & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                                                << 2U))
                                          : ((0x200U 
                                              == (0x1e00U 
                                                  & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                              ? (0x1ff8U 
                                                 & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                                                    << 3U))
                                              : ((0x100U 
                                                  == 
                                                  (0x1f00U 
                                                   & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                                  ? 
                                                 (0x1ff0U 
                                                  & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                                                     << 4U))
                                                  : 
                                                 ((0x80U 
                                                   == 
                                                   (0x1f80U 
                                                    & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                                   ? 
                                                  (0x1fe0U 
                                                   & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                                                      << 5U))
                                                   : 
                                                  ((0x40U 
                                                    == 
                                                    (0x1fc0U 
                                                     & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                                    ? 
                                                   (0x1fc0U 
                                                    & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                                                       << 6U))
                                                    : 
                                                   ((0x20U 
                                                     == 
                                                     (0x1fe0U 
                                                      & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                                     ? 
                                                    (0x1f80U 
                                                     & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                                                        << 7U))
                                                     : 
                                                    (0x1f00U 
                                                     & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                                                        << 8U)))))))))
            : ((8U == (0x1ff8U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                ? (0x1e00U & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                              << 9U)) : ((4U == (0x1ffcU 
                                                 & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                          ? (0x1c00U 
                                             & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                                                << 0xaU))
                                          : ((2U == 
                                              (0x1ffeU 
                                               & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                              ? (0x1800U 
                                                 & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                                                    << 0xbU))
                                              : ((1U 
                                                  == (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in))
                                                  ? 
                                                 (0x1000U 
                                                  & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                                                     << 0xcU))
                                                  : (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in))))));
    if (vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_carry_in) {
        if ((0x1eU == (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_exp_max_s3_in))) {
            vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__ovf = 1U;
        }
        vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__round_this 
            = (0xfffU & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in) 
                         >> 1U));
    } else {
        vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__round_this 
            = (0xfffU & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__shifted_frac));
    }
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__shifted_amount 
        = (((((((((0x800U == (0x1800U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in))) 
                  | (0x400U == (0x1c00U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))) 
                 | (0x200U == (0x1e00U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))) 
                | (0x100U == (0x1f00U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))) 
               | (0x80U == (0x1f80U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))) 
              | (0x40U == (0x1fc0U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))) 
             | (0x20U == (0x1fe0U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))) 
            | (0x10U == (0x1ff0U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in))))
            ? ((0x800U == (0x1800U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                ? 1U : ((0x400U == (0x1c00U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                         ? 2U : ((0x200U == (0x1e00U 
                                             & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                  ? 3U : ((0x100U == 
                                           (0x1f00U 
                                            & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                           ? 4U : (
                                                   (0x80U 
                                                    == 
                                                    (0x1f80U 
                                                     & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                                    ? 5U
                                                    : 
                                                   ((0x40U 
                                                     == 
                                                     (0x1fc0U 
                                                      & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                                     ? 6U
                                                     : 
                                                    ((0x20U 
                                                      == 
                                                      (0x1fe0U 
                                                       & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                                      ? 7U
                                                      : 8U)))))))
            : ((8U == (0x1ff8U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                ? 9U : ((4U == (0x1ffcU & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                         ? 0xaU : ((2U == (0x1ffeU 
                                           & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in)))
                                    ? 0xbU : ((1U == (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sum_in))
                                               ? 0xcU
                                               : 0U)))));
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__frac1_signed 
        = vlSelfRef.MAC_unit_tb__DOT__dut__DOT__frac_shifted_in;
    if (vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sign_shifted_in) {
        vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__frac1_signed 
            = (0x3fffU & (- (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__frac1_signed)));
    }
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__frac2_signed 
        = vlSelfRef.MAC_unit_tb__DOT__dut__DOT__frac_not_shifted_in;
    if (vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sign_not_shifted_in) {
        vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__frac2_signed 
            = (0x3fffU & (- (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__frac2_signed)));
    }
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_sum_exp 
        = (0x1fU & (((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_exp1_in) 
                     + ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_exp2_in) 
                        + (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_carryout_in))) 
                    - (IData)(0xfU)));
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__sum_signed 
        = (0x3fffU & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__frac1_signed) 
                      + (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__frac2_signed)));
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_carry_out = 0U;
    if ((1U & ((((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__frac1_signed) 
                 & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__frac2_signed)) 
                >> 0xdU) & (~ ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__sum_signed) 
                               >> 0xdU))))) {
        vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_carry_out = 1U;
        vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__sum_signed 
            = (0x2000U | (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__sum_signed));
    }
    if ((IData)((((~ ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__frac1_signed) 
                      >> 0xdU)) & (~ ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__frac2_signed) 
                                      >> 0xdU))) & 
                 ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__sum_signed) 
                  >> 0xdU)))) {
        vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_carry_out = 1U;
        vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__sum_signed 
            = (0x1fffU & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__sum_signed));
    }
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__unf = 0U;
    if ((1U & (~ (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_carry_in)))) {
        if (((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_exp_max_s3_in) 
             < (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__shifted_amount))) {
            vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__unf = 1U;
        }
    }
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__u_exp1 
        = vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_exp_max_s3_in;
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__u_shifted_amount 
        = vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__shifted_amount;
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__u_result 
        = (0x3fU & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__u_exp1) 
                    - (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__u_shifted_amount)));
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add1__DOT__diff 
        = (0x3fU & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_sum_exp) 
                    - (0x1fU & ((IData)(vlSymsp->TOP__MAC_unit_tb__DOT__mac_if.in_accumulate) 
                                >> 0xaU))));
    if ((0x20U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add1__DOT__diff))) {
        if ((0x20U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add1__DOT__diff))) {
            vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add1__DOT__diff 
                = (0x3fU & (- (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add1__DOT__diff)));
            vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add1__DOT__cmp_out = 1U;
        }
    } else {
        vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add1__DOT__cmp_out = 0U;
    }
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_result 
        = ((((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_sign1_in) 
             ^ (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_sign2_in)) 
            << 0xfU) | (((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_sum_exp) 
                         << 0xaU) | (0x3ffU & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_carryout_in)
                                                ? ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_product_in) 
                                                   >> 3U)
                                                : ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__mul_product_in) 
                                                   >> 2U)))));
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__rounded_fraction 
        = (0xfffU & ((2U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__round_this))
                      ? ((IData)(1U) + (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__round_this))
                      : (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__round_this)));
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__round_flag 
        = (1U & ((IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add3__DOT__round_this) 
                 >> 1U));
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sign_out = 0U;
    vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__change_to_unsigned__DOT__rfrac_signed 
        = vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__sum_signed;
    if ((0x2000U & (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__sum_signed))) {
        vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add_sign_out = 1U;
        vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__change_to_unsigned__DOT__rfrac_signed 
            = (0x3fffU & (- (IData)(vlSelfRef.MAC_unit_tb__DOT__dut__DOT__add2__DOT__sum_signed)));
    }
}
