// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vsystolic_array_tb.h for the primary calling header

#ifndef VERILATED_VSYSTOLIC_ARRAY_TB___024ROOT_H_
#define VERILATED_VSYSTOLIC_ARRAY_TB___024ROOT_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
class Vsystolic_array_tb_sysarr_MAC;
class Vsystolic_array_tb_systolic_array_MAC_if;
class Vsystolic_array_tb_systolic_array_add_if;
class Vsystolic_array_tb_systolic_array_control_unit_if;
class Vsystolic_array_tb_systolic_array_if;


class Vsystolic_array_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vsystolic_array_tb___024root final : public VerilatedModule {
  public:
    // CELLS
    Vsystolic_array_tb_systolic_array_if* __PVT__systolic_array_tb__DOT__memory_if;
    Vsystolic_array_tb_systolic_array_control_unit_if* __PVT__systolic_array_tb__DOT__DUT__DOT__control_unit_if;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__15__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__14__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__13__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__12__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__11__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__10__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__9__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__8__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__7__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__6__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__5__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__4__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__3__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__2__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__1__KET__;
    Vsystolic_array_tb_systolic_array_MAC_if* __PVT__systolic_array_tb__DOT__DUT__DOT__mac_ifs__BRA__0__KET__;
    Vsystolic_array_tb_systolic_array_add_if* __PVT__systolic_array_tb__DOT__DUT__DOT__add_ifs__BRA__3__KET__;
    Vsystolic_array_tb_systolic_array_add_if* __PVT__systolic_array_tb__DOT__DUT__DOT__add_ifs__BRA__2__KET__;
    Vsystolic_array_tb_systolic_array_add_if* __PVT__systolic_array_tb__DOT__DUT__DOT__add_ifs__BRA__1__KET__;
    Vsystolic_array_tb_systolic_array_add_if* __PVT__systolic_array_tb__DOT__DUT__DOT__add_ifs__BRA__0__KET__;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__0__KET____DOT__genblk1__BRA__0__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__0__KET____DOT__genblk1__BRA__1__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__0__KET____DOT__genblk1__BRA__2__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__0__KET____DOT__genblk1__BRA__3__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__1__KET____DOT__genblk1__BRA__0__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__1__KET____DOT__genblk1__BRA__1__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__1__KET____DOT__genblk1__BRA__2__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__1__KET____DOT__genblk1__BRA__3__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__2__KET____DOT__genblk1__BRA__0__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__2__KET____DOT__genblk1__BRA__1__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__2__KET____DOT__genblk1__BRA__2__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__2__KET____DOT__genblk1__BRA__3__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__3__KET____DOT__genblk1__BRA__0__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__3__KET____DOT__genblk1__BRA__1__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__3__KET____DOT__genblk1__BRA__2__KET____DOT__mac_inst;
    Vsystolic_array_tb_sysarr_MAC* __PVT__systolic_array_tb__DOT__DUT__DOT__genblk4__BRA__3__KET____DOT__genblk1__BRA__3__KET____DOT__mac_inst;

    // DESIGN SPECIFIC STATE
    // Anonymous structures to workaround compiler member-count bugs
    struct {
        CData/*0:0*/ systolic_array_tb__DOT__tb_nRST;
        CData/*0:0*/ systolic_array_tb__DOT__tb_clk;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__loadi;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__loadw;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__loadps;
        CData/*1:0*/ systolic_array_tb__DOT__DUT__DOT__row_out;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__start_flag;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__nxt_MAC_start;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__nxt_add_start;
        CData/*2:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__iteration_full;
        CData/*2:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__nxt_iteration_full;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__input_loading;
        CData/*1:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__curr_input_row;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__partial_loading;
        CData/*1:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__curr_partial_row;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__output_loading;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__in_data_loaded;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__ps_data_loaded;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__nxt_in_data_loaded;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__nxt_ps_data_loaded;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__input_fully_loaded;
        CData/*1:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__partial_fully_loaded;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__nxt_input_fully_loaded;
        CData/*1:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__nxt_partial_fully_loaded;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__ready;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__MAC_done;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__nxt_MAC_done;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT____Vlvbound_hd9ef4104__0;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT____Vlvbound_haaf93ebe__0;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__0__KET____DOT__i_fifo__DOT__wrt_ptr;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__0__KET____DOT__i_fifo__DOT__wrt_ptr_nxt;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__1__KET____DOT__i_fifo__DOT__wrt_ptr;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__1__KET____DOT__i_fifo__DOT__wrt_ptr_nxt;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__2__KET____DOT__i_fifo__DOT__wrt_ptr;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__2__KET____DOT__i_fifo__DOT__wrt_ptr_nxt;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__3__KET____DOT__i_fifo__DOT__wrt_ptr;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__3__KET____DOT__i_fifo__DOT__wrt_ptr_nxt;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__0__KET____DOT__ps_fifos__DOT__wrt_ptr;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__0__KET____DOT__ps_fifos__DOT__wrt_ptr_nxt;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__1__KET____DOT__ps_fifos__DOT__wrt_ptr;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__1__KET____DOT__ps_fifos__DOT__wrt_ptr_nxt;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__2__KET____DOT__ps_fifos__DOT__wrt_ptr;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__2__KET____DOT__ps_fifos__DOT__wrt_ptr_nxt;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__3__KET____DOT__ps_fifos__DOT__wrt_ptr;
        CData/*3:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__3__KET____DOT__ps_fifos__DOT__wrt_ptr_nxt;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__run_latched;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__start_passthrough_2;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__start_passthrough_3;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__run;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add_sign_shifted_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add_sign_not_shifted_in;
        CData/*4:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add_exp_max_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add_sign_out;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add_sign_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add_carry_out;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add_carry_in;
        CData/*4:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add_exp_max_s3_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add1__DOT__cmp_out;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add1__DOT__diff;
        CData/*4:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add3__DOT__shifted_amount;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add3__DOT__ovf;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add3__DOT__unf;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add3__DOT__u_exp1;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add3__DOT__u_shifted_amount;
    };
    struct {
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add3__DOT__u_result;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add3__DOT__round_flag;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__run_latched;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__start_passthrough_2;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__start_passthrough_3;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__run;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add_sign_shifted_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add_sign_not_shifted_in;
        CData/*4:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add_exp_max_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add_sign_out;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add_sign_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add_carry_out;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add_carry_in;
        CData/*4:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add_exp_max_s3_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add1__DOT__cmp_out;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add1__DOT__diff;
        CData/*4:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add3__DOT__shifted_amount;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add3__DOT__ovf;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add3__DOT__unf;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add3__DOT__u_exp1;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add3__DOT__u_shifted_amount;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add3__DOT__u_result;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add3__DOT__round_flag;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__run_latched;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__start_passthrough_2;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__start_passthrough_3;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__run;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add_sign_shifted_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add_sign_not_shifted_in;
        CData/*4:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add_exp_max_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add_sign_out;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add_sign_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add_carry_out;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add_carry_in;
        CData/*4:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add_exp_max_s3_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add1__DOT__cmp_out;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add1__DOT__diff;
        CData/*4:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add3__DOT__shifted_amount;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add3__DOT__ovf;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add3__DOT__unf;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add3__DOT__u_exp1;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add3__DOT__u_shifted_amount;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add3__DOT__u_result;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add3__DOT__round_flag;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__run_latched;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__start_passthrough_2;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__start_passthrough_3;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__run;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add_sign_shifted_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add_sign_not_shifted_in;
        CData/*4:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add_exp_max_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add_sign_out;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add_sign_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add_carry_out;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add_carry_in;
        CData/*4:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add_exp_max_s3_in;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add1__DOT__cmp_out;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add1__DOT__diff;
        CData/*4:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add3__DOT__shifted_amount;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add3__DOT__ovf;
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add3__DOT__unf;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add3__DOT__u_exp1;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add3__DOT__u_shifted_amount;
        CData/*5:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add3__DOT__u_result;
    };
    struct {
        CData/*0:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add3__DOT__round_flag;
        CData/*0:0*/ __VdlySet__systolic_array_tb__DOT__DUT__DOT__weights__v0;
        CData/*0:0*/ __VdlySet__systolic_array_tb__DOT__DUT__DOT__weights__v1;
        CData/*0:0*/ __VdlySet__systolic_array_tb__DOT__DUT__DOT__weights__v2;
        CData/*0:0*/ __VdlySet__systolic_array_tb__DOT__DUT__DOT__weights__v3;
        CData/*0:0*/ __VdlySet__systolic_array_tb__DOT__DUT__DOT__weights__v4;
        CData/*0:0*/ __VdlySet__systolic_array_tb__DOT__DUT__DOT__weights__v5;
        CData/*0:0*/ __VdlySet__systolic_array_tb__DOT__DUT__DOT__weights__v6;
        CData/*0:0*/ __VdlySet__systolic_array_tb__DOT__DUT__DOT__weights__v7;
        CData/*0:0*/ __VdlySet__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v0;
        CData/*0:0*/ __VdlySet__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v16;
        CData/*0:0*/ __VstlFirstIteration;
        CData/*0:0*/ __Vtrigprevexpr___TOP__systolic_array_tb__DOT__tb_clk__0;
        CData/*0:0*/ __Vtrigprevexpr___TOP__systolic_array_tb__DOT__tb_nRST__0;
        CData/*0:0*/ __VactContinue;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__frac_shifted_in;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__frac_not_shifted_in;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add_sum_in;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add2__DOT__frac1_signed;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add2__DOT__frac2_signed;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add2__DOT__sum_signed;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add2__DOT__change_to_unsigned__DOT__rfrac_signed;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add3__DOT__shifted_frac;
        SData/*11:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add3__DOT__round_this;
        SData/*11:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add3__DOT__rounded_fraction;
        SData/*14:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__0__KET____DOT__add_inst__DOT__add3__DOT____VdfgRegularize_h54187199_0_0;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__frac_shifted_in;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__frac_not_shifted_in;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add_sum_in;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add2__DOT__frac1_signed;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add2__DOT__frac2_signed;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add2__DOT__sum_signed;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add2__DOT__change_to_unsigned__DOT__rfrac_signed;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add3__DOT__shifted_frac;
        SData/*11:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add3__DOT__round_this;
        SData/*11:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add3__DOT__rounded_fraction;
        SData/*14:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__1__KET____DOT__add_inst__DOT__add3__DOT____VdfgRegularize_h54187199_0_0;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__frac_shifted_in;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__frac_not_shifted_in;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add_sum_in;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add2__DOT__frac1_signed;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add2__DOT__frac2_signed;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add2__DOT__sum_signed;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add2__DOT__change_to_unsigned__DOT__rfrac_signed;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add3__DOT__shifted_frac;
        SData/*11:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add3__DOT__round_this;
        SData/*11:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add3__DOT__rounded_fraction;
        SData/*14:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__2__KET____DOT__add_inst__DOT__add3__DOT____VdfgRegularize_h54187199_0_0;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__frac_shifted_in;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__frac_not_shifted_in;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add_sum_in;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add2__DOT__frac1_signed;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add2__DOT__frac2_signed;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add2__DOT__sum_signed;
        SData/*13:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add2__DOT__change_to_unsigned__DOT__rfrac_signed;
        SData/*12:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add3__DOT__shifted_frac;
        SData/*11:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add3__DOT__round_this;
        SData/*11:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add3__DOT__rounded_fraction;
        SData/*14:0*/ systolic_array_tb__DOT__DUT__DOT__genblk5__BRA__3__KET____DOT__add_inst__DOT__add3__DOT____VdfgRegularize_h54187199_0_0;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v0;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v1;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v2;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v3;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v4;
    };
    struct {
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v5;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v6;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v7;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v8;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v9;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v10;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v11;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v12;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v13;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v14;
        SData/*15:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__MAC_outputs__v15;
        IData/*31:0*/ systolic_array_tb__DOT__out_file;
        IData/*31:0*/ systolic_array_tb__DOT__file;
        IData/*31:0*/ systolic_array_tb__DOT__k;
        IData/*31:0*/ systolic_array_tb__DOT__i;
        IData/*31:0*/ systolic_array_tb__DOT__j;
        IData/*31:0*/ systolic_array_tb__DOT__z;
        IData/*31:0*/ systolic_array_tb__DOT__y;
        IData/*31:0*/ systolic_array_tb__DOT__r;
        IData/*31:0*/ systolic_array_tb__DOT__in;
        IData/*31:0*/ systolic_array_tb__DOT__which;
        IData/*31:0*/ systolic_array_tb__DOT__loaded_weights;
        IData/*31:0*/ systolic_array_tb__DOT__get_matrices__Vstatic__unnamedblk1__DOT__iterations;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__z;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__y;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__i;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__j;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__l;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__m;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__n;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__0__KET____DOT__i_fifo__DOT__fifo_mem;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__0__KET____DOT__i_fifo__DOT__fifo_mem_nxt;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__0__KET____DOT__i_fifo__DOT__i;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__1__KET____DOT__i_fifo__DOT__fifo_mem;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__1__KET____DOT__i_fifo__DOT__fifo_mem_nxt;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__1__KET____DOT__i_fifo__DOT__i;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__2__KET____DOT__i_fifo__DOT__fifo_mem;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__2__KET____DOT__i_fifo__DOT__fifo_mem_nxt;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__2__KET____DOT__i_fifo__DOT__i;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__3__KET____DOT__i_fifo__DOT__fifo_mem;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__3__KET____DOT__i_fifo__DOT__fifo_mem_nxt;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__genblk2__BRA__3__KET____DOT__i_fifo__DOT__i;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__0__KET____DOT__ps_fifos__DOT__fifo_mem;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__0__KET____DOT__ps_fifos__DOT__fifo_mem_nxt;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__0__KET____DOT__ps_fifos__DOT__i;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__1__KET____DOT__ps_fifos__DOT__fifo_mem;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__1__KET____DOT__ps_fifos__DOT__fifo_mem_nxt;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__1__KET____DOT__ps_fifos__DOT__i;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__2__KET____DOT__ps_fifos__DOT__fifo_mem;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__2__KET____DOT__ps_fifos__DOT__fifo_mem_nxt;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__2__KET____DOT__ps_fifos__DOT__i;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__3__KET____DOT__ps_fifos__DOT__fifo_mem;
        VlWide<4>/*127:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__3__KET____DOT__ps_fifos__DOT__fifo_mem_nxt;
        IData/*31:0*/ systolic_array_tb__DOT__DUT__DOT__genblk3__BRA__3__KET____DOT__ps_fifos__DOT__i;
        IData/*31:0*/ __VactIterCount;
        QData/*63:0*/ systolic_array_tb__DOT__DUT__DOT__top_input;
        QData/*63:0*/ systolic_array_tb__DOT__DUT__DOT__weights_input;
        VlWide<8>/*255:0*/ systolic_array_tb__DOT__DUT__DOT__current_out;
        QData/*63:0*/ systolic_array_tb__DOT__DUT__DOT__genblk6__BRA__0__KET____DOT__o_fifo__DOT__fifo_mem;
        QData/*63:0*/ systolic_array_tb__DOT__DUT__DOT__genblk6__BRA__0__KET____DOT__o_fifo__DOT__fifo_mem_next;
        QData/*63:0*/ systolic_array_tb__DOT__DUT__DOT__genblk6__BRA__1__KET____DOT__o_fifo__DOT__fifo_mem;
        QData/*63:0*/ systolic_array_tb__DOT__DUT__DOT__genblk6__BRA__1__KET____DOT__o_fifo__DOT__fifo_mem_next;
        QData/*63:0*/ systolic_array_tb__DOT__DUT__DOT__genblk6__BRA__2__KET____DOT__o_fifo__DOT__fifo_mem;
        QData/*63:0*/ systolic_array_tb__DOT__DUT__DOT__genblk6__BRA__2__KET____DOT__o_fifo__DOT__fifo_mem_next;
    };
    struct {
        QData/*63:0*/ systolic_array_tb__DOT__DUT__DOT__genblk6__BRA__3__KET____DOT__o_fifo__DOT__fifo_mem;
        QData/*63:0*/ systolic_array_tb__DOT__DUT__DOT__genblk6__BRA__3__KET____DOT__o_fifo__DOT__fifo_mem_next;
        QData/*63:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__weights__v0;
        QData/*63:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__weights__v2;
        QData/*63:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__weights__v4;
        QData/*63:0*/ __VdlyVal__systolic_array_tb__DOT__DUT__DOT__weights__v6;
        VlUnpacked<VlUnpacked<SData/*15:0*/, 4>, 4> systolic_array_tb__DOT__temp_weights;
        VlUnpacked<VlUnpacked<SData/*15:0*/, 4>, 4> systolic_array_tb__DOT__temp_inputs;
        VlUnpacked<VlUnpacked<SData/*15:0*/, 4>, 4> systolic_array_tb__DOT__temp_partials;
        VlUnpacked<VlUnpacked<SData/*15:0*/, 4>, 4> systolic_array_tb__DOT__temp_outputs;
        VlUnpacked<QData/*63:0*/, 4> systolic_array_tb__DOT__m_weights;
        VlUnpacked<QData/*63:0*/, 4> systolic_array_tb__DOT__m_inputs;
        VlUnpacked<QData/*63:0*/, 4> systolic_array_tb__DOT__m_partials;
        VlUnpacked<QData/*63:0*/, 4> systolic_array_tb__DOT__m_outputs;
        VlUnpacked<VlUnpacked<SData/*15:0*/, 4>, 4> systolic_array_tb__DOT__DUT__DOT__MAC_inputs;
        VlUnpacked<VlUnpacked<SData/*15:0*/, 4>, 4> systolic_array_tb__DOT__DUT__DOT__MAC_outputs;
        VlUnpacked<VlUnpacked<SData/*15:0*/, 4>, 4> systolic_array_tb__DOT__DUT__DOT__nxt_MAC_outputs;
        VlUnpacked<SData/*15:0*/, 4> systolic_array_tb__DOT__DUT__DOT__ps_add_inputs;
        VlUnpacked<QData/*63:0*/, 4> systolic_array_tb__DOT__DUT__DOT__weights;
        VlUnpacked<CData/*3:0*/, 3> systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__iteration;
        VlUnpacked<CData/*3:0*/, 3> systolic_array_tb__DOT__DUT__DOT__cu_inst__DOT__nxt_iteration;
        VlUnpacked<CData/*0:0*/, 9> __Vm_traceActivity;
    };
    std::string systolic_array_tb__DOT__line;
    VlDelayScheduler __VdlySched;
    VlTriggerScheduler __VtrigSched_h8059f569__0;
    VlTriggerScheduler __VtrigSched_h8059f538__0;
    VlTriggerVec<1> __VstlTriggered;
    VlTriggerVec<4> __VactTriggered;
    VlTriggerVec<4> __VnbaTriggered;

    // INTERNAL VARIABLES
    Vsystolic_array_tb__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vsystolic_array_tb___024root(Vsystolic_array_tb__Syms* symsp, const char* v__name);
    ~Vsystolic_array_tb___024root();
    VL_UNCOPYABLE(Vsystolic_array_tb___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
