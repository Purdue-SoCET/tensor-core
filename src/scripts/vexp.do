onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix binary /vexp_tb/dut/CLK
add wave -noupdate -radix binary /vexp_tb/dut/nRST
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/ONE
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/ONE_SIXTH
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul1_start
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul1_done
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul1_a
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul1_b
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul1_out
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul2_start
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul2_done
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul2_a
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul2_b
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul2_out
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul3_start
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul3_done
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul3_a
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul3_b
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul3_out
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul4_start
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul4_done
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul4_a
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul4_b
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/mul4_out
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/r_bits
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/s1_sum_comb
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/s1_sum_q
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/s1_r2_q
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/s1_v_q
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/r2_over_2
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/s2_sum_comb
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/s2_sum_q
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/s2_r3_q
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/s2_v_q
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/s3_sum_comb
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/s3_sum_q
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/s3_v_q
add wave -noupdate -expand -group {VExp Internal Signals} -color Yellow -radix binary /vexp_tb/dut/poweroftwo
add wave -noupdate -color Yellow -radix binary /vexp_tb/dut/fp1
add wave -noupdate -expand -group {VExp Signals} -color Cyan -radix binary /vexp_tb/vexpif/port_a
add wave -noupdate -expand -group {VExp Signals} -color Cyan -radix binary /vexp_tb/vexpif/out
add wave -noupdate -expand -group {VExp Signals} -color Cyan /vexp_tb/vexpif/enable
add wave -noupdate -expand -group {TB Signals} -color Magenta /vexp_tb/FP16_P0
add wave -noupdate -expand -group {TB Signals} -color Magenta /vexp_tb/FP16_N0
add wave -noupdate -expand -group {TB Signals} -color Magenta /vexp_tb/FP16_ONE
add wave -noupdate -expand -group {TB Signals} -color Magenta /vexp_tb/FP16_NEG1
add wave -noupdate -expand -group {TB Signals} -color Magenta /vexp_tb/FP16_TWO
add wave -noupdate -expand -group {TB Signals} -color Magenta /vexp_tb/FP16_HALF
add wave -noupdate -expand -group {TB Signals} -color Magenta /vexp_tb/FP16_PINF
add wave -noupdate -expand -group {TB Signals} -color Magenta /vexp_tb/FP16_NINF
add wave -noupdate -expand -group {TB Signals} -color Magenta /vexp_tb/FP16_QNAN
add wave -noupdate -expand -group {TB Signals} -color Magenta -radix decimal /vexp_tb/casenum
add wave -noupdate -expand -group {TB Signals} -color Magenta /vexp_tb/casename
add wave -noupdate -expand -group {VAS 1} /vexp_tb/dut/vaddsubif1/port_a
add wave -noupdate -expand -group {VAS 1} /vexp_tb/dut/vaddsubif1/port_b
add wave -noupdate -expand -group {VAS 1} /vexp_tb/dut/vaddsubif1/out
add wave -noupdate -expand -group {VAS 1} /vexp_tb/dut/vaddsubif1/sub
add wave -noupdate -expand -group {VAS 1} /vexp_tb/dut/vaddsubif1/enable
add wave -noupdate -expand -group {VAS 1} /vexp_tb/dut/vaddsubif1/overflow
add wave -noupdate -expand -group {VAS 2} /vexp_tb/dut/vaddsubif2/port_a
add wave -noupdate -expand -group {VAS 2} /vexp_tb/dut/vaddsubif2/port_b
add wave -noupdate -expand -group {VAS 2} /vexp_tb/dut/vaddsubif2/out
add wave -noupdate -expand -group {VAS 2} /vexp_tb/dut/vaddsubif2/sub
add wave -noupdate -expand -group {VAS 2} /vexp_tb/dut/vaddsubif2/enable
add wave -noupdate -expand -group {VAS 2} /vexp_tb/dut/vaddsubif2/overflow
add wave -noupdate -expand -group {VAS 3} /vexp_tb/dut/vaddsubif3/port_a
add wave -noupdate -expand -group {VAS 3} /vexp_tb/dut/vaddsubif3/port_b
add wave -noupdate -expand -group {VAS 3} /vexp_tb/dut/vaddsubif3/out
add wave -noupdate -expand -group {VAS 3} /vexp_tb/dut/vaddsubif3/sub
add wave -noupdate -expand -group {VAS 3} /vexp_tb/dut/vaddsubif3/enable
add wave -noupdate -expand -group {VAS 3} /vexp_tb/dut/vaddsubif3/overflow
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {196743 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {39800 ps} {324600 ps}
