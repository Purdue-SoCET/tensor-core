// verilator -f verilator.f 
//--lint-only for warnings
//--binary to create the binary then run with ./obj_dir/V<filename>
--top-module systolic_array_tb
src/modules/systolic_array.sv
src/modules/sysarr_control_unit.sv
src/modules/sysarr_MAC.sv
src/modules/sysarr_add.sv
src/modules/sysarr_FIFO.sv
src/modules/sysarr_PS_FIFO.sv
src/modules/sysarr_OUT_FIFO.sv
src/testbench/systolic_array_tb.sv
+incdir+src/include/
--timing
//strict warnings
--Wall
--assert
-Wno-TIMESCALEMOD
-Wno-BLKSEQ
//waves
--trace
--trace-fst
// Optional: Enables tracing of structs
// --trace-structs
// Optional: Allows tracing of large arrays
// --trace-max-array 1024  
// Optional: Enables tracing signals with underscores in names
--trace-underscore  



