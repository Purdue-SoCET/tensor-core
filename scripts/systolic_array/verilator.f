// Verilator arguments for systolic array compilation

--binary
-j 0

-Irtl/modules/common/
-Irtl/modules/systolic_array
-Irtl/include/common
-Irtl/include/systolic_array
-Itb/unit/common
-Itb/unit/systolic_array

--hierarchical
--trace