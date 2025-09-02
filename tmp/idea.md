### SCPAD Insts.

**scpad.load/scpad.store:**

```
[63:56] = opcode telling scpad stuff                         (8)
[55:52] = opcode telling load or store                       (4)
[51]     which scpad, 1 or 2?                                (1)
[50]     swizzling on or off?                                (1)
[49]     EMPTY                                               (1)
[48:44]  tma config record id -> stride, row, col, etc.      (5)
[43:40]  qid -> say in the future, we want QoS or some
         policy basic scheduling of loads                    (4)
[39]     EMPTY                                               (1)
[38:27]  num of elements to copy -> max is 1024 fp16
         per 2KB page                                        (12)
[26:21]  GPR with dram base                                  (6)
[20:14]  GPR with scpad base                                 (7)
[13:0]   EMPTY                                               (14)
                                                     ----
                                                     = 64 bits
```

**Would QID be useful? Maybe.**

* Let’s assign priority queues for the scpad contrller to choose from.
* The scheduler chooses the highest priority entry to load.
* Maybe this QoS stuff gets useful when we have signals coming from different units telling us that they're busy with something.
* Then, we can switch over to the next priority item. So, only once we are done completely with something, we remove an item from the queue.
* Maybe fencing?? Fence on each QID.

---

### VC Instrs.

**vreg.load/vreg.store:**

```
[63:56] opcode telling vector stuff                          (8)
[55:52] opcode telling load store                            (4)
[51]     which scratchpad                                    (1)
[50]     swizzling?                                          (1)
[49:45]  vector destination (for load) / source (for store)  (5)
[44:40]  EMPTY                                               (5)
[39:24]  num_elements to move                                (16)
[23:19]  GPR with SPAD base                                  (5)
[18:14]  EMPTY                                               (5)
[13:0]   offset from the base -> for subtiles                (14)
                                                     ----
                                                     = 64 bits
```

* Vector→vector when `reduce=0`; reductions write the scalar into `vdst[0]`.

---

### Systolic Array Instrs.

**sysarray.GEMM**

```
[63:56] opcode telling vector stuff                          (8)
[55:52] opcode telling GEMM                                  (4)
[51]     spA which scpad                                     (1)
[50]     spB   which scpad                                   (1)
[49]     spC which scpad to put outputs                      (1)
[48]     swzA  - swizzling read out                          (1)
[47]     swzB - swizzling read out                           (1)
[46:37]  M                                                   (10)
[36:27]  N                                                   (10)
[26:17]  K                                                   (10)
[16:12]  GPR with Scpad base byte - A                        (5)
[11:7]   GPRs with Scpad base byte - B                       (5)
[6:2]    GPR with Scpad base byte - C - for putting output   (5)
[1]      acc_en - put into buffer, or transfer into scpad
         directly                                            (1)
[0]      EMPTY                                               (1)
                                                     ----
                                                     = 64 bits
```

**sysarray.CONV**

```
[63:56] opcode telling sys array stuff                       (8)
[55:52] opcode telling conv                                  (4)
[51]     spX   -> which scpad                                (1)
[50]     spW                                                 (1)
[49]     spY                                                 (1)
[48]     swzX   -> to swizzle or not to                      (1)
[47]     swzW                                                (1)
[46:42]  sys_desc_id  conv config shit -- N,C,H,W, K, R,S,
         stride, pad, dil                                    (5)
[41:37]  rX_spad_base                                        (5)
[36:32]  rW_spad_base                                        (5)
[31:27]  rY_spad_base                                        (5)
[26]     acc_en - put into buffer, or transfer into scpad
         directly                                            (1)
[25:0]   EMPTY                                               (26)
                                                     ----
                                                     = 64 bits
```

**sysarray.store**

```
[63:56] opcode telling sysarray                              (8)
[55:52] opcode telling store from output buffer into Spcad   (4)
[51]     spC - which scpad to write output                   (1)
[50]     out_swz - swizzling while putting back              (1)
[49:45]  EMPTY                                               (5)
[44:40]  EMPTY                                               (5)
[39:24]  len_elems - num elements                            (16)
[23:19]  rC_spad_base - offset within scpad                  (5)
[18:14]  EMPTY                                               (5)
[13:0]   spad_off_C - write to a specific subtile within
         the base                                            (14)
                                                     ----
                                                     = 64 bits
```

---

### SCPAD transfer descriptor units


## `scpad.tdesc` (generic SPAD tile/stream descriptor — rows/cols/stride/etc.)

```
[31:24] row_elements      (8)  -- number of FP16 elements per logical row (0..255)
[23:16] col_elements      (8)  -- number of FP16 elements per logical column (0..255)
[15:8]  stride_elements   (8)  -- row  in FP16 elements (0..255). If 0, treat as row_elements.
[7]     swizzle           (1)  -- 0=row-wise, 1=column-wise (selects SPAD read/write mode)
[6:5]   elem_type         (2)  -- 00=fp16, 01=reserved, 10=reserved, 11=reserved
[4:2]   qid               (3)  -- queue id for QoS/fencing (0..7)
[1:0]   pad_elems         (2)  -- end-of-row padding in FP16 elems (0..3)
--------------------------------
= 32 bits total
```

---

## `systolic.cdesc` (convolution tile descriptor — N,C,H,W,Kf,R,S,stride,pad)

```
[31:27] C     (5)  -- input channels   (1..32 encoded as 0..31)
[26:22] H     (5)  -- input height     (1..32 encoded as 0..31)
[21:17] W     (5)  -- input width      (1..32 encoded as 0..31)
[16:12] Kf    (5)  -- output channels  (1..32 encoded as 0..31)
[11:9]  R     (3)  -- kernel height    (1..8  encoded as 0..7)
[8:6]   S     (3)  -- kernel width     (1..8  encoded as 0..7)
[5:4]   N     (2)  -- batch size       (1..4  encoded as 0..3)
[3:2]   stride(2)  -- conv stride      (1..4  encoded as 0..3)
[1:0]   pad   (2)  -- symmetric pad    (0..3 pixels)
--------------------------------
= 32 bits total
```
