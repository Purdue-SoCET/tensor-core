org 0x0000
li x10, 0xFFF

lw x10, 0(x0)
addi x11, x10, 5
sw x11, 200(x0)

halt