org 0x0000
li x10, 0xFFFF

beq x0, x0, jump
sw x10, 200(x0)
sw x10, 400(x0)
sw x10, 600(x0)
nop

jump:

halt