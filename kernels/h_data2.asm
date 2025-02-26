org 0x0000
li x10, 0x11

add x10, x10, x10
nop
add x11, x10, x0
sw x11, 0(x0)
halt