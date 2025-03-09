org 0x0000
li $10, 0x11

add $10, $10, $10
nop
add $11, $10, $0
sw $11, 0($0)
halt