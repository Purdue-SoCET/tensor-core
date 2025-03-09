org 0x0000
li $10, 0xFFF

lw $10, 0($0)
addi $11, $10, 5
sw $11, 200($0)

halt