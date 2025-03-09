org 0x0000
li $10, 0xFFFF

beq $0, $0, jump
sw $10, 200($0)
sw $10, 400($0)
sw $10, 600($0)
nop

jump:

halt