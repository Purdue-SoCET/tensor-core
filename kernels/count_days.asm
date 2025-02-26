org 0x0000
ori   $2, $0, 0xFFFC

li $28, 1
li $29, 2
li $30, 2001

push $28
push $29
push $30

pop $30

addi $30, $30, -2000
push $30

li $27, 365
push $27
jal $1, multiply

pop $31
pop $30
addi $30, $30, -1
li $27, 30
push $27
push $30
jal $1, multiply
pop $30
add $31, $30, $31

pop $28

add $21, $28, $31


j exit

multiply:
pop $18
pop $19

li $21, 0x0
li $20, 0x0

loop: 
 andi $20, $19, 1
 beq $20, $0, shift
 add $21, $21, $18
 shift:
  slli $18, $18, 1
  srli $19, $19, 1
  bnez $19, loop

  push $21
  ret

exit:
  halt