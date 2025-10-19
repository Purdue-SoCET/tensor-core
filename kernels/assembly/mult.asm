mult:
  org 0x0000
  ori $2, $0, 0xFFFC
  ori $5, $0, 10
  ori $6, $0, 5
  ori $28, $0, 0
  push $5
  push $6

  pop $6
  pop $7

mult_loop:
  beq $6, $0, end
  add $28, $28, $7
  addi $6, $6, -1
  j mult_loop

end:
  sw $28, 0($10)
  push $28
  halt
        
