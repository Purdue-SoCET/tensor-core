#----------------------------------------------------------
# RISC-V Assembly
#----------------------------------------------------------
#--------------------------------------
# Test with a fibonacci sequence
#--------------------------------------
  org 0x0000

  ori   $10, $10, start
   ori   $4, $4, 1
   ori   $5, $5, 4
   lui   $28, 0xFFFFF
   ori   $14, $14, 0xF00
   sub $14, $14, $28
   lw    $16, 0($14)
 
loop:
  lw    $11, 0 ($10)
   lw    $12, 4 ($10)
   add  $13, $11, $12
   sw    $13, 8 ($10)
   add  $10, $10, $5
   sub  $16, $16, $4
   bne   $16, $0, loop
 end:
  halt

  org 0x80

start:
  cfw 0
  cfw 1

#uncomment to work with the simulator (sim)
# comment to use mmio

  org 0x0F00
  cfw 22