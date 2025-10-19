#----------------------------------------------------------
# RISC-V Assembly
#----------------------------------------------------------
#--------------------------------------
# Test a search algorithm
#--------------------------------------
  org   0x0000
  ori   $2, $0, 0x80
 start:
  ori   $4, $0, 0x01
   ori   $10, $0, 0x04
 
  sw    $0, 0($2)            # set result to 0
   lw    $11, 4($2)            # load search variable into $11
   lw    $12, 8($2)            # load search length into $12
   addi $13, $2, 12           # search pointer is in $13
 
loop:
  lw    $14, 0($13)             # load element at pointer $13
   sub  $15, $14, $11            # compare loaded element with search var
   beq   $15, $0, found      # if matches, go to found
   add  $13, $13, $10            # increment pointer
   sub  $12, $12, $4            # subutract search length
   beq   $12, $0, notfound   # if end of list, go to not found
   beq   $0, $0, loop       # do loop again
 found:
  sw    $13, 0($2)            # store into 0x80
 notfound:
  halt


  org 0x80
item_position:
  cfw 0                       # should be found at 0x0124
search_item:
  cfw 0x5c6f
list_length:
  cfw 100
search_list:
  cfw 0x087d
  cfw 0x5fcb
  cfw 0xa41a
  cfw 0x4109
  cfw 0x4522
  cfw 0x700f
  cfw 0x766d
  cfw 0x6f60
  cfw 0x8a5e
  cfw 0x9580
  cfw 0x70a3
  cfw 0xaea9
  cfw 0x711a
  cfw 0x6f81
  cfw 0x8f9a
  cfw 0x2584
  cfw 0xa599
  cfw 0x4015
  cfw 0xce81
  cfw 0xf55b
  cfw 0x399e
  cfw 0xa23f
  cfw 0x3588
  cfw 0x33ac
  cfw 0xbce7
  cfw 0x2a6b
  cfw 0x9fa1
  cfw 0xc94b
  cfw 0xc65b
  cfw 0x0068
  cfw 0xf499
  cfw 0x5f71
  cfw 0xd06f
  cfw 0x14df
  cfw 0x1165
  cfw 0xf88d
  cfw 0x4ba4
  cfw 0x2e74
  cfw 0x5c6f
  cfw 0xd11e
  cfw 0x9222
  cfw 0xacdb
  cfw 0x1038
  cfw 0xab17
  cfw 0xf7ce
  cfw 0x8a9e
  cfw 0x9aa3
  cfw 0xb495
  cfw 0x8a5e
  cfw 0xd859
  cfw 0x0bac
  cfw 0xd0db
  cfw 0x3552
  cfw 0xa6b0
  cfw 0x727f
  cfw 0x28e4
  cfw 0xe5cf
  cfw 0x163c
  cfw 0x3411
  cfw 0x8f07
  cfw 0xfab7
  cfw 0x0f34
  cfw 0xdabf
  cfw 0x6f6f
  cfw 0xc598
  cfw 0xf496
  cfw 0x9a9a
  cfw 0xbd6a
  cfw 0x2136
  cfw 0x810a
  cfw 0xca55
  cfw 0x8bce
  cfw 0x2ac4
  cfw 0xddce
  cfw 0xdd06
  cfw 0xc4fc
  cfw 0xfb2f
  cfw 0xee5f
  cfw 0xfd30
  cfw 0xc540
  cfw 0xd5f1
  cfw 0xbdad
  cfw 0x45c3
  cfw 0x708a
  cfw 0xa359
  cfw 0xf40d
  cfw 0xba06
  cfw 0xbace
  cfw 0xb447
  cfw 0x3f48
  cfw 0x899e
  cfw 0x8084
  cfw 0xbdb9
  cfw 0xa05a
  cfw 0xe225
  cfw 0xfb0c
  cfw 0xb2b2
  cfw 0xa4db
  cfw 0x8bf9
  cfw 0x12f7