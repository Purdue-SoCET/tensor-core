#----------------------------------------------------------
# RISC-V Assembly
#----------------------------------------------------------
#--------------------------------------
# Test beq branch not taken
#--------------------------------------
org 0x0000

li $0, 1
li $6, 0xF # FAIL
li $7, 0xECE437 # PASS

beq $7, $0, beq_check
sw $7, 400($10)
j exit

beq_check:
 sw $6, 400($10)

exit:
halt