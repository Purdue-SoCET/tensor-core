	.file	"mergesort.c"
	.option nopic
	.attribute arch, "rv32i2p1"
	.attribute unaligned_access, 0
	.attribute stack_align, 16
	.text
	.align	2
	.globl	merge
	.type	merge, @function
merge:
	addi	sp,sp,-464
	sw	s0,460(sp)
	addi	s0,sp,464
	sw	a0,-452(s0)
	sw	a1,-456(s0)
	sw	a2,-460(s0)
	sw	a3,-464(s0)
	lw	a4,-460(s0)
	lw	a5,-456(s0)
	sub	a5,a4,a5
	addi	a5,a5,1
	sw	a5,-32(s0)
	lw	a4,-464(s0)
	lw	a5,-460(s0)
	sub	a5,a4,a5
	sw	a5,-36(s0)
	sw	zero,-20(s0)
	j	.L2
.L3:
	lw	a4,-456(s0)
	lw	a5,-20(s0)
	add	a5,a4,a5
	slli	a5,a5,2
	lw	a4,-452(s0)
	add	a5,a4,a5
	lw	a4,0(a5)
	lw	a5,-20(s0)
	slli	a5,a5,2
	addi	a5,a5,-16
	add	a5,a5,s0
	sw	a4,-220(a5)
	lw	a5,-20(s0)
	addi	a5,a5,1
	sw	a5,-20(s0)
.L2:
	lw	a4,-20(s0)
	lw	a5,-32(s0)
	blt	a4,a5,.L3
	sw	zero,-24(s0)
	j	.L4
.L5:
	lw	a5,-460(s0)
	addi	a4,a5,1
	lw	a5,-24(s0)
	add	a5,a4,a5
	slli	a5,a5,2
	lw	a4,-452(s0)
	add	a5,a4,a5
	lw	a4,0(a5)
	lw	a5,-24(s0)
	slli	a5,a5,2
	addi	a5,a5,-16
	add	a5,a5,s0
	sw	a4,-420(a5)
	lw	a5,-24(s0)
	addi	a5,a5,1
	sw	a5,-24(s0)
.L4:
	lw	a4,-24(s0)
	lw	a5,-36(s0)
	blt	a4,a5,.L5
	sw	zero,-20(s0)
	sw	zero,-24(s0)
	lw	a5,-456(s0)
	sw	a5,-28(s0)
	j	.L6
.L9:
	lw	a5,-20(s0)
	slli	a5,a5,2
	addi	a5,a5,-16
	add	a5,a5,s0
	lw	a4,-220(a5)
	lw	a5,-24(s0)
	slli	a5,a5,2
	addi	a5,a5,-16
	add	a5,a5,s0
	lw	a5,-420(a5)
	bgt	a4,a5,.L7
	lw	a5,-20(s0)
	addi	a4,a5,1
	sw	a4,-20(s0)
	lw	a4,-28(s0)
	addi	a3,a4,1
	sw	a3,-28(s0)
	slli	a4,a4,2
	lw	a3,-452(s0)
	add	a4,a3,a4
	slli	a5,a5,2
	addi	a5,a5,-16
	add	a5,a5,s0
	lw	a5,-220(a5)
	sw	a5,0(a4)
	j	.L6
.L7:
	lw	a5,-24(s0)
	addi	a4,a5,1
	sw	a4,-24(s0)
	lw	a4,-28(s0)
	addi	a3,a4,1
	sw	a3,-28(s0)
	slli	a4,a4,2
	lw	a3,-452(s0)
	add	a4,a3,a4
	slli	a5,a5,2
	addi	a5,a5,-16
	add	a5,a5,s0
	lw	a5,-420(a5)
	sw	a5,0(a4)
.L6:
	lw	a4,-20(s0)
	lw	a5,-32(s0)
	bge	a4,a5,.L10
	lw	a4,-24(s0)
	lw	a5,-36(s0)
	blt	a4,a5,.L9
	j	.L10
.L11:
	lw	a5,-20(s0)
	addi	a4,a5,1
	sw	a4,-20(s0)
	lw	a4,-28(s0)
	addi	a3,a4,1
	sw	a3,-28(s0)
	slli	a4,a4,2
	lw	a3,-452(s0)
	add	a4,a3,a4
	slli	a5,a5,2
	addi	a5,a5,-16
	add	a5,a5,s0
	lw	a5,-220(a5)
	sw	a5,0(a4)
.L10:
	lw	a4,-20(s0)
	lw	a5,-32(s0)
	blt	a4,a5,.L11
	j	.L12
.L13:
	lw	a5,-24(s0)
	addi	a4,a5,1
	sw	a4,-24(s0)
	lw	a4,-28(s0)
	addi	a3,a4,1
	sw	a3,-28(s0)
	slli	a4,a4,2
	lw	a3,-452(s0)
	add	a4,a3,a4
	slli	a5,a5,2
	addi	a5,a5,-16
	add	a5,a5,s0
	lw	a5,-420(a5)
	sw	a5,0(a4)
.L12:
	lw	a4,-24(s0)
	lw	a5,-36(s0)
	blt	a4,a5,.L13
	nop
	nop
	lw	s0,460(sp)
	addi	sp,sp,464
	jr	ra
	.size	merge, .-merge
	.align	2
	.globl	mergesort
	.type	mergesort, @function
mergesort:
	addi	sp,sp,-48
	sw	ra,44(sp)
	sw	s0,40(sp)
	addi	s0,sp,48
	sw	a0,-36(s0)
	sw	a1,-40(s0)
	sw	a2,-44(s0)
	lw	a4,-40(s0)
	lw	a5,-44(s0)
	bge	a4,a5,.L16
	lw	a4,-44(s0)
	lw	a5,-40(s0)
	sub	a5,a4,a5
	srli	a4,a5,31
	add	a5,a4,a5
	srai	a5,a5,1
	mv	a4,a5
	lw	a5,-40(s0)
	add	a5,a5,a4
	sw	a5,-20(s0)
	lw	a2,-20(s0)
	lw	a1,-40(s0)
	lw	a0,-36(s0)
	call	mergesort
	lw	a5,-20(s0)
	addi	a5,a5,1
	lw	a2,-44(s0)
	mv	a1,a5
	lw	a0,-36(s0)
	call	mergesort
	lw	a3,-44(s0)
	lw	a2,-20(s0)
	lw	a1,-40(s0)
	lw	a0,-36(s0)
	call	merge
.L16:
	nop
	lw	ra,44(sp)
	lw	s0,40(sp)
	addi	sp,sp,48
	jr	ra
	.size	mergesort, .-mergesort
	.ident	"GCC: (g) 13.2.0"
