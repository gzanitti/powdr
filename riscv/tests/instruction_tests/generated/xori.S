# 0 "sources/xori.S"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 0 "<command-line>" 2
# 1 "sources/xori.S"
# See LICENSE for license details.

#*****************************************************************************
# xori.S
#-----------------------------------------------------------------------------

# Test xori instruction.


# 1 "sources/riscv_test.h" 1
# 11 "sources/xori.S" 2
# 1 "sources/test_macros.h" 1






#-----------------------------------------------------------------------
# Helper macros
#-----------------------------------------------------------------------
# 20 "sources/test_macros.h"
# We use a macro hack to simpify code generation for various numbers
# of bubble cycles.
# 36 "sources/test_macros.h"
#-----------------------------------------------------------------------
# RV64UI MACROS
#-----------------------------------------------------------------------

#-----------------------------------------------------------------------
# Tests for instructions with immediate operand
#-----------------------------------------------------------------------
# 92 "sources/test_macros.h"
#-----------------------------------------------------------------------
# Tests for vector config instructions
#-----------------------------------------------------------------------
# 120 "sources/test_macros.h"
#-----------------------------------------------------------------------
# Tests for an instruction with register operands
#-----------------------------------------------------------------------
# 148 "sources/test_macros.h"
#-----------------------------------------------------------------------
# Tests for an instruction with register-register operands
#-----------------------------------------------------------------------
# 242 "sources/test_macros.h"
#-----------------------------------------------------------------------
# Test memory instructions
#-----------------------------------------------------------------------
# 319 "sources/test_macros.h"
#-----------------------------------------------------------------------
# Test branch instructions
#-----------------------------------------------------------------------
# 404 "sources/test_macros.h"
#-----------------------------------------------------------------------
# Test jump instructions
#-----------------------------------------------------------------------
# 433 "sources/test_macros.h"
#-----------------------------------------------------------------------
# RV64UF MACROS
#-----------------------------------------------------------------------

#-----------------------------------------------------------------------
# Tests floating-point instructions
#-----------------------------------------------------------------------
# 569 "sources/test_macros.h"
#-----------------------------------------------------------------------
# Pass and fail code (assumes test num is in x28)
#-----------------------------------------------------------------------
# 581 "sources/test_macros.h"
#-----------------------------------------------------------------------
# Test data section
#-----------------------------------------------------------------------
# 12 "sources/xori.S" 2


.globl _start; .globl __runtime_start; _start: __runtime_start: la x10,__return_pointer; sw x1,0(x10); li x10,0

  #-------------------------------------------------------------
  # Logical tests
  #-------------------------------------------------------------

  test_2: li x10, 2; ebreak; li x1, 0x0000000000ff0f00; xori x3, x1, ((0xf0f) | (-(((0xf0f) >> 11) & 1) << 11));; li x29, 0xffffffffff00f00f; li x28, 2; bne x3, x29, fail;;
  test_3: li x10, 3; ebreak; li x1, 0x000000000ff00ff0; xori x3, x1, ((0x0f0) | (-(((0x0f0) >> 11) & 1) << 11));; li x29, 0x000000000ff00f00; li x28, 3; bne x3, x29, fail;;
  test_4: li x10, 4; ebreak; li x1, 0x0000000000ff08ff; xori x3, x1, ((0x70f) | (-(((0x70f) >> 11) & 1) << 11));; li x29, 0x0000000000ff0ff0; li x28, 4; bne x3, x29, fail;;
  test_5: li x10, 5; ebreak; li x1, 0xfffffffff00ff00f; xori x3, x1, ((0x0f0) | (-(((0x0f0) >> 11) & 1) << 11));; li x29, 0xfffffffff00ff0ff; li x28, 5; bne x3, x29, fail;;

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  test_6: li x10, 6; ebreak; li x1, 0xffffffffff00f700; xori x1, x1, ((0x70f) | (-(((0x70f) >> 11) & 1) << 11));; li x29, 0xffffffffff00f00f; li x28, 6; bne x1, x29, fail;;

   #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  test_7: li x10, 7; ebreak; li x4, 0; test_7_l1: li x1, 0x000000000ff00ff0; xori x3, x1, ((0x0f0) | (-(((0x0f0) >> 11) & 1) << 11)); addi x6, x3, 0; addi x4, x4, 1; li x5, 2; bne x4, x5, test_7_l1; li x29, 0x000000000ff00f00; li x28, 7; bne x6, x29, fail;;
  test_8: li x10, 8; ebreak; li x4, 0; test_8_l1: li x1, 0x0000000000ff08ff; xori x3, x1, ((0x70f) | (-(((0x70f) >> 11) & 1) << 11)); nop; addi x6, x3, 0; addi x4, x4, 1; li x5, 2; bne x4, x5, test_8_l1; li x29, 0x0000000000ff0ff0; li x28, 8; bne x6, x29, fail;;
  test_9: li x10, 9; ebreak; li x4, 0; test_9_l1: li x1, 0xfffffffff00ff00f; xori x3, x1, ((0x0f0) | (-(((0x0f0) >> 11) & 1) << 11)); nop; nop; addi x6, x3, 0; addi x4, x4, 1; li x5, 2; bne x4, x5, test_9_l1; li x29, 0xfffffffff00ff0ff; li x28, 9; bne x6, x29, fail;;

  test_10: li x10, 10; ebreak; li x4, 0; test_10_l1: li x1, 0x000000000ff00ff0; xori x3, x1, ((0x0f0) | (-(((0x0f0) >> 11) & 1) << 11)); addi x4, x4, 1; li x5, 2; bne x4, x5, test_10_l1; li x29, 0x000000000ff00f00; li x28, 10; bne x3, x29, fail;;
  test_11: li x10, 11; ebreak; li x4, 0; test_11_l1: li x1, 0x0000000000ff0fff; nop; xori x3, x1, ((0x00f) | (-(((0x00f) >> 11) & 1) << 11)); addi x4, x4, 1; li x5, 2; bne x4, x5, test_11_l1; li x29, 0x0000000000ff0ff0; li x28, 11; bne x3, x29, fail;;
  test_12: li x10, 12; ebreak; li x4, 0; test_12_l1: li x1, 0xfffffffff00ff00f; nop; nop; xori x3, x1, ((0x0f0) | (-(((0x0f0) >> 11) & 1) << 11)); addi x4, x4, 1; li x5, 2; bne x4, x5, test_12_l1; li x29, 0xfffffffff00ff0ff; li x28, 12; bne x3, x29, fail;;

  test_13: li x10, 13; ebreak; xori x1, x0, ((0x0f0) | (-(((0x0f0) >> 11) & 1) << 11));; li x29, 0x0f0; li x28, 13; bne x1, x29, fail;;
  test_14: li x10, 14; ebreak; li x1, 0x00ff00ff; xori x0, x1, ((0x70f) | (-(((0x70f) >> 11) & 1) << 11));; li x29, 0; li x28, 14; bne x0, x29, fail;;

  bne x0, x28, pass; fail: unimp;; pass: la x10,__return_pointer; lw x1,0(x10); ret;



  .data
.balign 4; __return_pointer: .word 0;

 


