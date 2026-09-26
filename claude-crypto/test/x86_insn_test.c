// Differential test of the x86-64 instruction semantics of the Lean model
// (lean/ClaudeCrypto/X86/Basic.lean) against the real CPU.
//
// Every instruction form of the table below is executed on pseudo-random
// machine states.  For each test, a small assembly function (one per form):
//   * loads RFLAGS, all 16 general-purpose registers (including rsp), and, for
//     vector forms, all 16 ymm registers from g_fin / g_in / g_vin;
//   * executes the instruction;
//   * stores all of them back to g_fout / g_out / g_vout.
// Memory operands point into the 128-byte buffer g_buf (at random, mostly
// unaligned offsets, via random index registers and the form's displacement).
// One line is printed per test:
//   v <form> <rflags in> <16 GPRs in> <16 ymm in | -> <buffer in | -> <rflags out>
//     <changed GPRs as i=value,... | -> <changed ymm | -> <buffer out | ->
// (values in hex; the buffer and ymm registers as little-endian numbers, i.e.
// most significant byte first).  Header lines give the buffer address
// ("b <addr> <len>"), the assembly text of each form ("f <id> <text>") and CPU
// features that are missing ("nofeature <n> <name>"), whose forms are skipped.
// test/X86InsnCheck.lean recomputes every output with the model and compares.
//
// The form table is generated from the model: the assembly text of each form is
// the model printer's text for an `Instr` value (see X86InsnCheck.lean, whose
// `--gen` option prints the table), and the checker verifies this for every
// form, so the C table and the model cannot silently disagree.
//
//   gcc -O1 -static x86_insn_test.c -o x86_insn_test
//   [X86_INSN_FORCE_SHA=1] ./x86_insn_test [vectors-per-form [seed]] > vectors.txt
#include <cpuid.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BUFLEN 128

// Machine state in and out (referenced from the assembly by name).
uint64_t g_in[16], g_out[16], g_fin, g_fout, g_saved_rsp;
uint8_t g_vin[16 * 32] __attribute__((aligned(32)));
uint8_t g_vout[16 * 32] __attribute__((aligned(32)));
uint8_t g_buf[BUFLEN] __attribute__((aligned(64)));
uint64_t g_stack[64] __attribute__((aligned(16)));

// F(id, "text", vec, kind, base, index, scale, disp, size, feature, hasimm, imm):
//   vec: 1 = load/store the ymm registers too
//   kind: 0 = no memory access, 1 = memory operand [base + index*scale + disp]
//         (base -1: RIP-relative to g_buf), 2 = push, 3 = pop
//   size: bytes accessed; feature: 0 = baseline, 1 = SHA extensions
//   hasimm, imm: the (sign-extended) immediate operand of ALU forms; some
//   random vectors then give the registers values next to it
// BEGIN GENERATED FORMS (lake env lean --run ../test/X86InsnCheck.lean --gen)
#define FORMS(F) \
  F(0, "mov ebx, edx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(1, "mov r11d, r14d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(2, "mov ecx, r8d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(3, "mov ebx, ebx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(4, "mov ecx, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(5, "mov edx, -128", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(6, "mov ebx, -2147483648", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(7, "mov ebp, 1249150122", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(8, "mov esi, 65535", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(9, "mov edi, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(10, "mov ebx, DWORD PTR [rdi]", 0, 1, 7, -1, 1, 0LL, 4, 0, 0, 0LL) \
  F(11, "mov ebp, DWORD PTR [rsi+8]", 0, 1, 6, -1, 1, 8LL, 4, 0, 0, 0LL) \
  F(12, "mov esi, DWORD PTR [rsp+24]", 0, 1, 4, -1, 1, 24LL, 4, 0, 0, 0LL) \
  F(13, "mov edi, DWORD PTR [rip+g_buf+3]", 0, 1, -1, -1, 1, 3LL, 4, 0, 0, 0LL) \
  F(14, "mov r8d, DWORD PTR [rbp-16]", 0, 1, 5, -1, 1, -16LL, 4, 0, 0, 0LL) \
  F(15, "mov r9d, DWORD PTR [r13]", 0, 1, 13, -1, 1, 0LL, 4, 0, 0, 0LL) \
  F(16, "mov r10d, DWORD PTR [rdx+rcx*1]", 0, 1, 2, 1, 1, 0LL, 4, 0, 0, 0LL) \
  F(17, "mov r11d, DWORD PTR [r12+40]", 0, 1, 12, -1, 1, 40LL, 4, 0, 0, 0LL) \
  F(18, "mov r12d, DWORD PTR [rbx+r9*2+7]", 0, 1, 3, 9, 2, 7LL, 4, 0, 0, 0LL) \
  F(19, "mov r13d, DWORD PTR [r10+rbp*4-100]", 0, 1, 10, 5, 4, -100LL, 4, 0, 0, 0LL) \
  F(20, "mov r14d, DWORD PTR [rip+g_buf]", 0, 1, -1, -1, 1, 0LL, 4, 0, 0, 0LL) \
  F(21, "mov r15d, DWORD PTR [r15+r11*8+74565]", 0, 1, 15, 11, 8, 74565LL, 4, 0, 0, 0LL) \
  F(22, "mov eax, DWORD PTR [rax+rdx*8-2147479552]", 0, 1, 0, 2, 8, -2147479552LL, 4, 0, 0, 0LL) \
  F(23, "mov ecx, DWORD PTR [r8+rsi*1+127]", 0, 1, 8, 6, 1, 127LL, 4, 0, 0, 0LL) \
  F(24, "mov edx, DWORD PTR [rsp+r14*4-128]", 0, 1, 4, 14, 4, -128LL, 4, 0, 0, 0LL) \
  F(25, "mov ebx, DWORD PTR [rip+g_buf+61]", 0, 1, -1, -1, 1, 61LL, 4, 0, 0, 0LL) \
  F(26, "mov DWORD PTR [rdi], ecx", 0, 1, 7, -1, 1, 0LL, 4, 0, 0, 0LL) \
  F(27, "mov DWORD PTR [rsi+8], ebx", 0, 1, 6, -1, 1, 8LL, 4, 0, 0, 0LL) \
  F(28, "mov DWORD PTR [rsp+24], esi", 0, 1, 4, -1, 1, 24LL, 4, 0, 0, 0LL) \
  F(29, "mov DWORD PTR [rip+g_buf+3], r8d", 0, 1, -1, -1, 1, 3LL, 4, 0, 0, 0LL) \
  F(30, "mov DWORD PTR [rbp-16], r10d", 0, 1, 5, -1, 1, -16LL, 4, 0, 0, 0LL) \
  F(31, "mov DWORD PTR [r13], r12d", 0, 1, 13, -1, 1, 0LL, 4, 0, 0, 0LL) \
  F(32, "mov DWORD PTR [rdx+rcx*1], r14d", 0, 1, 2, 1, 1, 0LL, 4, 0, 0, 0LL) \
  F(33, "mov DWORD PTR [r12+40], eax", 0, 1, 12, -1, 1, 40LL, 4, 0, 0, 0LL) \
  F(34, "mov DWORD PTR [rbx+r9*2+7], edx", 0, 1, 3, 9, 2, 7LL, 4, 0, 0, 0LL) \
  F(35, "mov DWORD PTR [r10+rbp*4-100], ebp", 0, 1, 10, 5, 4, -100LL, 4, 0, 0, 0LL) \
  F(36, "mov DWORD PTR [rip+g_buf], edi", 0, 1, -1, -1, 1, 0LL, 4, 0, 0, 0LL) \
  F(37, "mov DWORD PTR [r15+r11*8+74565], r9d", 0, 1, 15, 11, 8, 74565LL, 4, 0, 0, 0LL) \
  F(38, "mov DWORD PTR [rax+rdx*8-2147479552], r11d", 0, 1, 0, 2, 8, -2147479552LL, 4, 0, 0, 0LL) \
  F(39, "mov DWORD PTR [r8+rsi*1+127], r13d", 0, 1, 8, 6, 1, 127LL, 4, 0, 0, 0LL) \
  F(40, "mov DWORD PTR [rsp+r14*4-128], r15d", 0, 1, 4, 14, 4, -128LL, 4, 0, 0, 0LL) \
  F(41, "mov DWORD PTR [rip+g_buf+61], ecx", 0, 1, -1, -1, 1, 61LL, 4, 0, 0, 0LL) \
  F(42, "add ebx, edx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(43, "add esi, esi", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(44, "add ecx, 127", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 127LL) \
  F(45, "add edx, -128", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -128LL) \
  F(46, "add ebx, 128", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 128LL) \
  F(47, "add ebx, DWORD PTR [rsi+8]", 0, 1, 6, -1, 1, 8LL, 4, 0, 0, 0LL) \
  F(48, "add r11d, DWORD PTR [rbx+r9*2+7]", 0, 1, 3, 9, 2, 7LL, 4, 0, 0, 0LL) \
  F(49, "adc r8d, ebp", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(50, "adc r8d, r8d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(51, "adc ebx, -1012569735", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -1012569735LL) \
  F(52, "adc ebp, 1249150122", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 1249150122LL) \
  F(53, "adc esi, -1538233109", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -1538233109LL) \
  F(54, "adc esi, DWORD PTR [rip+g_buf+3]", 0, 1, -1, -1, 1, 3LL, 4, 0, 0, 0LL) \
  F(55, "adc r13d, DWORD PTR [rip+g_buf]", 0, 1, -1, -1, 1, 0LL, 4, 0, 0, 0LL) \
  F(56, "sub edi, r12d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(57, "sub r10d, r10d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(58, "sub esi, -32", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -32LL) \
  F(59, "sub edi, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 0LL) \
  F(60, "sub r8d, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 1LL) \
  F(61, "sub r8d, DWORD PTR [r13]", 0, 1, 13, -1, 1, 0LL, 4, 0, 0, 0LL) \
  F(62, "sub r15d, DWORD PTR [rax+rdx*8-2147479552]", 0, 1, 0, 2, 8, -2147479552LL, 4, 0, 0, 0LL) \
  F(63, "sbb r9d, eax", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(64, "sbb r12d, r12d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(65, "sbb r8d, 128", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 128LL) \
  F(66, "sbb r9d, 2147483647", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 2147483647LL) \
  F(67, "sbb r10d, -2147483648", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -2147483648LL) \
  F(68, "sbb r10d, DWORD PTR [r12+40]", 0, 1, 12, -1, 1, 40LL, 4, 0, 0, 0LL) \
  F(69, "sbb ecx, DWORD PTR [rsp+r14*4-128]", 0, 1, 4, 14, 4, -128LL, 4, 0, 0, 0LL) \
  F(70, "and r14d, ebx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(71, "and r14d, r14d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(72, "and r10d, -1538233109", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -1538233109LL) \
  F(73, "and r11d, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 255LL) \
  F(74, "and r12d, 65535", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 65535LL) \
  F(75, "and r12d, DWORD PTR [r10+rbp*4-100]", 0, 1, 10, 5, 4, -100LL, 4, 0, 0, 0LL) \
  F(76, "and ebx, DWORD PTR [rdi]", 0, 1, 7, -1, 1, 0LL, 4, 0, 0, 0LL) \
  F(77, "or r15d, r12d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(78, "or eax, eax", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(79, "or r12d, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 1LL) \
  F(80, "or r13d, -1", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -1LL) \
  F(81, "or r14d, 127", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 127LL) \
  F(82, "or r14d, DWORD PTR [r15+r11*8+74565]", 0, 1, 15, 11, 8, 74565LL, 4, 0, 0, 0LL) \
  F(83, "or esi, DWORD PTR [rsp+24]", 0, 1, 4, -1, 1, 24LL, 4, 0, 0, 0LL) \
  F(84, "xor ebx, edx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(85, "xor edx, edx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(86, "xor r14d, -2147483648", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -2147483648LL) \
  F(87, "xor r15d, 305419896", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 305419896LL) \
  F(88, "xor eax, -1012569735", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -1012569735LL) \
  F(89, "xor eax, DWORD PTR [r8+rsi*1+127]", 0, 1, 8, 6, 1, 127LL, 4, 0, 0, 0LL) \
  F(90, "xor r8d, DWORD PTR [rbp-16]", 0, 1, 5, -1, 1, -16LL, 4, 0, 0, 0LL) \
  F(91, "cmp r8d, ebp", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(92, "cmp ebp, ebp", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(93, "cmp eax, 65535", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 65535LL) \
  F(94, "cmp ecx, 64", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 64LL) \
  F(95, "cmp edx, -32", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -32LL) \
  F(96, "cmp edx, DWORD PTR [rip+g_buf+61]", 0, 1, -1, -1, 1, 61LL, 4, 0, 0, 0LL) \
  F(97, "cmp r10d, DWORD PTR [rdx+rcx*1]", 0, 1, 2, 1, 1, 0LL, 4, 0, 0, 0LL) \
  F(98, "test edi, r12d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(99, "test edi, edi", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(100, "test edx, 127", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 127LL) \
  F(101, "test ebx, -128", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -128LL) \
  F(102, "test ebp, 128", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 128LL) \
  F(103, "test ebp, DWORD PTR [rsi+8]", 0, 1, 6, -1, 1, 8LL, 4, 0, 0, 0LL) \
  F(104, "test r12d, DWORD PTR [rbx+r9*2+7]", 0, 1, 3, 9, 2, 7LL, 4, 0, 0, 0LL) \
  F(105, "lea ecx, [rdi]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(106, "lea edx, [rsi+8]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(107, "lea ebx, [rsp+24]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(108, "lea ebp, [rip+g_buf+3]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(109, "lea esi, [rbp-16]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(110, "lea edi, [r13]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(111, "lea r8d, [rdx+rcx*1]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(112, "lea r9d, [r12+40]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(113, "lea r10d, [rbx+r9*2+7]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(114, "lea r11d, [r10+rbp*4-100]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(115, "lea r12d, [rip+g_buf]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(116, "lea r13d, [r15+r11*8+74565]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(117, "lea r14d, [rax+rdx*8-2147479552]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(118, "lea r15d, [r8+rsi*1+127]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(119, "lea eax, [rsp+r14*4-128]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(120, "lea ecx, [rip+g_buf+61]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(121, "rorx ebx, edx, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(122, "rorx esi, r15d, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(123, "rorx r8d, ebp, 6", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(124, "rorx r13d, r10d, 13", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(125, "rorx edi, r12d, 31", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(126, "rorx r11d, r14d, 32", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(127, "rorx r9d, eax, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(128, "rorx r10d, r10d, 7", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(129, "andn eax, ebx, ecx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(130, "andn r10d, r10d, r11d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(131, "andn r12d, r13d, r12d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(132, "andn esi, edi, edi", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(133, "andn r8d, r8d, r8d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(134, "andn edx, r8d, DWORD PTR [rsp+24]", 0, 1, 4, -1, 1, 24LL, 4, 0, 0, 0LL) \
  F(135, "andn r10d, r15d, DWORD PTR [r10+rbp*4-100]", 0, 1, 10, 5, 4, -100LL, 4, 0, 0, 0LL) \
  F(136, "andn r13d, edx, DWORD PTR [rax+rdx*8-2147479552]", 0, 1, 0, 2, 8, -2147479552LL, 4, 0, 0, 0LL) \
  F(137, "ror ecx, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(138, "ror ebp, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(139, "ror r8d, 2", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(140, "ror r11d, 7", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(141, "ror r14d, 16", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(142, "ror ecx, 31", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(143, "ror ebp, 32", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(144, "ror r8d, 33", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(145, "ror r11d, 63", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(146, "ror r14d, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(147, "rol edx, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(148, "rol esi, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(149, "rol r9d, 2", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(150, "rol r12d, 7", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(151, "rol r15d, 16", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(152, "rol edx, 31", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(153, "rol esi, 32", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(154, "rol r9d, 33", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(155, "rol r12d, 63", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(156, "rol r15d, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(157, "shr ebx, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(158, "shr edi, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(159, "shr r10d, 2", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(160, "shr r13d, 7", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(161, "shr eax, 16", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(162, "shr ebx, 31", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(163, "shr edi, 32", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(164, "shr r10d, 33", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(165, "shr r13d, 63", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(166, "shr eax, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(167, "shl ebp, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(168, "shl r8d, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(169, "shl r11d, 2", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(170, "shl r14d, 7", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(171, "shl ecx, 16", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(172, "shl ebp, 31", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(173, "shl r8d, 32", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(174, "shl r11d, 33", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(175, "shl r14d, 63", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(176, "shl ecx, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(177, "not eax", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(178, "not r14d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(179, "bswap ecx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(180, "bswap r9d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(181, "bswap ebp", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(182, "inc edx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(183, "dec edx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(184, "inc r11d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(185, "dec r11d", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(186, "movbe ecx, DWORD PTR [rsi+8]", 0, 1, 6, -1, 1, 8LL, 4, 0, 0, 0LL) \
  F(187, "movbe ebp, DWORD PTR [rbp-16]", 0, 1, 5, -1, 1, -16LL, 4, 0, 0, 0LL) \
  F(188, "movbe r10d, DWORD PTR [r10+rbp*4-100]", 0, 1, 10, 5, 4, -100LL, 4, 0, 0, 0LL) \
  F(189, "movbe r14d, DWORD PTR [r8+rsi*1+127]", 0, 1, 8, 6, 1, 127LL, 4, 0, 0, 0LL) \
  F(190, "movbe ecx, DWORD PTR [rdi]", 0, 1, 7, -1, 1, 0LL, 4, 0, 0, 0LL) \
  F(191, "mov rsi, r15", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(192, "mov r9, rax", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(193, "mov r15, r12", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(194, "mov rbx, rbx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(195, "mov rdx, -1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(196, "mov rbx, 128", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(197, "mov rbp, 305419896", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(198, "mov rsi, -1538233109", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(199, "mov rdi, 64", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(200, "mov r8, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(201, "mov rdi, QWORD PTR [rdi]", 0, 1, 7, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(202, "mov r8, QWORD PTR [rsi+8]", 0, 1, 6, -1, 1, 8LL, 8, 0, 0, 0LL) \
  F(203, "mov r9, QWORD PTR [rsp+24]", 0, 1, 4, -1, 1, 24LL, 8, 0, 0, 0LL) \
  F(204, "mov r10, QWORD PTR [rip+g_buf+3]", 0, 1, -1, -1, 1, 3LL, 8, 0, 0, 0LL) \
  F(205, "mov r11, QWORD PTR [rbp-16]", 0, 1, 5, -1, 1, -16LL, 8, 0, 0, 0LL) \
  F(206, "mov r12, QWORD PTR [r13]", 0, 1, 13, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(207, "mov r13, QWORD PTR [rdx+rcx*1]", 0, 1, 2, 1, 1, 0LL, 8, 0, 0, 0LL) \
  F(208, "mov r14, QWORD PTR [r12+40]", 0, 1, 12, -1, 1, 40LL, 8, 0, 0, 0LL) \
  F(209, "mov r15, QWORD PTR [rbx+r9*2+7]", 0, 1, 3, 9, 2, 7LL, 8, 0, 0, 0LL) \
  F(210, "mov rax, QWORD PTR [r10+rbp*4-100]", 0, 1, 10, 5, 4, -100LL, 8, 0, 0, 0LL) \
  F(211, "mov rcx, QWORD PTR [rip+g_buf]", 0, 1, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(212, "mov rdx, QWORD PTR [r15+r11*8+74565]", 0, 1, 15, 11, 8, 74565LL, 8, 0, 0, 0LL) \
  F(213, "mov rbx, QWORD PTR [rax+rdx*8-2147479552]", 0, 1, 0, 2, 8, -2147479552LL, 8, 0, 0, 0LL) \
  F(214, "mov rbp, QWORD PTR [r8+rsi*1+127]", 0, 1, 8, 6, 1, 127LL, 8, 0, 0, 0LL) \
  F(215, "mov rsi, QWORD PTR [rsp+r14*4-128]", 0, 1, 4, 14, 4, -128LL, 8, 0, 0, 0LL) \
  F(216, "mov rdi, QWORD PTR [rip+g_buf+61]", 0, 1, -1, -1, 1, 61LL, 8, 0, 0, 0LL) \
  F(217, "mov QWORD PTR [rdi], rdx", 0, 1, 7, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(218, "mov QWORD PTR [rsi+8], rbp", 0, 1, 6, -1, 1, 8LL, 8, 0, 0, 0LL) \
  F(219, "mov QWORD PTR [rsp+24], rdi", 0, 1, 4, -1, 1, 24LL, 8, 0, 0, 0LL) \
  F(220, "mov QWORD PTR [rip+g_buf+3], r9", 0, 1, -1, -1, 1, 3LL, 8, 0, 0, 0LL) \
  F(221, "mov QWORD PTR [rbp-16], r11", 0, 1, 5, -1, 1, -16LL, 8, 0, 0, 0LL) \
  F(222, "mov QWORD PTR [r13], r13", 0, 1, 13, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(223, "mov QWORD PTR [rdx+rcx*1], r15", 0, 1, 2, 1, 1, 0LL, 8, 0, 0, 0LL) \
  F(224, "mov QWORD PTR [r12+40], rcx", 0, 1, 12, -1, 1, 40LL, 8, 0, 0, 0LL) \
  F(225, "mov QWORD PTR [rbx+r9*2+7], rbx", 0, 1, 3, 9, 2, 7LL, 8, 0, 0, 0LL) \
  F(226, "mov QWORD PTR [r10+rbp*4-100], rsi", 0, 1, 10, 5, 4, -100LL, 8, 0, 0, 0LL) \
  F(227, "mov QWORD PTR [rip+g_buf], r8", 0, 1, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(228, "mov QWORD PTR [r15+r11*8+74565], r10", 0, 1, 15, 11, 8, 74565LL, 8, 0, 0, 0LL) \
  F(229, "mov QWORD PTR [rax+rdx*8-2147479552], r12", 0, 1, 0, 2, 8, -2147479552LL, 8, 0, 0, 0LL) \
  F(230, "mov QWORD PTR [r8+rsi*1+127], r14", 0, 1, 8, 6, 1, 127LL, 8, 0, 0, 0LL) \
  F(231, "mov QWORD PTR [rsp+r14*4-128], rax", 0, 1, 4, 14, 4, -128LL, 8, 0, 0, 0LL) \
  F(232, "mov QWORD PTR [rip+g_buf+61], rdx", 0, 1, -1, -1, 1, 61LL, 8, 0, 0, 0LL) \
  F(233, "add rsi, r15", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(234, "add rdi, rdi", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(235, "add rdx, 2147483647", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 2147483647LL) \
  F(236, "add rbx, -2147483648", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -2147483648LL) \
  F(237, "add rbp, 305419896", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 305419896LL) \
  F(238, "add rbp, QWORD PTR [rsp+24]", 0, 1, 4, -1, 1, 24LL, 8, 0, 0, 0LL) \
  F(239, "add r12, QWORD PTR [r10+rbp*4-100]", 0, 1, 10, 5, 4, -100LL, 8, 0, 0, 0LL) \
  F(240, "adc r13, r10", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(241, "adc r9, r9", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(242, "adc rbp, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 255LL) \
  F(243, "adc rsi, 65535", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 65535LL) \
  F(244, "adc rdi, 64", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 64LL) \
  F(245, "adc rdi, QWORD PTR [rbp-16]", 0, 1, 5, -1, 1, -16LL, 8, 0, 0, 0LL) \
  F(246, "adc r14, QWORD PTR [r15+r11*8+74565]", 0, 1, 15, 11, 8, 74565LL, 8, 0, 0, 0LL) \
  F(247, "sub r11, r14", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(248, "sub r11, r11", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(249, "sub rdi, -1", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -1LL) \
  F(250, "sub r8, 127", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 127LL) \
  F(251, "sub r9, -128", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -128LL) \
  F(252, "sub r9, QWORD PTR [rdx+rcx*1]", 0, 1, 2, 1, 1, 0LL, 8, 0, 0, 0LL) \
  F(253, "sub rax, QWORD PTR [r8+rsi*1+127]", 0, 1, 8, 6, 1, 127LL, 8, 0, 0, 0LL) \
  F(254, "sbb rdx, r13", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(255, "sbb r13, r13", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(256, "sbb r9, 305419896", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 305419896LL) \
  F(257, "sbb r10, -1012569735", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -1012569735LL) \
  F(258, "sbb r11, 1249150122", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 1249150122LL) \
  F(259, "sbb r11, QWORD PTR [rbx+r9*2+7]", 0, 1, 3, 9, 2, 7LL, 8, 0, 0, 0LL) \
  F(260, "sbb rdx, QWORD PTR [rip+g_buf+61]", 0, 1, -1, -1, 1, 61LL, 8, 0, 0, 0LL) \
  F(261, "and rcx, r8", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(262, "and r15, r15", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(263, "and r11, 64", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 64LL) \
  F(264, "and r12, -32", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -32LL) \
  F(265, "and r13, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 0LL) \
  F(266, "and r13, QWORD PTR [rip+g_buf]", 0, 1, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(267, "and rbp, QWORD PTR [rsi+8]", 0, 1, 6, -1, 1, 8LL, 8, 0, 0, 0LL) \
  F(268, "or rax, rcx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(269, "or rcx, rcx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(270, "or r13, -128", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -128LL) \
  F(271, "or r14, 128", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 128LL) \
  F(272, "or r15, 2147483647", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 2147483647LL) \
  F(273, "or r15, QWORD PTR [rax+rdx*8-2147479552]", 0, 1, 0, 2, 8, -2147479552LL, 8, 0, 0, 0LL) \
  F(274, "or rdi, QWORD PTR [rip+g_buf+3]", 0, 1, -1, -1, 1, 3LL, 8, 0, 0, 0LL) \
  F(275, "xor rsi, r15", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(276, "xor rbx, rbx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(277, "xor r15, 1249150122", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 1249150122LL) \
  F(278, "xor rax, -1538233109", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -1538233109LL) \
  F(279, "xor rcx, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 255LL) \
  F(280, "xor rcx, QWORD PTR [rsp+r14*4-128]", 0, 1, 4, 14, 4, -128LL, 8, 0, 0, 0LL) \
  F(281, "xor r9, QWORD PTR [r13]", 0, 1, 13, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(282, "cmp r13, r10", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(283, "cmp rsi, rsi", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(284, "cmp rcx, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 0LL) \
  F(285, "cmp rdx, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 1LL) \
  F(286, "cmp rbx, -1", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -1LL) \
  F(287, "cmp rbx, QWORD PTR [rdi]", 0, 1, 7, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(288, "cmp r11, QWORD PTR [r12+40]", 0, 1, 12, -1, 1, 40LL, 8, 0, 0, 0LL) \
  F(289, "test r11, r14", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(290, "test r8, r8", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(291, "test rbx, 2147483647", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 2147483647LL) \
  F(292, "test rbp, -2147483648", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -2147483648LL) \
  F(293, "test rsi, 305419896", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 305419896LL) \
  F(294, "test rsi, QWORD PTR [rsp+24]", 0, 1, 4, -1, 1, 24LL, 8, 0, 0, 0LL) \
  F(295, "test r13, QWORD PTR [r10+rbp*4-100]", 0, 1, 10, 5, 4, -100LL, 8, 0, 0, 0LL) \
  F(296, "lea rdx, [rdi]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(297, "lea rbx, [rsi+8]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(298, "lea rbp, [rsp+24]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(299, "lea rsi, [rip+g_buf+3]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(300, "lea rdi, [rbp-16]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(301, "lea r8, [r13]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(302, "lea r9, [rdx+rcx*1]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(303, "lea r10, [r12+40]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(304, "lea r11, [rbx+r9*2+7]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(305, "lea r12, [r10+rbp*4-100]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(306, "lea r13, [rip+g_buf]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(307, "lea r14, [r15+r11*8+74565]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(308, "lea r15, [rax+rdx*8-2147479552]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(309, "lea rax, [r8+rsi*1+127]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(310, "lea rcx, [rsp+r14*4-128]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(311, "lea rdx, [rip+g_buf+61]", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(312, "rorx rsi, r15, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(313, "rorx r8, rbp, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(314, "rorx r13, r10, 6", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(315, "rorx rdi, r12, 28", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(316, "rorx r11, r14, 32", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(317, "rorx r9, rax, 41", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(318, "rorx rdx, r13, 63", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(319, "rorx r14, rbx, 64", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(320, "rorx rcx, r8, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(321, "rorx r10, r10, 7", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(322, "andn rax, rbx, rcx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(323, "andn r10, r10, r11", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(324, "andn r12, r13, r12", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(325, "andn rsi, rdi, rdi", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(326, "andn r8, r8, r8", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(327, "andn rdx, r8, QWORD PTR [rip+g_buf+3]", 0, 1, -1, -1, 1, 3LL, 8, 0, 0, 0LL) \
  F(328, "andn r10, r15, QWORD PTR [rip+g_buf]", 0, 1, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(329, "andn r13, rdx, QWORD PTR [r8+rsi*1+127]", 0, 1, 8, 6, 1, 127LL, 8, 0, 0, 0LL) \
  F(330, "ror rdx, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(331, "ror rsi, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(332, "ror r9, 2", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(333, "ror r12, 7", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(334, "ror r15, 31", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(335, "ror rdx, 32", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(336, "ror rsi, 33", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(337, "ror r9, 63", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(338, "ror r12, 64", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(339, "ror r15, 65", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(340, "ror rdx, 127", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(341, "ror rsi, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(342, "rol rbx, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(343, "rol rdi, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(344, "rol r10, 2", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(345, "rol r13, 7", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(346, "rol rax, 31", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(347, "rol rbx, 32", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(348, "rol rdi, 33", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(349, "rol r10, 63", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(350, "rol r13, 64", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(351, "rol rax, 65", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(352, "rol rbx, 127", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(353, "rol rdi, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(354, "shr rbp, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(355, "shr r8, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(356, "shr r11, 2", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(357, "shr r14, 7", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(358, "shr rcx, 31", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(359, "shr rbp, 32", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(360, "shr r8, 33", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(361, "shr r11, 63", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(362, "shr r14, 64", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(363, "shr rcx, 65", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(364, "shr rbp, 127", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(365, "shr r8, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(366, "shl rsi, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(367, "shl r9, 1", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(368, "shl r12, 2", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(369, "shl r15, 7", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(370, "shl rdx, 31", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(371, "shl rsi, 32", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(372, "shl r9, 33", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(373, "shl r12, 63", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(374, "shl r15, 64", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(375, "shl rdx, 65", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(376, "shl rsi, 127", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(377, "shl r9, 255", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(378, "not rax", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(379, "not r14", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(380, "bswap rcx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(381, "bswap r9", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(382, "bswap rbp", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(383, "inc rdx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(384, "dec rdx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(385, "inc r11", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(386, "dec r11", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(387, "movbe rdx, QWORD PTR [rsp+24]", 0, 1, 4, -1, 1, 24LL, 8, 0, 0, 0LL) \
  F(388, "movbe rsi, QWORD PTR [r13]", 0, 1, 13, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(389, "movbe r11, QWORD PTR [rip+g_buf]", 0, 1, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(390, "movbe r15, QWORD PTR [rsp+r14*4-128]", 0, 1, 4, 14, 4, -128LL, 8, 0, 0, 0LL) \
  F(391, "movbe rdx, QWORD PTR [rsi+8]", 0, 1, 6, -1, 1, 8LL, 8, 0, 0, 0LL) \
  F(392, "sub rsp, 1792", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 1792LL) \
  F(393, "add rsp, 512", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, 512LL) \
  F(394, "and rsp, -32", 0, 0, -1, -1, 1, 0LL, 0, 0, 1, -32LL) \
  F(395, "mov r15, rsp", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(396, "mov rsp, rbp", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(397, "push rax", 0, 2, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(398, "push rbx", 0, 2, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(399, "push rsp", 0, 2, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(400, "push rbp", 0, 2, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(401, "push r12", 0, 2, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(402, "push r15", 0, 2, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(403, "pop rcx", 0, 3, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(404, "pop rbp", 0, 3, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(405, "pop rsp", 0, 3, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(406, "pop r13", 0, 3, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(407, "pop rdi", 0, 3, -1, -1, 1, 0LL, 8, 0, 0, 0LL) \
  F(408, "mulx rax, rbx, rcx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(409, "mulx r8, r9, rdx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(410, "mulx rax, rax, rbx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(411, "mulx rdx, rcx, rbx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(412, "mulx rbx, rdx, rcx", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(413, "mulx r14, r15, r14", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(414, "mulx r10, r11, r11", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(415, "movabs rax, 0", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(416, "movabs rbx, 18446744073709551615", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(417, "movabs rbp, 9223372036854775808", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(418, "movabs r15, 81985529216486895", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(419, "movabs r9, 2147483648", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(420, "movabs rsi, 4294967295", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(421, "movabs rdx, 18364758544493064720", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(422, "je 1f; mov rax, 0; jmp 2f; 1: mov rax, 1; 2:", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(423, "jne 1f; mov rax, 0; jmp 2f; 1: mov rax, 1; 2:", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(424, "jb 1f; mov rax, 0; jmp 2f; 1: mov rax, 1; 2:", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(425, "jae 1f; mov rax, 0; jmp 2f; 1: mov rax, 1; 2:", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(426, "jbe 1f; mov rax, 0; jmp 2f; 1: mov rax, 1; 2:", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(427, "ja 1f; mov rax, 0; jmp 2f; 1: mov rax, 1; 2:", 0, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(428, "vmovdqu xmm1, XMMWORD PTR [rsi+8]", 1, 1, 6, -1, 1, 8LL, 16, 0, 0, 0LL) \
  F(429, "vmovdqu ymm2, YMMWORD PTR [rbp-16]", 1, 1, 5, -1, 1, -16LL, 32, 0, 0, 0LL) \
  F(430, "vmovdqu YMMWORD PTR [r12+40], ymm3", 1, 1, 12, -1, 1, 40LL, 32, 0, 0, 0LL) \
  F(431, "vbroadcasti128 ymm4, XMMWORD PTR [rip+g_buf]", 1, 1, -1, -1, 1, 0LL, 16, 0, 0, 0LL) \
  F(432, "vpaddd ymm0, ymm7, YMMWORD PTR [r8+rsi*1+127]", 1, 1, 8, 6, 1, 127LL, 32, 0, 0, 0LL) \
  F(433, "vmovdqu xmm6, XMMWORD PTR [rbp-16]", 1, 1, 5, -1, 1, -16LL, 16, 0, 0, 0LL) \
  F(434, "vmovdqu ymm7, YMMWORD PTR [r12+40]", 1, 1, 12, -1, 1, 40LL, 32, 0, 0, 0LL) \
  F(435, "vmovdqu YMMWORD PTR [rip+g_buf], ymm8", 1, 1, -1, -1, 1, 0LL, 32, 0, 0, 0LL) \
  F(436, "vbroadcasti128 ymm9, XMMWORD PTR [r8+rsi*1+127]", 1, 1, 8, 6, 1, 127LL, 16, 0, 0, 0LL) \
  F(437, "vpaddd ymm3, ymm10, YMMWORD PTR [rdi]", 1, 1, 7, -1, 1, 0LL, 32, 0, 0, 0LL) \
  F(438, "vmovdqu xmm11, XMMWORD PTR [r12+40]", 1, 1, 12, -1, 1, 40LL, 16, 0, 0, 0LL) \
  F(439, "vmovdqu ymm12, YMMWORD PTR [rip+g_buf]", 1, 1, -1, -1, 1, 0LL, 32, 0, 0, 0LL) \
  F(440, "vmovdqu YMMWORD PTR [r8+rsi*1+127], ymm13", 1, 1, 8, 6, 1, 127LL, 32, 0, 0, 0LL) \
  F(441, "vbroadcasti128 ymm14, XMMWORD PTR [rdi]", 1, 1, 7, -1, 1, 0LL, 16, 0, 0, 0LL) \
  F(442, "vpaddd ymm6, ymm13, YMMWORD PTR [rip+g_buf+3]", 1, 1, -1, -1, 1, 3LL, 32, 0, 0, 0LL) \
  F(443, "vmovdqu xmm0, XMMWORD PTR [rip+g_buf]", 1, 1, -1, -1, 1, 0LL, 16, 0, 0, 0LL) \
  F(444, "vmovdqu ymm1, YMMWORD PTR [r8+rsi*1+127]", 1, 1, 8, 6, 1, 127LL, 32, 0, 0, 0LL) \
  F(445, "vmovdqu YMMWORD PTR [rdi], ymm2", 1, 1, 7, -1, 1, 0LL, 32, 0, 0, 0LL) \
  F(446, "vbroadcasti128 ymm3, XMMWORD PTR [rip+g_buf+3]", 1, 1, -1, -1, 1, 3LL, 16, 0, 0, 0LL) \
  F(447, "vpaddd ymm9, ymm0, YMMWORD PTR [rdx+rcx*1]", 1, 1, 2, 1, 1, 0LL, 32, 0, 0, 0LL) \
  F(448, "vmovdqu xmm5, XMMWORD PTR [r8+rsi*1+127]", 1, 1, 8, 6, 1, 127LL, 16, 0, 0, 0LL) \
  F(449, "vmovdqu ymm6, YMMWORD PTR [rdi]", 1, 1, 7, -1, 1, 0LL, 32, 0, 0, 0LL) \
  F(450, "vmovdqu YMMWORD PTR [rip+g_buf+3], ymm7", 1, 1, -1, -1, 1, 3LL, 32, 0, 0, 0LL) \
  F(451, "vbroadcasti128 ymm8, XMMWORD PTR [rdx+rcx*1]", 1, 1, 2, 1, 1, 0LL, 16, 0, 0, 0LL) \
  F(452, "vpaddd ymm12, ymm3, YMMWORD PTR [r10+rbp*4-100]", 1, 1, 10, 5, 4, -100LL, 32, 0, 0, 0LL) \
  F(453, "vinserti128 ymm0, ymm1, XMMWORD PTR [rdi], 1", 1, 1, 7, -1, 1, 0LL, 16, 0, 0, 0LL) \
  F(454, "vinserti128 ymm9, ymm14, XMMWORD PTR [rip+g_buf+3], 1", 1, 1, -1, -1, 1, 3LL, 16, 0, 0, 0LL) \
  F(455, "vinserti128 ymm5, ymm5, XMMWORD PTR [rdx+rcx*1], 1", 1, 1, 2, 1, 1, 0LL, 16, 0, 0, 0LL) \
  F(456, "vinserti128 ymm15, ymm3, XMMWORD PTR [r10+rbp*4-100], 1", 1, 1, 10, 5, 4, -100LL, 16, 0, 0, 0LL) \
  F(457, "vpshufb ymm0, ymm1, ymm2", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(458, "vpaddd ymm0, ymm1, ymm2", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(459, "vpxor ymm0, ymm1, ymm2", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(460, "vpshufb ymm5, ymm5, ymm12", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(461, "vpaddd ymm5, ymm5, ymm12", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(462, "vpxor ymm5, ymm5, ymm12", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(463, "vpshufb ymm9, ymm3, ymm9", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(464, "vpaddd ymm9, ymm3, ymm9", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(465, "vpxor ymm9, ymm3, ymm9", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(466, "vpshufb ymm15, ymm8, ymm8", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(467, "vpaddd ymm15, ymm8, ymm8", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(468, "vpxor ymm15, ymm8, ymm8", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(469, "vpshufb ymm7, ymm7, ymm7", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(470, "vpaddd ymm7, ymm7, ymm7", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(471, "vpxor ymm7, ymm7, ymm7", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(472, "vpshufb ymm10, ymm13, ymm4", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(473, "vpaddd ymm10, ymm13, ymm4", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(474, "vpxor ymm10, ymm13, ymm4", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(475, "vpalignr ymm0, ymm5, ymm2, 0", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(476, "vpalignr ymm1, ymm6, ymm5, 1", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(477, "vpalignr ymm2, ymm7, ymm8, 4", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(478, "vpalignr ymm3, ymm8, ymm11, 8", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(479, "vpalignr ymm4, ymm9, ymm14, 12", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(480, "vpalignr ymm5, ymm10, ymm1, 15", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(481, "vpalignr ymm6, ymm11, ymm4, 16", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(482, "vpalignr ymm7, ymm12, ymm7, 17", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(483, "vpalignr ymm8, ymm13, ymm10, 24", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(484, "vpalignr ymm9, ymm14, ymm13, 31", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(485, "vpalignr ymm10, ymm15, ymm0, 32", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(486, "vpalignr ymm11, ymm0, ymm3, 255", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(487, "vpsrld ymm1, ymm0, 0", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(488, "vpsrld ymm2, ymm2, 1", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(489, "vpsrld ymm3, ymm4, 2", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(490, "vpsrld ymm4, ymm6, 3", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(491, "vpsrld ymm5, ymm8, 7", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(492, "vpsrld ymm6, ymm10, 10", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(493, "vpsrld ymm7, ymm12, 17", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(494, "vpsrld ymm8, ymm14, 18", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(495, "vpsrld ymm9, ymm0, 31", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(496, "vpsrld ymm10, ymm2, 32", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(497, "vpsrld ymm11, ymm4, 255", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(498, "vpslld ymm3, ymm0, 0", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(499, "vpslld ymm4, ymm3, 1", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(500, "vpslld ymm5, ymm6, 5", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(501, "vpslld ymm6, ymm9, 13", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(502, "vpslld ymm7, ymm12, 14", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(503, "vpslld ymm8, ymm15, 25", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(504, "vpslld ymm9, ymm2, 31", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(505, "vpslld ymm10, ymm5, 32", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(506, "vpslld ymm11, ymm8, 255", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(507, "vpsrlq ymm7, ymm0, 0", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(508, "vpsrlq ymm8, ymm5, 1", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(509, "vpsrlq ymm9, ymm10, 6", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(510, "vpsrlq ymm10, ymm15, 19", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(511, "vpsrlq ymm11, ymm4, 32", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(512, "vpsrlq ymm12, ymm9, 61", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(513, "vpsrlq ymm13, ymm14, 63", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(514, "vpsrlq ymm14, ymm3, 64", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(515, "vpsrlq ymm15, ymm8, 255", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(516, "vpshufd ymm2, ymm1, 0", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(517, "vpshufd ymm3, ymm8, 27", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(518, "vpshufd ymm4, ymm15, 78", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(519, "vpshufd ymm5, ymm6, 147", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(520, "vpshufd ymm6, ymm13, 177", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(521, "vpshufd ymm7, ymm4, 228", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(522, "vpshufd ymm8, ymm11, 255", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(523, "vpshufd ymm9, ymm2, 57", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(524, "vzeroupper", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(525, "movdqu xmm2, XMMWORD PTR [rip+g_buf+3]", 1, 1, -1, -1, 1, 3LL, 16, 0, 0, 0LL) \
  F(526, "movdqu XMMWORD PTR [rdx+rcx*1], xmm4", 1, 1, 2, 1, 1, 0LL, 16, 0, 0, 0LL) \
  F(527, "movdqu xmm5, XMMWORD PTR [rdx+rcx*1]", 1, 1, 2, 1, 1, 0LL, 16, 0, 0, 0LL) \
  F(528, "movdqu XMMWORD PTR [r10+rbp*4-100], xmm7", 1, 1, 10, 5, 4, -100LL, 16, 0, 0, 0LL) \
  F(529, "movdqu xmm8, XMMWORD PTR [r10+rbp*4-100]", 1, 1, 10, 5, 4, -100LL, 16, 0, 0, 0LL) \
  F(530, "movdqu XMMWORD PTR [rax+rdx*8-2147479552], xmm10", 1, 1, 0, 2, 8, -2147479552LL, 16, 0, 0, 0LL) \
  F(531, "movdqu xmm11, XMMWORD PTR [rax+rdx*8-2147479552]", 1, 1, 0, 2, 8, -2147479552LL, 16, 0, 0, 0LL) \
  F(532, "movdqu XMMWORD PTR [rip+g_buf+61], xmm13", 1, 1, -1, -1, 1, 61LL, 16, 0, 0, 0LL) \
  F(533, "movdqa xmm1, xmm2", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(534, "paddd xmm1, xmm2", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(535, "pshufb xmm1, xmm2", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(536, "punpcklqdq xmm1, xmm2", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(537, "punpckhqdq xmm1, xmm2", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(538, "sha256rnds2 xmm1, xmm2, xmm0", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(539, "sha256msg1 xmm1, xmm2", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(540, "sha256msg2 xmm1, xmm2", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(541, "movdqa xmm0, xmm11", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(542, "paddd xmm0, xmm11", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(543, "pshufb xmm0, xmm11", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(544, "punpcklqdq xmm0, xmm11", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(545, "punpckhqdq xmm0, xmm11", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(546, "sha256rnds2 xmm0, xmm11, xmm0", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(547, "sha256msg1 xmm0, xmm11", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(548, "sha256msg2 xmm0, xmm11", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(549, "movdqa xmm6, xmm6", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(550, "paddd xmm6, xmm6", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(551, "pshufb xmm6, xmm6", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(552, "punpcklqdq xmm6, xmm6", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(553, "punpckhqdq xmm6, xmm6", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(554, "sha256rnds2 xmm6, xmm6, xmm0", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(555, "sha256msg1 xmm6, xmm6", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(556, "sha256msg2 xmm6, xmm6", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(557, "movdqa xmm13, xmm4", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(558, "paddd xmm13, xmm4", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(559, "pshufb xmm13, xmm4", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(560, "punpcklqdq xmm13, xmm4", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(561, "punpckhqdq xmm13, xmm4", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(562, "sha256rnds2 xmm13, xmm4, xmm0", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(563, "sha256msg1 xmm13, xmm4", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(564, "sha256msg2 xmm13, xmm4", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(565, "movdqa xmm8, xmm15", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(566, "paddd xmm8, xmm15", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(567, "pshufb xmm8, xmm15", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(568, "punpcklqdq xmm8, xmm15", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(569, "punpckhqdq xmm8, xmm15", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(570, "sha256rnds2 xmm8, xmm15, xmm0", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(571, "sha256msg1 xmm8, xmm15", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(572, "sha256msg2 xmm8, xmm15", 1, 0, -1, -1, 1, 0LL, 0, 1, 0, 0LL) \
  F(573, "pshufd xmm3, xmm0, 0", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(574, "pshufd xmm4, xmm5, 27", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(575, "pshufd xmm5, xmm10, 78", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(576, "pshufd xmm6, xmm15, 147", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(577, "pshufd xmm7, xmm4, 228", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(578, "pshufd xmm8, xmm9, 255", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(579, "palignr xmm1, xmm6, 0", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(580, "palignr xmm2, xmm9, 1", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(581, "palignr xmm3, xmm12, 4", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(582, "palignr xmm4, xmm15, 8", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(583, "palignr xmm5, xmm2, 12", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(584, "palignr xmm6, xmm5, 15", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(585, "palignr xmm7, xmm8, 16", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(586, "palignr xmm8, xmm11, 17", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(587, "palignr xmm9, xmm14, 31", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(588, "palignr xmm10, xmm1, 32", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \
  F(589, "palignr xmm11, xmm4, 255", 1, 0, -1, -1, 1, 0LL, 0, 0, 0, 0LL) \

// END GENERATED FORMS

#define PROLOGUE                                                               \
  "push rbx\n\tpush rbp\n\tpush r12\n\tpush r13\n\tpush r14\n\tpush r15\n\t"   \
  "mov QWORD PTR [rip+g_saved_rsp], rsp\n\t"                                   \
  "lea rsp, [rip+g_stack+256]\n\t"                                             \
  "push QWORD PTR [rip+g_fin]\n\tpopfq\n\t"
#define VLOAD_0 ""
#define VLOAD_1                                                                \
  "vmovdqu ymm0, [rip+g_vin+0]\n\tvmovdqu ymm1, [rip+g_vin+32]\n\t"            \
  "vmovdqu ymm2, [rip+g_vin+64]\n\tvmovdqu ymm3, [rip+g_vin+96]\n\t"           \
  "vmovdqu ymm4, [rip+g_vin+128]\n\tvmovdqu ymm5, [rip+g_vin+160]\n\t"         \
  "vmovdqu ymm6, [rip+g_vin+192]\n\tvmovdqu ymm7, [rip+g_vin+224]\n\t"         \
  "vmovdqu ymm8, [rip+g_vin+256]\n\tvmovdqu ymm9, [rip+g_vin+288]\n\t"         \
  "vmovdqu ymm10, [rip+g_vin+320]\n\tvmovdqu ymm11, [rip+g_vin+352]\n\t"       \
  "vmovdqu ymm12, [rip+g_vin+384]\n\tvmovdqu ymm13, [rip+g_vin+416]\n\t"       \
  "vmovdqu ymm14, [rip+g_vin+448]\n\tvmovdqu ymm15, [rip+g_vin+480]\n\t"
#define GLOAD                                                                  \
  "mov rax, [rip+g_in+0]\n\tmov rcx, [rip+g_in+8]\n\t"                         \
  "mov rdx, [rip+g_in+16]\n\tmov rbx, [rip+g_in+24]\n\t"                       \
  "mov rsp, [rip+g_in+32]\n\tmov rbp, [rip+g_in+40]\n\t"                       \
  "mov rsi, [rip+g_in+48]\n\tmov rdi, [rip+g_in+56]\n\t"                       \
  "mov r8, [rip+g_in+64]\n\tmov r9, [rip+g_in+72]\n\t"                         \
  "mov r10, [rip+g_in+80]\n\tmov r11, [rip+g_in+88]\n\t"                       \
  "mov r12, [rip+g_in+96]\n\tmov r13, [rip+g_in+104]\n\t"                      \
  "mov r14, [rip+g_in+112]\n\tmov r15, [rip+g_in+120]\n\t"
#define GSTORE                                                                 \
  "mov [rip+g_out+0], rax\n\tmov [rip+g_out+8], rcx\n\t"                       \
  "mov [rip+g_out+16], rdx\n\tmov [rip+g_out+24], rbx\n\t"                     \
  "mov [rip+g_out+32], rsp\n\tmov [rip+g_out+40], rbp\n\t"                     \
  "mov [rip+g_out+48], rsi\n\tmov [rip+g_out+56], rdi\n\t"                     \
  "mov [rip+g_out+64], r8\n\tmov [rip+g_out+72], r9\n\t"                       \
  "mov [rip+g_out+80], r10\n\tmov [rip+g_out+88], r11\n\t"                     \
  "mov [rip+g_out+96], r12\n\tmov [rip+g_out+104], r13\n\t"                    \
  "mov [rip+g_out+112], r14\n\tmov [rip+g_out+120], r15\n\t"
#define VSTORE_0 ""
#define VSTORE_1                                                               \
  "vmovdqu [rip+g_vout+0], ymm0\n\tvmovdqu [rip+g_vout+32], ymm1\n\t"          \
  "vmovdqu [rip+g_vout+64], ymm2\n\tvmovdqu [rip+g_vout+96], ymm3\n\t"         \
  "vmovdqu [rip+g_vout+128], ymm4\n\tvmovdqu [rip+g_vout+160], ymm5\n\t"       \
  "vmovdqu [rip+g_vout+192], ymm6\n\tvmovdqu [rip+g_vout+224], ymm7\n\t"       \
  "vmovdqu [rip+g_vout+256], ymm8\n\tvmovdqu [rip+g_vout+288], ymm9\n\t"       \
  "vmovdqu [rip+g_vout+320], ymm10\n\tvmovdqu [rip+g_vout+352], ymm11\n\t"     \
  "vmovdqu [rip+g_vout+384], ymm12\n\tvmovdqu [rip+g_vout+416], ymm13\n\t"     \
  "vmovdqu [rip+g_vout+448], ymm14\n\tvmovdqu [rip+g_vout+480], ymm15\n\t"
#define EPILOGUE                                                               \
  "lea rsp, [rip+g_stack+256]\n\t"                                             \
  "pushfq\n\tpop QWORD PTR [rip+g_fout]\n\t"                                   \
  "mov rsp, QWORD PTR [rip+g_saved_rsp]\n\t"                                   \
  "pop r15\n\tpop r14\n\tpop r13\n\tpop r12\n\tpop rbp\n\tpop rbx\n\t"         \
  "vzeroupper\n\tret\n"

// One assembly function t_<id> per form.  Flags are set by popfq before the
// register loads (mov does not affect flags) and read by pushfq after the
// register stores, so the instruction under test is the only flag writer.
#define ASMFN(id, text, vec, ...)                                              \
  __asm__(".pushsection .text\n\t.intel_syntax noprefix\n"                     \
          ".globl t_" #id "\n.type t_" #id ", @function\nt_" #id ":\n\t"         \
          PROLOGUE VLOAD_##vec GLOAD text "\n\t" GSTORE VSTORE_##vec EPILOGUE     \
          ".att_syntax prefix\n.popsection\n");
FORMS(ASMFN)

#define DECL(id, ...) void t_##id(void);
FORMS(DECL)

struct form {
  void (*fn)(void);
  const char *text;
  int vec, kind, base, index, scale;
  int64_t disp;
  int size, feature, hasimm;
  int64_t imm;
};
#define ENTRY(id, text, vec, kind, base, index, scale, disp, size, feature,     \
              hasimm, imm)                                                     \
  {t_##id, text, vec, kind, base, index, scale, disp, size, feature, hasimm, imm},
static const struct form forms[] = {FORMS(ENTRY)};
#define NFORMS ((int)(sizeof forms / sizeof forms[0]))

// xorshift64*
static uint64_t st = 0x0123456789abcdefULL;
static uint64_t rnd(void) {
  st ^= st >> 12; st ^= st << 25; st ^= st >> 27;
  return st * 0x2545f4914f6cdd1dULL;
}

// 64-bit edge values; the edge-case vectors give even-numbered registers
// E[j % 8] and odd-numbered ones E[j / 8 % 8], so any (even, odd) operand
// pair sees all 64 combinations.
static const uint64_t E[8] = {0, 1, ~0ULL, 1ULL << 63, (1ULL << 63) - 1,
                              0x80000000ULL, 0xffffffffULL, 0x7fffffffULL};
static const uint32_t E32[6] = {0, 1, 0xffffffffU, 0x80000000U, 0x7fffffffU, 0x00ff00ffU};
#define NEDGE 128

// A random 64-bit value, biased towards edge cases.
static uint64_t rv64(void) {
  uint64_t x = rnd();
  switch (rnd() % 16) {
    case 0: return 0;
    case 1: return ~0ULL;
    case 2: return 1ULL << 63;
    case 3: return (1ULL << 63) - 1;
    case 4: return x % 4;
    case 5: return -(x % 4);
    case 6: return (uint32_t)x;
    case 7: return 1ULL << (x % 64);
    case 8: return E[x % 8] ^ (1ULL << (rnd() % 64));
    default: return x;
  }
}

static uint32_t rv32(void) {
  uint32_t x = (uint32_t)rnd();
  switch (rnd() % 8) {
    case 0: return E32[rnd() % 6];
    case 1: return 1U << (x % 32);
    default: return x;
  }
}

static void phex(const uint8_t *p, int n) {  // most significant byte first
  for (int i = n - 1; i >= 0; i--) printf("%02x", p[i]);
}

int main(int argc, char **argv) {
  int nrandom = argc > 1 ? atoi(argv[1]) : 512;
  if (argc > 2) st = strtoull(argv[2], 0, 0) | 1;
  unsigned a, b, c, d;
  // X86_INSN_FORCE_SHA=1 tests the SHA forms even if CPUID does not report the
  // SHA extensions (some CPUs/VMs execute them without advertising them).
  const char *force_sha = getenv("X86_INSN_FORCE_SHA");
  int have_sha = (force_sha && *force_sha && strcmp(force_sha, "0")) ||
                 (__get_cpuid_count(7, 0, &a, &b, &c, &d) && (b >> 29 & 1));
  int have_avx2 = __get_cpuid_count(7, 0, &a, &b, &c, &d) && (b >> 5 & 1) && (b >> 3 & 1) &&
                  (b >> 8 & 1);
  if (!have_avx2) {
    fprintf(stderr, "this CPU lacks AVX2/BMI1/BMI2\n");
    return 1;
  }
  printf("b %llx %d\n", (unsigned long long)(uintptr_t)g_buf, BUFLEN);
  if (!have_sha) printf("nofeature 1 sha\n");
  for (int f = 0; f < NFORMS; f++) printf("f %d %s\n", f, forms[f].text);
  static uint64_t in[16];
  static uint8_t vin[16 * 32], buf[BUFLEN];
  for (int f = 0; f < NFORMS; f++) {
    const struct form *F = &forms[f];
    if (F->feature == 1 && !have_sha) continue;
    for (int j = 0; j < NEDGE + nrandom; j++) {
      int edge = j < NEDGE;
      uint64_t fl = 0x202;  // IF and the reserved bit; DF, TF clear
      if (edge) {
        for (int r = 0; r < 16; r++) in[r] = E[r % 2 ? j / 8 % 8 : j % 8];
        fl |= (j >> 6 & 1) | (rnd() & 0x8d4);
      } else {
        for (int r = 0; r < 16; r++) in[r] = rv64();
        for (int r = 0; r < 16; r++) {  // equal / related operands
          switch (rnd() % 16) {
            case 0: in[r] = in[rnd() % 16]; break;
            case 1: in[r] = ~in[rnd() % 16]; break;
            case 2: in[r] = in[rnd() % 16] + 1; break;
            case 3: in[r] = -in[rnd() % 16]; break;
          }
        }
        if (F->hasimm && rnd() % 8 == 0)  // operands equal / adjacent to the immediate
          for (int r = 0; r < 16; r++) {
            in[r] = (uint64_t)F->imm + rnd() % 3 - 1;
            if (rnd() % 2) in[r] = (uint32_t)in[r] | rnd() << 32;  // (32-bit forms)
          }
        fl |= rnd() & 0x8d5;  // CF PF AF ZF SF OF
      }
      for (int k = 0; k < 16 * 8; k++) {
        uint32_t w = edge ? E32[(j + k * 5 + k / 8) % 6] : rv32();
        memcpy(vin + 4 * k, &w, 4);
      }
      for (int k = 0; k < BUFLEN; k += 8) {
        uint64_t w = rv64();
        memcpy(buf + k, &w, 8);
      }
      // Point the memory operand / stack pointer into the buffer.
      uint64_t bufa = (uint64_t)(uintptr_t)g_buf;
      if (F->kind == 1 && F->base >= 0) {
        int range = BUFLEN - F->size + 1;
        uint64_t off = edge ? (uint64_t)(j * 7 % range) : rnd() % range;
        uint64_t idx = F->index >= 0 ? in[F->index] : 0;
        in[F->base] = bufa + off - idx * (uint64_t)F->scale - (uint64_t)F->disp;
      } else if (F->kind == 2) {  // push writes [rsp-8, rsp)
        in[4] = bufa + 8 + (edge ? (uint64_t)(j * 7 % (BUFLEN - 7)) : rnd() % (BUFLEN - 7));
      } else if (F->kind == 3) {  // pop reads [rsp, rsp+8)
        in[4] = bufa + (edge ? (uint64_t)(j * 7 % (BUFLEN - 7)) : rnd() % (BUFLEN - 7));
      }
      memcpy(g_in, in, sizeof in);
      memcpy(g_vin, vin, sizeof vin);
      memcpy(g_buf, buf, sizeof buf);
      g_fin = fl;
      F->fn();
      printf("v %d %llx ", f, (unsigned long long)fl);
      for (int r = 0; r < 16; r++) printf("%s%016llx", r ? "," : "", (unsigned long long)in[r]);
      printf(" ");
      if (F->vec) {
        for (int r = 0; r < 16; r++) { if (r) printf(","); phex(vin + 32 * r, 32); }
      } else printf("-");
      printf(" ");
      if (F->kind) phex(buf, BUFLEN); else printf("-");
      printf(" %llx ", (unsigned long long)(g_fout & 0x8d5));
      int any = 0;
      for (int r = 0; r < 16; r++)
        if (g_out[r] != in[r]) printf("%s%d=%016llx", any++ ? "," : "", r, (unsigned long long)g_out[r]);
      if (!any) printf("-");
      printf(" ");
      any = 0;
      if (F->vec)
        for (int r = 0; r < 16; r++)
          if (memcmp(g_vout + 32 * r, vin + 32 * r, 32)) {
            printf("%s%d=", any++ ? "," : "", r);
            phex(g_vout + 32 * r, 32);
          }
      if (!any) printf("-");
      printf(" ");
      if (F->kind) phex(g_buf, BUFLEN); else printf("-");
      printf("\n");
    }
  }
  return 0;
}
