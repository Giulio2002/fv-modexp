.intel_syntax noprefix
.text
.globl gr
gr:
  lea r8, [rcx+rcx]
  cmp rbx, r8
  ja NEWLEN
  cmp rcx, 256
  jb HAVE
  mov r8, rcx
LOOP:
  lea r9, [r8+768]
  shr r9, 2
  add r8, r9
  cmp r8, rbx
  jb LOOP
  jmp HAVE
NEWLEN:
  mov r8, rbx
HAVE:
  mov r9, r8
  shl r9, 3
  cmp r9, 32760
  ja LARGE
C0:
  mov r10d, 8
  cmp r9, r10
  {disp32} jbe ALLOC
C1:
  mov r10d, 16
  cmp r9, r10
  {disp32} jbe ALLOC
C2:
  mov r10d, 24
  cmp r9, r10
  {disp32} jbe ALLOC
C3:
  mov r10d, 32
  cmp r9, r10
  {disp32} jbe ALLOC
C4:
  mov r10d, 48
  cmp r9, r10
  {disp32} jbe ALLOC
C5:
  mov r10d, 64
  cmp r9, r10
  {disp32} jbe ALLOC
C6:
  mov r10d, 80
  cmp r9, r10
  {disp32} jbe ALLOC
C7:
  mov r10d, 96
  cmp r9, r10
  {disp32} jbe ALLOC
C8:
  mov r10d, 112
  cmp r9, r10
  {disp32} jbe ALLOC
C9:
  mov r10d, 128
  cmp r9, r10
  {disp32} jbe ALLOC
C10:
  mov r10d, 144
  cmp r9, r10
  {disp32} jbe ALLOC
C11:
  mov r10d, 160
  cmp r9, r10
  {disp32} jbe ALLOC
C12:
  mov r10d, 176
  cmp r9, r10
  {disp32} jbe ALLOC
C13:
  mov r10d, 192
  cmp r9, r10
  {disp32} jbe ALLOC
C14:
  mov r10d, 208
  cmp r9, r10
  {disp32} jbe ALLOC
C15:
  mov r10d, 224
  cmp r9, r10
  {disp32} jbe ALLOC
C16:
  mov r10d, 240
  cmp r9, r10
  {disp32} jbe ALLOC
C17:
  mov r10d, 256
  cmp r9, r10
  {disp32} jbe ALLOC
C18:
  mov r10d, 288
  cmp r9, r10
  {disp32} jbe ALLOC
C19:
  mov r10d, 320
  cmp r9, r10
  {disp32} jbe ALLOC
C20:
  mov r10d, 352
  cmp r9, r10
  {disp32} jbe ALLOC
C21:
  mov r10d, 384
  cmp r9, r10
  {disp32} jbe ALLOC
C22:
  mov r10d, 416
  cmp r9, r10
  {disp32} jbe ALLOC
C23:
  mov r10d, 448
  cmp r9, r10
  {disp32} jbe ALLOC
C24:
  mov r10d, 480
  cmp r9, r10
  {disp32} jbe ALLOC
C25:
  mov r10d, 512
  cmp r9, r10
  {disp32} jbe ALLOC
C26:
  mov r10d, 576
  cmp r9, r10
  {disp32} jbe ALLOC
C27:
  mov r10d, 640
  cmp r9, r10
  {disp32} jbe ALLOC
C28:
  mov r10d, 704
  cmp r9, r10
  {disp32} jbe ALLOC
C29:
  mov r10d, 768
  cmp r9, r10
  {disp32} jbe ALLOC
C30:
  mov r10d, 896
  cmp r9, r10
  {disp32} jbe ALLOC
C31:
  mov r10d, 1024
  cmp r9, r10
  {disp32} jbe ALLOC
C32:
  mov r10d, 1152
  cmp r9, r10
  {disp32} jbe ALLOC
C33:
  mov r10d, 1280
  cmp r9, r10
  {disp32} jbe ALLOC
C34:
  mov r10d, 1408
  cmp r9, r10
  {disp32} jbe ALLOC
C35:
  mov r10d, 1536
  cmp r9, r10
  {disp32} jbe ALLOC
C36:
  mov r10d, 1792
  cmp r9, r10
  {disp32} jbe ALLOC
C37:
  mov r10d, 2048
  cmp r9, r10
  {disp32} jbe ALLOC
C38:
  mov r10d, 2304
  cmp r9, r10
  {disp32} jbe ALLOC
C39:
  mov r10d, 2688
  cmp r9, r10
  {disp32} jbe ALLOC
C40:
  mov r10d, 3072
  cmp r9, r10
  {disp32} jbe ALLOC
C41:
  mov r10d, 3200
  cmp r9, r10
  {disp32} jbe ALLOC
C42:
  mov r10d, 3456
  cmp r9, r10
  {disp32} jbe ALLOC
C43:
  mov r10d, 4096
  cmp r9, r10
  {disp32} jbe ALLOC
C44:
  mov r10d, 4864
  cmp r9, r10
  {disp32} jbe ALLOC
C45:
  mov r10d, 5376
  cmp r9, r10
  {disp32} jbe ALLOC
C46:
  mov r10d, 6144
  cmp r9, r10
  {disp32} jbe ALLOC
C47:
  mov r10d, 6528
  cmp r9, r10
  {disp32} jbe ALLOC
C48:
  mov r10d, 6784
  cmp r9, r10
  {disp32} jbe ALLOC
C49:
  mov r10d, 6912
  cmp r9, r10
  {disp32} jbe ALLOC
C50:
  mov r10d, 8192
  cmp r9, r10
  {disp32} jbe ALLOC
C51:
  mov r10d, 9472
  cmp r9, r10
  {disp32} jbe ALLOC
C52:
  mov r10d, 9728
  cmp r9, r10
  {disp32} jbe ALLOC
C53:
  mov r10d, 10240
  cmp r9, r10
  {disp32} jbe ALLOC
C54:
  mov r10d, 10880
  cmp r9, r10
  {disp32} jbe ALLOC
C55:
  mov r10d, 12288
  cmp r9, r10
  {disp32} jbe ALLOC
C56:
  mov r10d, 13568
  cmp r9, r10
  {disp32} jbe ALLOC
C57:
  mov r10d, 14336
  cmp r9, r10
  {disp32} jbe ALLOC
C58:
  mov r10d, 16384
  cmp r9, r10
  {disp32} jbe ALLOC
C59:
  mov r10d, 18432
  cmp r9, r10
  {disp32} jbe ALLOC
C60:
  mov r10d, 19072
  cmp r9, r10
  {disp32} jbe ALLOC
C61:
  mov r10d, 20480
  cmp r9, r10
  {disp32} jbe ALLOC
C62:
  mov r10d, 21760
  cmp r9, r10
  {disp32} jbe ALLOC
C63:
  mov r10d, 24576
  cmp r9, r10
  {disp32} jbe ALLOC
C64:
  mov r10d, 27264
  cmp r9, r10
  {disp32} jbe ALLOC
C65:
  mov r10d, 28672
  cmp r9, r10
  {disp32} jbe ALLOC
C66:
  mov r10d, 32768
  cmp r9, r10
  {disp32} jbe ALLOC
  jmp LARGE
LARGE:
  lea r10, [r9+8191]
  shr r10, 13
  shl r10, 13
ALLOC:
  mov r11d, 0x400000
  mov r12, [r11]
  mov rdx, rbx
  sub rdx, rdi
  shl rdx, 3
  mov rdi, r12
  mov rsi, rax
  mov rcx, rdx
  test rcx, rcx
  jz DONE
  cmp rdi, rsi
  ja BWD
FWDREP:
  rep movsb
  jmp DONE
BWD:
  lea rdi, [rdi+rcx-1]
  lea rsi, [rsi+rcx-1]
  std
BWDREP:
  rep movsb
  cld
DONE:
  mov rdx, r10
  shl rdx, 4
  add rdx, r12
  mov [r11], rdx
  mov rax, r12
  mov rcx, r10
  shr rcx, 3
  ret
