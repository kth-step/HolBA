open HolKernel boolLib liteLib simpLib Parse bossLib;


structure bir_scamv_driverLib =
struct

(*
 workflow:
 - (a) program generation
 - lifting
 - (b) obs model augmentation
 - symbolic execution
 - conversion to symbolic observation paths (n paths)
 - relation synthesis
 - (c) relation partitioning (m partitions)
 - somewhere around here: constraining memory accesses (and probably some registers or flags) for test setup
 - state generation using SMT solver
 - test execution
 - driver decision (jump to a, b or c)
 *)

(*
 https://static.docs.arm.com/100898/0100/the_a64_Instruction_set_100898_0100.pdf
 https://www.element14.com/community/servlet/JiveServlet/previewBody/41836-102-1-229511/ARM.Reference_Manual.pdf
 http://infocenter.arm.com/help/topic/com.arm.doc.dui0801d/dom1359731161338.html
 *)


(*
 example entropy-paper0:
      b.eq l2
      mul x1, x2, x3
  l2: ldr x2, [x1, #8]

 models:
  (if sharedline(x) then tag(x)),
  (tag(x)),
  (if sharedline(x) then x)
 *)

(*
 example entropy-paper1:
      cmp x2, x3
      b.lo lb
      add x1, x2, x3
  lb: ldr x2, [x1]
 *)

(*
 example ld-ld:
  ldr x3, [x1]
  ldr x4, [x2]
 models:
  (cache line(x)),
  (cache line(x), tag(x))
 input:
  ((0,0), (0,cache size))
 *)


end;



