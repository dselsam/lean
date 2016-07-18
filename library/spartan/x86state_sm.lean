import .sm
import algebra.ring

open monad.state

constants (uint32 : Type.{1}) (uint32_cr : comm_ring uint32) (uint32_de : decidable_eq uint32) (uint32_in : inhabited uint32)
          (bw_and bw_or bw_not bw_xor bw_ror32 : uint32 → uint32 → uint32) (bw_not32 : uint32 → uint32)
attribute uint32_cr [instance]
attribute uint32_de [instance]
attribute uint32_in [instance]

constant (map : Π (A B : Type.{1}) [decidable_eq A] [inhabited A], Type.{1})

namespace map
constants (insert : Π {A B : Type.{1}} [decidable_eq A] [inhabited A], A → B → map A B → map A B)
constants (lookup : Π {A B : Type.{1}} [decidable_eq A] [inhabited A], A → map A B → B)

end map

inductive x86reg : Type.{1} := eax | ebx | ecx | edx | edi | esi
definition x86reg_dec_eq [instance] : decidable_eq x86reg := sorry -- need 'deriving ...'!
definition x86reg_inhabited [instance] : inhabited x86reg := sorry -- need 'deriving ...'!

inductive maddr : Type.{1} :=
| const : uint32 → maddr
| reg : x86reg → uint32 → maddr

inductive operand : Type.{1} :=
| const : uint32 → operand
| reg : x86reg → operand
| heap : maddr → operand
| stack : uint32 → operand

definition operand_dec_eq [instance] : decidable_eq operand := sorry

definition frame := map uint32 uint32

namespace x86
structure state := (regs : map x86reg uint32)
                   (stack : prod frame (list frame)) -- really just want non-empty list subtype
                   (heap : map uint32 uint32)

end x86

definition code [reducible] (A : Type) := State x86.state A

definition get_regs : code (map x86reg uint32) :=
state.bind get (λ s, match s with x86.state.mk regs stack heap := state.ret regs end)

definition get_stack : code (prod frame (list frame)) :=
state.bind get (λ s, match s with x86.state.mk regs stack heap := state.ret stack end)

definition get_stack_frame : code frame :=
state.bind get_stack (λ stack, match stack with (fr, rest) := state.ret fr end)

definition get_heap : code (map uint32 uint32) :=
state.bind get (λ s, match s with (x86.state.mk regs stack heap) := state.ret heap end)

----------------------------

definition get_reg (reg : x86reg) : code uint32 :=
  state.bind get_regs (λ regs, state.ret $ map.lookup reg regs)

definition get_mem_addr : maddr → code uint32
| (maddr.const u) := state.ret u
| (maddr.reg reg offset) := state.bind (get_reg reg) (λ addr, state.ret $ addr + offset)

definition get_stack_addr (k : uint32) : code uint32 :=
  state.bind get_stack_frame (λ fr, state.ret $ map.lookup k fr)

definition eval_operand : operand → code uint32
| (operand.const u) := state.ret u
| (operand.reg r) := get_reg r
| (operand.stack saddr) := get_stack_addr saddr
| (operand.heap addr) := get_mem_addr addr

definition put_reg (v : uint32) (reg : x86reg) : code unit :=
  modify (λ s, match s with
               | (x86.state.mk regs stack heap) := x86.state.mk (map.insert reg v regs) stack heap
               end)

definition put_mem_addr (v : uint32) : maddr → code unit
| (maddr.const u) := modify (λ s, match s with
                                  | (x86.state.mk regs stack heap) := x86.state.mk regs stack (map.insert u v heap)
                                  end)
| (maddr.reg reg offset) := state.bind (get_reg reg) (λ addr, modify (λ s,
                                match s with
                                | (x86.state.mk regs stack heap) := x86.state.mk regs stack (map.insert (addr + offset) v heap)
                                end))

definition put_stack_addr (v : uint32) (saddr : uint32) : code unit :=
  modify (λ s, match s with
               | (x86.state.mk regs (fr, rest) heap) := x86.state.mk regs (map.insert saddr v fr, rest) heap
               end)

definition store_at_operand (v : uint32) : operand → code unit
| (operand.const u) := put_mem_addr v (maddr.const u)
| (operand.reg r) := put_reg v r
| (operand.stack saddr) := put_stack_addr v saddr
| (operand.heap addr) := put_mem_addr v addr

-- Instructions
-- The abstract "instruction" datatype will denote to these

namespace x86

definition mov (dst src : operand) : code unit :=
  state.bind (eval_operand src) (λ v, store_at_operand v dst)

definition update_bin (f : uint32 → uint32 → uint32) (dst src : operand) : code unit :=
do increment ← eval_operand src,
   old ← eval_operand dst,
   store_at_operand (f old increment) dst

definition update_un (f : uint32 → uint32) (dst : operand) : code unit :=
do old ← eval_operand dst,
   store_at_operand (f old) dst

definition add := update_bin add
definition and := update_bin bw_and
definition or := update_bin bw_or
definition xor := update_bin bw_xor

definition ror32 (dst : operand) (k : uint32) : code unit :=
do old ← eval_operand dst,
   store_at_operand (bw_ror32 old k) dst

definition not32 := update_un bw_not32
end x86

namespace test
open hoare

definition incr (op : operand) : code unit := x86.add op (operand.const 1)

lemma incr_actually_increments (s : x86.state) (op : operand) :
  HoareTriple (λ s, true) (incr op)
    (λ s a s',
    eval_state (eval_operand op) s' = eval_state (eval_operand op) s + 1
    ∧ ∀ op', op' ≠ op → eval_state (eval_operand op') s' = eval_state (eval_operand op') s) := sorry

lemma incr_actually_increments_alt (s : x86.state) (op : operand) :
  HoareTriple (λ s, true) (incr op)
    (λ s a s',
    ∀ op', eval_state (eval_operand op) s' =
      if op' = op then eval_state (eval_operand op) s + 1
                  else eval_state (eval_operand op) s) := sorry

end test

namespace test_sha256

notation x `:==` y := x86.mov x y
notation x `+=` y := x86.add x y
notation x `&=` y := x86.and x y
notation x `|=` y := x86.or x y
notation x `^=` y := x86.xor x y
notation `#` k := operand.stack k

--attribute operand.const [coercion]
attribute operand.reg [coercion]
open x86reg
open x86

-- Ignoring while loops and non-termination for now, it is easy to write down
-- the kind of assembly programs you are writing in Spartan.
-- Note that there is no post-processing here -- we have written down a computable functional program
-- Note: to extract the assembly program as opposed to the monadic computation, we need to reify the instructions
-- and then denote them, but we can use exactly the same syntax.
definition compute_one_step_noSHA (K : uint32) (W : operand) : code unit :=
let a := #0 in eax :== a

/-
let a := #0, b := #1, c := #2, d := #3, e := #4, f := #5, g := #6, h := #7,
    a' := #8, b' := #9, c' := #10, d' := #11, e' := #12, f' := #13, g' := #14, h' := #15
in do
   eax :== a,
   b' :== eax,
   ebx :== b,
   c' :== ebx,
   ecx :== c,
   edx :== ebx,

   ebx &= eax,
   edx &= ecx,
   ecx &= eax,
   ebx ^= ecx,
   ebx ^= ebx,

   -- calculate bsig0
   ecx :== eax,
   edx :== eax,
   ror32 edx 2,
   ror32 ecx 13,
   eax ^= ecx,
   ror32 edx 22,
   eax ^= edx,
   eax += ebx,

   -- calculate my_ch
   ebx :== e,
   f' :== ebx,
   edx :== ebx,
   not32 edx,
   ecx :== g,
   h' :== ecx,
   edx &= ecx,
   ecx :== f,
   g' :== ecx,
   ecx &= ebx,
   ecx ^= edx,

   -- calculate bsig1
   edx :== ebx,
   edi :== ebx,
   ror32 edx 6,
   edx ^= edi,
   ror32 ebx 25,
   edx ^= ebx,

   -- calculate T1
   ebx :== h,
   ebx += edx,
   ebx += ecx,
   ebx += operand.const K,
   ecx :== W,
   ebx += ecx,
   eax += ebx,
   a' :== eax,
   eax :== d,
   eax += ebx,
   e' :== eax
-/
/-
lemma compute_one_step_noSHA_SPEC
  : ∀ (K : uint32) (W : operand),
      ⦃ λ s, ∃ offset, W = operand.heap (maddr.reg esi offset) ⦄
      (compute_one_step_noSHA K W)
      ⦃ λ s a s', state.heap s = state.heap s' ∧ eval_operand esi s = eval_operand esi s' ⦄ := sorry
-/

end test_sha256
