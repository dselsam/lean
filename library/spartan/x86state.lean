import .hsm
import algebra.ring

constants (uint32 : Type.{1}) (uint32_cr : comm_ring uint32) (uint32_de : decidable_eq uint32) (uint32_in : inhabited uint32)
attribute uint32_cr [instance]
attribute uint32_de [instance]
attribute uint32_in [instance]

constant (map : Π (A B : Type.{1}) [decidable_eq A] [inhabited A], Type.{1})
namespace map
constants (insert : Π {A B : Type.{1}} [decidable_eq A] [inhabited A], A → B → map A B → map A B)
constants (lookup : Π {A B : Type.{1}} [decidable_eq A] [inhabited A], A → map A B → B)

end map


inductive x86reg : Type.{1} := eax | ebx | edx
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

definition frame := map uint32 uint32

namespace x86
structure state := (regs : map x86reg uint32)
                   (stack : prod frame (list frame)) -- really just want non-empty list subtype
                   (heap : map uint32 uint32)

end x86

definition code [reducible] (A : Type) := HoareState x86.state A

open HS_defs

definition get_regs : code (map x86reg uint32) :=
HS.bind get (λ s, match s with x86.state.mk regs stack heap := HS.return regs end)

definition get_stack : code (prod frame (list frame)) :=
HS.bind get (λ s, match s with x86.state.mk regs stack heap := HS.return stack end)

definition get_stack_frame : code frame :=
HS.bind get_stack (λ stack, match stack with (fr, rest) := HS.return fr end)

definition get_heap : code (map uint32 uint32) :=
HS.bind get (λ s, match s with (x86.state.mk regs stack heap) := HS.return heap end)

----------------------------

definition get_reg (reg : x86reg) : code uint32 :=
  HS.bind get_regs (λ regs, HS.return $ map.lookup reg regs)

lemma get_reg_SPEC (s s' : x86.state) (out : uint32) (reg : x86reg) :
  HoareState.post (get_reg reg) s out s' = ∃ regs, HoareState.post get_regs s regs s ∧ out = map.lookup reg regs := sorry

definition get_mem_addr : maddr → code uint32
| (maddr.const u) := HS.return u
| (maddr.reg reg offset) := HS.bind (get_reg reg) (λ addr, HS.return $ addr + offset)

lemma get_mem_addr_SPEC (s s' : x86.state) (out : uint32) (addr : maddr) :
  HoareState.post (get_mem_addr addr) s out s' =
    (s = s') ∧ match addr with
                | (maddr.const u) := out = u
                | (maddr.reg reg offset) := HoareState.post (get_reg reg) s (out - offset) s
                end := sorry

definition get_stack_addr (k : uint32) : code uint32 :=
  HS.bind get_stack_frame (λ fr, HS.return $ map.lookup k fr)

definition eval_operand : operand → code uint32
| (operand.const u) := HS.return u
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
| (maddr.reg reg offset) := HS.bind (get_reg reg) (λ addr, modify (λ s,
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
  HS.bind (eval_operand src) (λ v, store_at_operand v dst)

definition add (dst src : operand) : code unit :=
HS.bind (eval_operand src)
        (λ increment, HS.bind
                      (eval_operand dst)
                      (λ old_value, store_at_operand (old_value + increment) dst))

end x86

namespace test

definition incr (op : operand) : code unit := x86.add op (operand.const 1)

lemma incr_actually_increments (s s' : x86.state) (op : operand) (pre_s : HoareState.pre (incr op) s) :
  HoareState.post (incr op) s unit.star s' →
    eval_state (eval_operand op) s' sorry = eval_state (eval_operand op) s sorry + 1
      := sorry

lemma incr_arbitrary_requires_ensures (s s' : x86.state) (op : operand) :
      HoareState.pre (incr op) s →
      eval_state (eval_operand op) s sorry = 10 → -- (arbitrary requires)
      /- (extra requires) ... → -/
      HoareState.post (incr op) s unit.star s' →
      eval_state (eval_operand op) s' sorry = 11 -- (arbitrary ensures)
      /- ∧ ... (extra ensures) ... -/ := sorry

end test
