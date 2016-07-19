import .sm .util
import algebra.ring

namespace x86
namespace basic

inductive reg := eax | ebx | ecx | edx | edi | esi
definition reg_dec_eq [instance] : decidable_eq reg := sorry -- need 'deriving ...'!

inductive maddr :=
| const : uint32 → maddr
| reg : reg → uint32 → maddr

inductive operand :=
| const : uint32 → operand
| reg : reg → operand
| heap : maddr → operand
| stack : uint32 → operand
| ghost : uint32 → operand

definition operand_dec_eq [instance] : decidable_eq operand := sorry

definition sframe [reducible] := Map uint32 uint32
definition gframe [reducible] := Map uint32 uint32 -- do they really need to store { T : Type, T }?

structure state := (regs : Map reg uint32)
                   (stack : list sframe)
                   (heap : Map uint32 uint32)
                   (ghost : list gframe)

end basic
open basic

namespace fields
definition regs : state → Map reg uint32
| (state.mk rgs _ _ _) := rgs

definition stack : state → list sframe
| (state.mk _ st _ _) := st

definition heap : state → Map uint32 uint32
| (state.mk _ _ h _) := h

definition ghost : state → list gframe
| (state.mk _ _ _ g) := g

end fields

namespace prog

inductive instruction :=
| mov32 : operand → operand → instruction
| add32 : operand → operand → instruction
| and32 : operand → operand → instruction

namespace instruction end instruction -- Need to do this to open it?

inductive ocmp := OEq | OLe

inductive obool :=
| mk : ocmp → operand → operand → obool

inductive code :=
| sline : list instruction → code
| ite : obool → code → code → code
| while : obool → code → code
| call : code → code -- pushes onto the ghost stack
-- | block : list code → code

definition prog := list code

end prog

namespace primitives
open monad.state

definition get_reg (rg : reg) : State state uint32 :=
do ov ← gets (Map.lookup rg ∘ fields.regs),
   match ov with
   | (some k) := return k
   | none := fail
   end

definition get_mem_addr : maddr → State state uint32
| (maddr.const u) := return u
| (maddr.reg rg offset) := do addr ← get_reg rg, return $ addr + offset

definition get_stack_addr (k : uint32) : State state uint32 :=
do st ← gets fields.stack,
   match st with
   | (list.cons fr frs) := match Map.lookup k fr with
                           | (some v) := return v
                           | none := fail
                           end
   | list.nil := fail
   end

definition get_ghost_addr (k : uint32) : State state uint32 :=
do st ← gets fields.ghost,
   match st with
   | (list.cons fr frs) := match Map.lookup k fr with
                           | (some v) := return v
                           | none := fail
                           end
   | list.nil := fail
   end

definition eval_operand : operand → State state uint32
| (operand.const u) := return u
| (operand.reg rg) := get_reg rg
| (operand.stack saddr) := get_stack_addr saddr
| (operand.heap addr) := get_mem_addr addr
| (operand.ghost gaddr) := get_ghost_addr gaddr

definition put_reg (v : uint32) (rg : reg) : State state unit :=
  modify (λ s, match s with
               | (state.mk regs stack heap ghost) := state.mk (Map.insert rg v regs) stack heap ghost
               end)

definition put_mem_addr (v : uint32) : maddr → State state unit
| (maddr.const u) := modify (λ s, match s with
                                  | (state.mk regs stack heap ghost) := state.mk regs stack (Map.insert u v heap) ghost
                                  end)
| (maddr.reg rg offset) := do addr ← get_reg rg,
                              modify (λ s, match s with
                                           | (state.mk regs stack heap ghost) := state.mk regs stack (Map.insert (addr + offset) v heap) ghost
                                           end)

definition put_stack_addr (v : uint32) (saddr : uint32) : State state unit :=
bind get $ λ s,
   match s with
   | (state.mk regs st heap ghost) :=
                   match st with
                   | (list.cons fr frs) := put $ state.mk regs (list.cons (Map.insert saddr v fr) frs) heap ghost
                   | list.nil := fail
                   end
   end

definition put_ghost_addr (v : uint32) (gaddr : uint32) : State state unit :=
bind get $ λ s,
   match s with
   | (state.mk regs st heap ghost) :=
                   match ghost with
                   | (list.cons fr frs) := put $ state.mk regs st heap (list.cons (Map.insert gaddr v fr) frs)
                   | list.nil := fail
                   end
   end

definition store_at_operand (v : uint32) : operand → State state unit
| (operand.const u) := put_mem_addr v (maddr.const u)
| (operand.reg r) := put_reg v r
| (operand.stack saddr) := put_stack_addr v saddr
| (operand.heap addr) := put_mem_addr v addr
| (operand.ghost gaddr) := put_ghost_addr v gaddr

definition ghost_tainted : operand → operand → Prop
| (operand.ghost g₁) (operand.ghost g₂) := false
| (operand.ghost g₁) o₂ := true
| o₁ (operand.ghost g₂) := true
| o₁ o₂ := false

definition ghost_tainted_dec_eq [instance] : decidable_rel ghost_tainted := sorry

definition push_gframe : state → state
| (state.mk regs st heap ghost) := state.mk regs st heap (list.cons Map.empty ghost)

definition pop_gframe : state → option state
| (state.mk regs st heap ghost) := match ghost with
                                   | list.nil := none
                                   | (list.cons fr frs) := some $ state.mk regs st heap frs
                                   end

definition update_bin (f : uint32 → uint32 → uint32) (dst src : operand) : State state unit :=
if ghost_tainted dst src then fail else
do increment ← eval_operand src,
   old ← eval_operand dst,
   store_at_operand (f old increment) dst

definition update_un (f : uint32 → uint32) (dst : operand) : State state unit :=
do old ← eval_operand dst,
   store_at_operand (f old) dst

end primitives

namespace denotation
open prog
open prog.instruction
open prog.ocmp
open primitives
open monad.state

definition denote_ocmp : ocmp → (uint32 → uint32 → Prop)
| OEq := λ v₁ v₂, v₁ = v₂
| OLe := λ v₁ v₂, v₁ ≤ v₂

definition denote_ocmp_dec_eq [instance] (cmp : ocmp) : decidable_rel (denote_ocmp cmp) := sorry

definition eval_obool : obool → State state bool
| (obool.mk cmp o₁ o₂) := do v₁ ← eval_operand o₁,
                             v₂ ← eval_operand o₂,
                             if (denote_ocmp cmp v₁ v₂) then return tt else return ff

definition denote_instruction : instruction → State state unit
| (mov32 dst src) := update_bin (λ x y, y) dst src
| (add32 dst src) := update_bin add dst src
| (and32 dst src) := update_bin bw_and dst src

end denotation

namespace interpret
open prog
open prog.code
open denotation
open monad.state
open list
open primitives

inductive evals_to : code → state → state → Prop :=
| eval_sline : Π (ins : list instruction) (s s' : state),
                 exec_state (sequence ∘ map denote_instruction $ ins) s = some s' →
                 evals_to (sline ins) s s'
| eval_ite_true : Π (test : obool) (cthen celse : code) (s s' : state),
                  eval_state (eval_obool test) s = some tt →
                  evals_to cthen s s'→
                  evals_to (ite test cthen celse) s s'
| eval_ite_false : Π (test : obool) (cthen celse : code) (s s' : state),
                   eval_state (eval_obool test) s = some ff →
                   evals_to celse s s'→
                   evals_to (ite test cthen celse) s s'

| eval_while_true : Π (test : obool) (cbody : code) (s : state),
                    eval_state (eval_obool test) s = some tt →
                    evals_to (while test cbody) s s
| eval_while_false : Π (test : obool) (cbody : code) (s s' s'' : state),
                     eval_state (eval_obool test) s = some ff →
                     evals_to cbody s s' →
                     evals_to (while test cbody) s' s'' →
                     evals_to (while test cbody) s s''

| eval_call : ∀ (c : code) (s s' s'' : state),
              pop_gframe s' = some s'' → -- here only because of ordering req
              evals_to c (push_gframe s) s' →
              evals_to (call c) s s''

end interpret



end x86
