import .sm .util
import algebra.ring

namespace x86

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

definition sframe [reducible] := map uint32 uint32
definition gframe [reducible] := map uint32 uint32

structure state := (regs : map reg uint32)
                   (stack : list sframe)
                   (heap : map uint32 uint32)
                   (ghost : list gframe)

namespace fields
definition regs : state → map reg uint32
| (state.mk rgs _ _ _) := rgs

definition stack : state → list sframe
| (state.mk _ st _ _) := st

definition heap : state → map uint32 uint32
| (state.mk _ _ h _) := h

definition ghost : state → list gframe
| (state.mk _ _ _ g) := g

end fields


end x86

namespace prog
open x86

inductive instruction :=
| mov32 : operand → operand → instruction
| add32 : operand → operand → instruction
| and32 : operand → operand → instruction

inductive ocmp := OEq | OLe

inductive obool :=
| OCmp : ocmp → operand → operand → obool

inductive code :=
| sline : list instruction → code
| ite : obool → code → code → code
| while : obool → code → code
| call : code → code -- pushes onto the ghost stack
-- | block : list code → code

definition prog := list code

end prog


namespace x86_sm
open monad.state
open x86

definition get_reg (rg : reg) : State state uint32 :=
do ov ← gets (map.lookup rg ∘ fields.regs),
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
   | (list.cons fr frs) := match map.lookup k fr with
                           | (some v) := return v
                           | none := fail
                           end
   | list.nil := fail
   end

definition get_ghost_addr (k : uint32) : State state uint32 :=
do st ← gets fields.ghost,
   match st with
   | (list.cons fr frs) := match map.lookup k fr with
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
               | (state.mk regs stack heap ghost) := state.mk (map.insert rg v regs) stack heap ghost
               end)

definition put_mem_addr (v : uint32) : maddr → State state unit
| (maddr.const u) := modify (λ s, match s with
                                  | (state.mk regs stack heap ghost) := state.mk regs stack (map.insert u v heap) ghost
                                  end)
| (maddr.reg rg offset) := do addr ← get_reg rg,
                              modify (λ s, match s with
                                           | (state.mk regs stack heap ghost) := state.mk regs stack (map.insert (addr + offset) v heap) ghost
                                           end)

set_option unifier.conservative true
set_option pp.implicit true

definition put_stack_addr (v : uint32) (saddr : uint32) : State state unit :=
bind get (λ s,
   match s with
   | (state.mk regs st heap ghost) :=
                   match st with
                   | (list.cons fr frs) := put $ state.mk regs (list.cons (map.insert saddr v fr) frs) heap ghost
                   | list.nil := fail
                   end
   end)

print monad.bind
definition put_ghost_addr (v : uint32) (gaddr : uint32) : State state unit :=
/-
bind get (λ s,
   match s with
   | (state.mk regs st heap ghost) :=
                   match ghost with
                   | (list.cons fr frs) := put $ state.mk regs st heap (list.cons (map.insert gaddr v fr) frs)
                   | list.nil := fail
                   end
   end)
-/
do s ← get,
   match s with
   | (state.mk regs st heap ghost) :=
                   match st with
                   | (list.cons fr frs) := return unit.star --put $ state.mk regs (list.cons (map.insert saddr v fr) frs) heap ghost
                   | list.nil := fail
                   end
   end

definition store_at_operand (v : uint32) : operand → State state unit
| (operand.const u) := put_mem_addr v (maddr.const u)
| (operand.reg r) := put_reg v r
| (operand.stack saddr) := put_stack_addr v saddr
| (operand.heap addr) := put_mem_addr v addr
| (operand.ghost gaddr) := put_ghost_addr v gaddr

end x86_sm

open monad.state
