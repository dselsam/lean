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

definition frame := map uint32 uint32

structure state := (regs : map reg uint32)
                   (stack : list (map uint32 uint32))
                   (heap : map uint32 uint32)
                   (ghost : list (map ℕ uint32))

end x86

open x86

namespace prog

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

open prog

namespace x86



end x86

open monad.state





/-



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
-/
