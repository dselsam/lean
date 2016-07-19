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

definition X86State [reducible] := monad.state.FState state

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
| assert : X86State bool → instruction -- TODO tricky to use decidable here

--namespace instruction end instruction -- Need to do this to open it?

inductive ocmp := OEq | OLe

inductive obool :=
| mk : ocmp → operand → operand → obool

inductive code :=
| sline : list instruction → code
| ifte : obool → code → code → code
| while : obool → X86State bool → code → code
| call : code → code -- pushes onto the ghost stack
| seq : code → code → code
-- | block : list code → code

definition code_dec_eq [instance] : decidable_eq code := sorry

definition prog := list code

end prog

namespace primitives
open monad.state

definition get_reg (rg : reg) : X86State uint32 :=
do ov ← gets (Map.lookup rg ∘ fields.regs),
   match ov with
   | (some k) := return k
   | none := fail
   end

definition get_mem_addr : maddr → X86State uint32
| (maddr.const u) := return u
| (maddr.reg rg offset) := do addr ← get_reg rg, return $ addr + offset

definition get_stack_addr (k : uint32) : X86State uint32 :=
do st ← gets fields.stack,
   match st with
   | (list.cons fr frs) := match Map.lookup k fr with
                           | (some v) := return v
                           | none := fail
                           end
   | list.nil := fail
   end

definition get_ghost_addr (k : uint32) : X86State uint32 :=
do st ← gets fields.ghost,
   match st with
   | (list.cons fr frs) := match Map.lookup k fr with
                           | (some v) := return v
                           | none := fail
                           end
   | list.nil := fail
   end

definition eval_operand : operand → X86State uint32
| (operand.const u) := return u
| (operand.reg rg) := get_reg rg
| (operand.stack saddr) := get_stack_addr saddr
| (operand.heap addr) := get_mem_addr addr
| (operand.ghost gaddr) := get_ghost_addr gaddr

definition put_reg (v : uint32) (rg : reg) : X86State unit :=
  modify (λ s, match s with
               | (state.mk regs stack heap ghost) := state.mk (Map.insert rg v regs) stack heap ghost
               end)

definition put_mem_addr (v : uint32) : maddr → X86State unit
| (maddr.const u) := modify (λ s, match s with
                                  | (state.mk regs stack heap ghost) := state.mk regs stack (Map.insert u v heap) ghost
                                  end)
| (maddr.reg rg offset) := do addr ← get_reg rg,
                              modify (λ s, match s with
                                           | (state.mk regs stack heap ghost) := state.mk regs stack (Map.insert (addr + offset) v heap) ghost
                                           end)

definition put_stack_addr (v : uint32) (saddr : uint32) : X86State unit :=
bind get $ λ s,
   match s with
   | (state.mk regs st heap ghost) :=
                   match st with
                   | (list.cons fr frs) := put $ state.mk regs (list.cons (Map.insert saddr v fr) frs) heap ghost
                   | list.nil := fail
                   end
   end

definition put_ghost_addr (v : uint32) (gaddr : uint32) : X86State unit :=
bind get $ λ s,
   match s with
   | (state.mk regs st heap ghost) :=
                   match ghost with
                   | (list.cons fr frs) := put $ state.mk regs st heap (list.cons (Map.insert gaddr v fr) frs)
                   | list.nil := fail
                   end
   end

definition store_at_operand (v : uint32) : operand → X86State unit
| (operand.const u) := put_mem_addr v (maddr.const u)
| (operand.reg r) := put_reg v r
| (operand.stack saddr) := put_stack_addr v saddr
| (operand.heap addr) := put_mem_addr v addr
| (operand.ghost gaddr) := put_ghost_addr v gaddr

definition ghost_tainted : operand → operand → Prop
| (operand.ghost g₁) o₂ := false
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

definition update_bin (f : uint32 → uint32 → uint32) (dst src : operand) : X86State unit :=
if ghost_tainted dst src then fail else
do increment ← eval_operand src,
   old ← eval_operand dst,
   store_at_operand (f old increment) dst

definition update_un (f : uint32 → uint32) (dst : operand) : X86State unit :=
do old ← eval_operand dst,
   store_at_operand (f old) dst


definition guard (p : Prop) [decidable p] : X86State unit :=
if p then return unit.star else fail

definition gassert (pred : X86State bool) : X86State unit :=
do old_s ← get, b ← pred, guard (b = tt), put old_s

definition is_ghost : operand → Prop
| (operand.ghost gaddr) := true
| _ := false

definition is_ghost_dec_eq [instance] : decidable_pred (is_ghost) := sorry

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

definition eval_obool : obool → X86State bool
| (obool.mk cmp o₁ o₂) := if is_ghost o₁ ∨ is_ghost o₂ then fail else do
                             v₁ ← eval_operand o₁,
                             v₂ ← eval_operand o₂,
                             if (denote_ocmp cmp v₁ v₂) then return tt else return ff

definition denote_instruction : instruction → X86State unit
| (mov32 dst src) := update_bin (λ x y, y) dst src
| (add32 dst src) := update_bin add dst src
| (and32 dst src) := update_bin bw_and dst src
| (assert pred) := gassert pred

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
| eval_ifte_true : Π (test : obool) (cthen celse : code) (s s' : state),
                  eval_state (eval_obool test) s = some tt →
                  evals_to cthen s s'→
                  evals_to (ifte test cthen celse) s s'
| eval_ifte_false : Π (test : obool) (cthen celse : code) (s s' : state),
                   eval_state (eval_obool test) s = some ff →
                   evals_to celse s s'→
                   evals_to (ifte test cthen celse) s s'
| eval_while_true : Π (test : obool) (invar : X86State bool) (cbody : code) (s s' s'': state),
                    eval_state invar s = some tt → -- TODO does this make sense? the program only evals if the given loop invaniant is correct?
                    eval_state (eval_obool test) s = some tt →
                    evals_to cbody s s' →
                    evals_to (while test invar cbody) s' s'' →
                    evals_to (while test invar cbody) s s''
| eval_while_false : Π (test : obool) (invar : X86State bool) (cbody : code) (s : state),
                     eval_state invar s = some tt →
                     eval_state (eval_obool test) s = some ff →
                     evals_to (while test invar cbody) s s
| eval_call : Π (c : code) (s s' s'' : state),
              pop_gframe s' = some s'' → -- here only because of ordering req
              evals_to c (push_gframe s) s' →
              evals_to (call c) s s''
| eval_seq : Π (c₁ c₂ : code) (s s' s'' : state),
               evals_to c₁ s s' →
               evals_to c₂ s' s'' →
               evals_to (seq c₁ c₂) s s''

end interpret

namespace compile
open basic
open basic.reg
open prog
open prog.code
open prog.instruction
open primitives
open basic.operand
attribute operand.reg [coercion]
open monad.state
open list
open denotation
open interpret

definition is_computational : instruction → Prop
| (mov32 dst src) := not (is_ghost dst) ∧ not (is_ghost src)
| (add32 dst src) := not (is_ghost dst) ∧ not (is_ghost src)
| (and32 dst src) := not (is_ghost dst) ∧ not (is_ghost src)
| (assert pred) := false

definition is_computational_dec_eq [instance] : decidable_pred is_computational := sorry

definition erase_noncomputational : code → code
| (sline ins) := sline (filter is_computational ins)
| (ifte ob cthen celse) := ifte ob (erase_noncomputational cthen) (erase_noncomputational celse)
| (while ob invar cbody) := while ob invar (erase_noncomputational cbody)
| (call c) := erase_noncomputational c
| (seq c₁ c₂) := let c₁' := erase_noncomputational c₁, c₂' := erase_noncomputational c₂ in
                 if c₁' = sline [] then c₂' else
                 if c₂' = sline [] then c₁' else seq c₁' c₂'


end compile

namespace examples1
open basic
open basic.reg
open prog
open prog.code
open prog.instruction
open primitives
open basic.operand
attribute operand.reg [coercion]
open monad.state
open list
open denotation
open interpret
open compile

definition s₀ : state := state.mk Map.empty [Map.empty] Map.empty [Map.empty]

definition runs_safely (prog : X86State unit) (s : state) : Prop := match exec_state prog s with
                                                                    | (some s') := true
                                                                    | none := false
                                                                    end
set_option unifier.conservative true

definition code1 : list instruction :=
 [
  mov32 eax (operand.const 1),
  mov32 (ghost 0) (operand.const 10),
  assert $ do
    u ← eval_operand eax,
    g ← eval_operand (ghost 0),
    return $ to_bool (g = 10 * u)
]

lemma code1_runs : runs_safely (sequence ∘ map denote_instruction $ code1) s₀ := sorry -- should be rfl once decidable-eqs are filled in
lemma code1_compiled : erase_noncomputational (sline code1) = sline [mov32 eax (operand.const 1)] := sorry -- rfl

definition code2 : list instruction :=
[
  mov32 eax (operand.const 1),
  add32 eax eax,

  mov32 (ghost 0) (operand.const 10),
  add32 (ghost 0) (ghost 0),

  assert $ do
    u ← eval_operand eax,
    g ← eval_operand (ghost 0),
    return $ to_bool (g = 10 * u)
]

lemma code2_runs : runs_safely (sequence ∘ map denote_instruction $ code2) s₀ := sorry -- should be rfl once decidable-eqs are filled in
lemma code2_always_runs : ∀ s, runs_safely (sequence ∘ map denote_instruction $ code2) s := sorry

definition code3 : code :=
  -- mov eax 10, mov ebx 10, if eax == ebx then mov edx 100 else mov ecx 100
  seq (sline [mov32 eax (operand.const 10), mov32 ebx (operand.const 10)]) (ifte (obool.mk ocmp.OEq eax ebx) (sline [mov32 edx (operand.const 100)]) (sline [mov32 ecx (operand.const 100)]))

-- TODO need more here -- code3 must run safely, and the evaling-operands must run safely as well (always the case)
lemma code3_sets_ebx_to_1 : ∀ s s', evals_to code3 s s' → eval_state (eval_operand ebx) s' = eval_state (eval_operand eax) s' := sorry

end examples1




end x86
