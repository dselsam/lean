import algebra.ring
constants (uint32 : Type.{1}) (uint32_cr : comm_ring uint32) (uint32_de : decidable_eq uint32)
attribute uint32_cr [instance]
attribute uint32_de [instance]

namespace monad
namespace state

definition State (S A : Type) := S → prod A S
variable {S : Type}
namespace state

definition fmap : Π {A B : Type}, (A → B) → State S A → State S B :=
  λ (A B : Type) (f : A → B) (P : S → prod A S) (s : S),
     match P s with
     | (a, s') := (f a, s')
     end

definition ret : Π {A : Type}, A → State S A :=
  λ (A : Type) (a : A) (s : S), (a, s)

definition bind : Π {A B : Type}, State S A → (A → State S B) → State S B :=
  λ (A B : Type) (P₁ : State S A) (P₂ : A → State S B) (s₁ : S),
    match P₁ s₁ with
    | (a, s₂) := P₂ a s₂
    end
end state

definition is_monad [instance] : monad (State S) :=
monad.mk (@state.fmap S) (@state.ret S) (@state.bind S)

definition get : State S S := λ (s : S), (s, s)
definition put (s_new : S) : State S unit := λ (s : S), (unit.star, s_new)
definition modify (f : S → S) : State S unit := state.bind get put -- elaborator is nuts
definition run_state {A : Type} (P : State S A) (s : S) : prod A S := P s
definition eval_state {A : Type} (P : State S A) (s₁ : S) : A := match P s₁ with
                                                                | (a, s₂) := a
                                                                end

definition exec_state {A : Type} (P : State S A) (s₁ : S) : S := match P s₁ with
                                                                | (a, s₂) := s₂
                                                                end

end state
end monad

definition map.insert {A B : Type} [decidable_eq A] (a₁ : A) (b : B) (f : A → B) : A → B := sorry
--  λ (a₂ : A), if a₁ == a₂ then b else f a₂ -- wtf? can't synthesize unless I spell it out

open monad.state

namespace spartan

inductive x64reg : Type.{1} := eax | ebx | edx
definition x64reg_dec_eq [instance] : decidable_eq x64reg := sorry

inductive maddr : Type.{1} :=
| const : uint32 → maddr
| reg : x64reg → uint32 → maddr

inductive operand : Type.{1} :=
| const : uint32 → operand
| reg : x64reg → operand
| heap : maddr → operand
--| stack : uint32 → operand

definition frame := list uint32
structure state := (regs : x64reg → uint32)
                   (heap : uint32 → uint32)
--                   (stack : list frame)

definition code [reducible] (A : Type) := State state A

definition get_reg (reg : x64reg) : code uint32 :=
  state.bind get (λ (s : state),
                      match s with
                      | state.mk regs heap := return $ regs reg
                      end)

definition get_mem_addr : maddr → code uint32
| (maddr.const u) := return u
| (maddr.reg reg offset) := state.bind (get_reg reg) (λ addr, return $ addr + offset)

definition eval_operand : operand → code uint32
| (operand.const u) := return u
| (operand.reg r) := get_reg r
| (operand.heap addr) := get_mem_addr addr
-- | (operand.stack k) := (preconditions? dependent types?)


definition put_reg (v : uint32) (reg : x64reg) : code unit :=
  state.bind get (λ (s : state),
                      match s with
                      | state.mk regs heap := put $ state.mk (map.insert reg v regs) heap
                      end)

definition put_mem_addr (v : uint32) : maddr → code unit
| (maddr.const u) := state.bind get (λ (s : state),
                       match s with
                       | state.mk regs heap := put $ state.mk regs (map.insert u v heap)
                       end)
| (maddr.reg reg offset) := state.bind get (λ (s : state), state.bind (get_reg reg)
                              (λ addr,
                                match s with
                                | state.mk regs heap := put $ state.mk regs (map.insert (addr + offset) v heap)
                                end))

definition store_at_operand (v : uint32) : operand → code unit
| (operand.const u) := put_mem_addr v (maddr.const u)
| (operand.reg r) := put_reg v r
| (operand.heap addr) := put_mem_addr v addr

definition instruction := code unit -- not all [code unit] are "instructions"

definition mov (dst src : operand) : instruction :=
  state.bind (eval_operand src) (λ v, store_at_operand v dst)

definition add (dst src : operand) : instruction :=
state.bind
(eval_operand src) (λ increment, state.bind
(eval_operand dst) (λ old_value, store_at_operand (old_value + increment) dst))

end spartan

open spartan

namespace test
definition incr (op : operand) : code unit := add op (operand.const 1)
definition wrap_incr (op : operand) (k : uint32) : code unit :=
state.bind (incr op)
(λ ignore₁, state.bind (add op (operand.const k))
(λ ignore₂, mov (operand.reg x64reg.edx) op))

lemma incr_correct : ∀ (s : state) (op : operand),
  eval_state (eval_operand op) (exec_state (incr op) s) == eval_state (eval_operand op) s + 1 := sorry

-- TODO(dhs): hoare state monad!



end test
