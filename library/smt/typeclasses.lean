import smt.util smt.theory
set_option eqn_compiler.max_steps 10000

namespace tactic
namespace smt
open expr

private meta def strip : bool → expr → option expr
-- Int
| _ (app (app (const `zero _) (const `Int [])) _) := some $ (const `Int.zero [])
| _ (app (app (const `one _) (const `Int [])) _)  := some $ (const `Int.one [])

| _ (app (app (app (app (const `add _) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Int.add []) t₁) t₂)
| _ (app (app (app (app (const `mul _) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Int.mul []) t₁) t₂)
| _ (app (app (app (app (const `sub _) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Int.sub []) t₁) t₂)
| _ (app (app (app (app (const `div _) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Int.div []) t₁) t₂)
| _ (app (app (app (app (const `lt _) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Int.lt []) t₁) t₂)
| _ (app (app (app (app (const `le _) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Int.le []) t₁) t₂)
| _ (app (app (app (app (const `gt _) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Int.lt []) t₂) t₁)
| _ (app (app (app (app (const `ge _) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Int.le []) t₂) t₁)

-- Real
| _ (app (app (const `zero _) (const `Real [])) _) := some $ (const `Real.zero [])
| _ (app (app (const `one _) (const `Real [])) _)  := some $ (const `Real.one [])

| _ (app (app (app (app (const `add _) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Real.add []) t₁) t₂)
| _ (app (app (app (app (const `mul _) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Real.mul []) t₁) t₂)
| _ (app (app (app (app (const `sub _) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Real.sub []) t₁) t₂)
| _ (app (app (app (app (const `div _) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Real.div []) t₁) t₂)
| _ (app (app (app (app (const `lt _) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Real.lt []) t₁) t₂)
| _ (app (app (app (app (const `le _) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Real.le []) t₁) t₂)
| _ (app (app (app (app (const `gt _) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Real.lt []) t₂) t₁)
| _ (app (app (app (app (const `ge _) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some (app (app (const `Real.le []) t₂) t₁)

-- BitVec
| _ (app (app (const `zero _) (app (const `BitVec []) e)) _) := some $ app (const `BitVec.zero []) e
| _ (app (app (const `one _) (app (const `BitVec []) e)) _)  := some $ app (const `BitVec.one []) e

| _ (app (app (app (app (const `add _) (app (const `BitVec []) e)) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some $ app (app (app (const `BitVec.add []) e) t₁) t₂
| _ (app (app (app (app (const `mul _) (app (const `BitVec []) e)) _) e₁) e₂) :=
       do t₁ ← strip tt e₁, t₂ ← strip tt e₂, some $ app (app (app (const `BitVec.mul []) e) t₁) t₂

-- Numerals
| b e := match toMaybeNat e with
         | some (n, const `Int []) := some $ mkNumeralMacro n ConcreteArithType.Int
         | some (n, const `Real []) := some $ mkNumeralMacro n ConcreteArithType.Real
         | some (n, app (const `BitVec []) k) := match toMaybeNat k with
                                                 | some (v, const `nat []) := some $ mkNumeralMacro n (ConcreteArithType.BitVec v)
                                                 | _ := none
                                                 end
         | _ :=
         match b with
         | ff := none
         | tt := some e
         end
         end

meta def stripTypeclasses : tactic unit :=
do tgt ← target,
   change $ replace tgt (λ (e : expr) (depth : nat), strip ff e)

end smt
end tactic
