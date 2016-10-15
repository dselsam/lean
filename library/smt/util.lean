set_option eqn_compiler.max_steps 10000

namespace list

private def withSepCore {X : Type} (f : X -> string) (sep : string) : bool -> list X -> string
| b [] := ""
| tt (x::xs) := f x ++ withSepCore ff xs
| ff (x::xs) := sep ++ f x ++ withSepCore ff xs

def withSep {X : Type} (f : X -> string) (sep : string) : list X -> string := withSepCore f sep tt

end list

namespace name

-- TODO(dhs): will need to get rid of unicode, and do other things as well
def toSMT : name → string
| anonymous                := "[anonymous]"
| (mk_string s anonymous)  := s
| (mk_numeral v anonymous) := v~>val~>to_string
| (mk_string s n)          := toSMT n ++ "__" ++ s
| (mk_numeral v n)         := toSMT n ++ "__" ++ v~>val~>to_string

end name

namespace level

@[reducible, pattern] definition one : level := succ zero
@[reducible, pattern] definition two : level := succ one

end level

namespace expr

@[reducible, pattern] meta def mk_Prop : expr := sort level.zero
@[reducible, pattern] meta def mk_Type : expr := sort level.one
@[reducible, pattern] meta def mk_Type₂ : expr := sort level.two

meta def toMaybeNat : expr → option (ℕ × expr)
| (app (app (const `zero _) ty) _) := some (0, ty)
| (app (app (const `one _)  ty) _)  := some (1, ty)
| (app (app (app (const `bit0 _) ty) _) e) := do n ← toMaybeNat e, return (2 * n~>fst, ty)
| (app (app (app (app (const `bit1 _) ty) _) _) e) := do n ← toMaybeNat e, return $ (2 * n~>fst + 1, ty)
| _ := none

inductive ConcreteArithType
| Int, Real
-- | BitVec : ℕ → ConcreteArithType -- TODO(dhs): mpq_macro doesn't support this yet

-- TODO(dhs): second arg is right now an encoding of ConcreteArithType
meta constant mkNumeralMacro : ℕ → expr → expr
-- TODO(dhs): note that environment is just for convenience to use the app-builder
-- could also make it a tactic
meta constant isNumeralMacro : environment → expr → option (ℕ × expr)

end expr

namespace lref
open expr tactic

meta def getUniqName (e : expr) : name := local_uniq_name e
meta def getPPName (e : expr) : name := local_pp_name e
meta def getType (e : expr) : tactic expr := infer_type e
meta def getValue (e : expr) : tactic (option expr) :=
  do v ← whnf_no_delta e, if v = e then return none else return (some v)

end lref

namespace tactic
open expr

meta def exprToNat : expr → tactic ℕ
| (app (app (const `zero _) _) _) := return 0
| (app (app (const `one _)  _) _)  := return 1
| (app (app (app (const `bit0 _) _) _) e) := do n ← exprToNat e, return (2 * n)
| (app (app (app (app (const `bit1 _) _) _) _) e) := do n ← exprToNat e, return $ 2 * n + 1
| e := fail $ "cannot parse number from '" ++ e~>to_string ++ "'"

meta def mkFreshNat : tactic ℕ :=
do (name.mk_numeral k _) ← mk_fresh_name | failed,
   return k~>val

meta def revertAll : tactic unit := local_context >>= revert_lst >> return ()

meta def introNot : tactic expr :=
do tgt ← target,
   match tgt with
   | (app (const `not []) e) := intro1
   | _                       := fail "target not an application of 'not'"
   end

end tactic
