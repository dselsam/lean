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

meta def localType : expr → expr
| (local_const _ _ _ ty) := ty
| _                      := default expr

meta def mkBinding (is_pi : bool) (e : expr) (locals : list expr) : expr :=
list.foldr (λ (l : expr) (e : expr),
               if is_pi
               then pi l~>local_uniq_name binder_info.default l~>localType e
               else lam l~>local_uniq_name binder_info.default l~>localType e)
           (abstract_locals e $ list.map local_uniq_name locals)
           locals

end expr

namespace tactic namespace smt

inductive ConcreteArithType
| Int, Real, nat
| BitVec : ℕ → ConcreteArithType -- TODO(dhs): mpq_macro doesn't support this yet

meta constant mkNumeralMacro : ℕ → ConcreteArithType → expr
meta constant isNumeralMacro : expr → option (ℕ × ConcreteArithType)

end smt end tactic

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

meta def mkFreshNamePrefix (s : string) : tactic name :=
do uniqId  ← mkFreshNat,
   return $ mk_simple_name $ "x_" ++ uniqId~>to_string

meta def mkFreshLocal (ty : expr) : tactic expr :=
do uniqId  ← mkFreshNat,
   n ← return $ mk_simple_name $ "local_" ++ uniqId~>to_string,
   return $ local_const n n binder_info.default ty

meta def revertAll : tactic unit := local_context >>= revert_lst >> return ()

meta def targetIsFalse : tactic unit :=
do tgt ← target,
   match tgt with
   | (const `false []) := skip
   | _                 := fail "target is not 'false'"
   end

meta def mkTargetFalse : tactic unit :=
 intros >> (targetIsFalse <|> by_contradiction `_SMT_negated_goal >> skip)

end tactic
