import smt.util smt.theory smt.core

namespace tactic
namespace smt
open expr

meta def collectLocals : expr → list expr
| (app f arg)                := list.union (collectLocals f) (collectLocals arg)
| (lam n bi dom bod)         := list.union (collectLocals dom) (collectLocals bod)
| (pi n bi dom bod)          := list.union (collectLocals dom) (collectLocals bod)
| (elet n ty val bod)        := list.union (list.union (collectLocals ty) (collectLocals val)) (collectLocals bod)
| (local_const n pp_n bi ty) := (local_const n pp_n bi ty) :: collectLocals ty
| (mvar n ty)                := collectLocals ty
| _                          := []

meta def liftLambdasHyp : expr → tactic expr
| (elet n ty val bod) :=
    do arity ← get_pi_arity ty,
       match arity with
       | 0 := -- if it is not a function, we keep it as a let
           do ty' ← liftLambdasHyp ty,
              val' ← liftLambdasHyp val,
              l    ← mkFreshLocal ty',
              liftedBod ← liftLambdasHyp $ instantiate_var bod l,
              bod' ← return $ abstract_local liftedBod (local_uniq_name l),
              return $ elet n ty' val' bod'
       | _ :=
         do localsInVal ← return $ collectLocals val,
            hyps ← local_context,
            localsToAbstract ← return $ list.filter (λ x, x ∉ hyps) localsInVal,
            newTy ← return $ mkBinding tt ty localsToAbstract,
            newVal ← return $ mkBinding ff val localsToAbstract,
            definev n newTy newVal,
            newFn ← get_local n,
            liftLambdasHyp $ instantiate_var bod (app_of_list newFn localsToAbstract)
       end

| (app f arg)                := do f' ← liftLambdasHyp f,
                                   arg' ← liftLambdasHyp arg,
                                   return $ app f' arg'

| (pi n bi dom bod)         := do dom' ← liftLambdasHyp dom,
                                   ln    ← mkFreshNamePrefix "_local_",
                                   l    ← return $ local_const ln ln bi dom,
                                   bod' ← liftLambdasHyp (instantiate_var bod l),
                                   return $ pi n bi dom' (abstract_local bod' ln)

| (lam n bi dom bod)         := do dom' ← liftLambdasHyp dom,
                                   ln    ← mkFreshNamePrefix "_local_",
                                   l    ← return $ local_const ln ln bi dom,
                                   bod' ← liftLambdasHyp (instantiate_var bod l),
                                   return $ lam n bi dom' (abstract_local bod' ln)

| e := return e

private meta def liftLambdasCore : unit → tactic unit
| _ :=
do tgt ← target,
   match tgt with
   | (pi n bi dom bod) :=
         do dom' ← liftLambdasHyp dom,
            change $ pi n bi dom' bod,
            intro1,
            liftLambdasCore ()
   | _ := revertAll
   end

meta def liftLambdas : tactic unit := liftLambdasCore ()

end smt
end tactic
