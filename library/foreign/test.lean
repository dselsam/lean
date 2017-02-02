import foreign.eigen icml2017.certigrad.tmath icml2017.certigrad.compute_grad

meta def approx_name : name → name
| `certigrad       := `certigrad.approx
| (name.mk_string s p)  :=  name.mk_string s (approx_name p)
| (name.mk_numeral s p) :=  name.mk_numeral s (approx_name p)
| anonymous := anonymous

meta def names_to_approx : list name :=
  [ /- RNG -/
    `certigrad.RNG,
    `certigrad.RNG.to_string,
    `certigrad.RNG.has_to_string,
    `certigrad.RNG.mk,
    /- T -/
    `certigrad.TShape,
    `certigrad.T,
    `certigrad.T.to_string,
    `certigrad.T.has_to_string,
    `certigrad.T.zero,
    `certigrad.T.one,
    `certigrad.T.pi,
    `certigrad.T.const,

    `certigrad.T.neg,
    `certigrad.T.inv,
    `certigrad.T.log,
    `certigrad.T.exp,
    `certigrad.T.sqrt,
    `certigrad.T.tanh,

    `certigrad.T.add,
    `certigrad.T.mul,
    `certigrad.T.sub,
    `certigrad.T.div,

    `certigrad.T.smul,

    `certigrad.T.sum,
    `certigrad.T.prod,

    `certigrad.T.get_row,
    `certigrad.T.get_col,
    `certigrad.T.get_col_range,

    `certigrad.T.gemv,
    `certigrad.T.gemm,
    `certigrad.T.sample_gauss
]

meta def names_to_transport : list name :=
[   `certigrad.T.has_zero,
    `certigrad.T.has_one,
    `certigrad.T.has_neg,
    `certigrad.T.has_inv,
    `certigrad.T.has_add,
    `certigrad.T.has_mul,
    `certigrad.T.has_sub,
    `certigrad.T.has_div,
    `certigrad.T.inhabited,

    `certigrad.T.dot,
    `certigrad.T.square,

    `certigrad.T.grad,
    `certigrad.T.D,
    `certigrad.T.tmulT,

    `certigrad.T.mvn_iso_pdf,
    `certigrad.T.mvn_iso_logpdf,
    `certigrad.T.mvn_iso_std_logpdf,
    `certigrad.T.mvn_transform,

    `certigrad.T.IsContinuous,

    `certigrad.Distribution.Primitive.Grad,
    `certigrad.Distribution.Primitive.Grad.mk,
    `certigrad.Distribution.Primitive.Grad.rec,
    `certigrad.Distribution.Primitive.Grad.cases_on,
    `certigrad.Distribution.Primitive.Grad.rec_on,

    `certigrad.Distribution.Primitive,
    `certigrad.Distribution.Primitive.mk,
    `certigrad.Distribution.Primitive.rec,
    `certigrad.Distribution.Primitive.cases_on,
    `certigrad.Distribution.Primitive.rec_on,


    `certigrad.Distribution,
    `certigrad.Distribution.rec,
    `certigrad.Distribution.cases_on,
    `certigrad.Distribution.rec_on,
    `certigrad.Distribution.dret,
    `certigrad.Distribution.dbind,
    `certigrad.Distribution.dprim,

    `certigrad.PDF,
    `certigrad.PDF.mk,
    `certigrad.PDF.rec,
    `certigrad.PDF.cases_on,
    `certigrad.PDF.rec_on,

    `certigrad.Env,

    `certigrad.Det.Grad,
    `certigrad.Det.Grad.mk,
    `certigrad.Det.Grad.rec,
    `certigrad.Det.Grad.cases_on,
    `certigrad.Det.Grad.rec_on,
    `certigrad.Det.Grad.H_cont,
    `certigrad.Det.Grad.f_pb,
    `certigrad.Det.Grad.H_f_pb,

    `certigrad.Op,
    `certigrad.Op.rec,
    `certigrad.Op.cases_on,
    `certigrad.Op.rec_on,
    `certigrad.Op.det,
    `certigrad.Op.rand,
    `certigrad.Op.to_dist._main,
    `certigrad.Op.to_dist,

    `certigrad.Node,
    `certigrad.Node.mk,
    `certigrad.Node.rec,
    `certigrad.Node.cases_on,
    `certigrad.Node.rec_on,
    `certigrad.Node.name,
    `certigrad.Node.ishapes,
    `certigrad.Node.oshape,
    `certigrad.Node.op,
    `certigrad.Node.parents,
    `certigrad.Node.H_same_len,

    `certigrad.Target,
    `certigrad.Target.mk,
    `certigrad.Target.rec,
    `certigrad.Target.cases_on,
    `certigrad.Target.rec_on,

    `certigrad.Graph,
    `certigrad.Graph.mk,
    `certigrad.Graph.rec,
    `certigrad.Graph.cases_on,
    `certigrad.Graph.rec_on,

    `certigrad.Graph.to_dist._main,
    `certigrad.Graph.to_dist,

    `certigrad.sum_costs,

    `certigrad.sum_downstream_costs,
    `certigrad.compute_grad_slow._main,
    `certigrad.compute_grad_slow,
    `certigrad.compute_grad_step._main,
    `certigrad.compute_grad_step,
    `certigrad.backprop._main,
    `certigrad.backprop,
    `certigrad.bprop
]

print certigrad.Det.Grad.H_cont

open tactic

private meta def apply_replacement (replacements : name_map name) (e : expr) : expr :=
e^.replace (λ e d,
  match e with
  | expr.const n ls :=
    match replacements^.find n with
    | some new_n := some (expr.const new_n ls)
    | none       := none
    end
  | _ := none
  end)

meta def meta_copy_decl_using (replacements : name_map name) (src_decl_name : name) (new_decl_name : name) : command :=
do env  ← get_env,
   decl ← returnex $ env^.get src_decl_name,
   new_decl ← match decl : declaration → tactic declaration with
              | declaration.defn n lp_names ty val rhints trusted :=
                   return $ declaration.defn new_decl_name
                            decl^.univ_params
                            (apply_replacement replacements decl^.type)
                            (apply_replacement replacements decl^.value)
                            (reducibility_hints.regular 1 tt)
                            ff
              | declaration.cnst n lp_names ty trusted :=
                   return $ declaration.cnst new_decl_name
                            decl^.univ_params
                            (apply_replacement replacements decl^.type)
                            ff
              | _ := fail "not defn or cnst"
              end,
   add_decl new_decl,
   copy_attribute `instance src_decl_name tt new_decl_name

open tactic

meta def transport_inductive (env : environment) (replacements : name_map name) (n : name) : command := do
  decl ← returnex $ env^.get n,
  cnames ← return $ env^.constructors_of n,
  cdecls ← monad.mapm (λ cn, returnex $ env^.get cn) cnames,
  cnames_approx ← return $ list.map approx_name cnames,
  ctypes_approx ← return $ list.map (λ (cdecl : declaration), apply_replacement replacements cdecl^.type) cdecls,
  add_inductive (approx_name n)
                decl^.univ_params
                (env^.inductive_num_params n)
                (apply_replacement replacements decl^.type)
                (list.zip cnames_approx ctypes_approx)
                ff

meta def mtransport : command :=
let dict : name_map name := rb_map.of_list (list.map (λ n, (n, approx_name n)) (names_to_approx ++ names_to_transport)) in
list.foldl (λ t (n : name), do
  env ← get_env,
  if environment.is_constructor env n = tt then t else
  if environment.is_recursor env n = tt then t else
  (if environment.is_inductive env n = tt
   then t >> transport_inductive env dict n
   else t >> meta_copy_decl_using dict n (approx_name n)))
skip names_to_transport

run_command mtransport
/-
print "certigrad.approx.T.dot:"
print certigrad.approx.T.dot

print "(1 : T [5]) dot 1"
vm_eval certigrad.approx.T.dot (1 : certigrad.approx.T [5]) 1
-/
