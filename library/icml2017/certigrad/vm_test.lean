import .tmath .compute_grad .builder .aevb

namespace certigrad

attribute [semireducible] T

def M₁ : T [2, 3] := 2
def N₁ : T [3, 2] := 3
def x₁ : T [3] := 5

print "[5 5 5]"
vm_eval x₁

print "75"
vm_eval T.dot x₁ x₁

print "[30 30]"
vm_eval T.gemv M₁ x₁

print "[18 18]"
vm_eval T.gemm M₁ N₁

print "12"
vm_eval T.sum M₁

print "15"
vm_eval T.sum x₁

print "64"
vm_eval T.prod M₁

print "125"
vm_eval T.prod x₁

-----------------------------

print "[0 0]"
vm_eval compute_grad_slow [Identifier.str "cost"]
                          [2] (Identifier.str "theta")
                          [⟨Identifier.str "cost", [], [], Ops.Det.const (7 : T []), [], rfl⟩]
                          (DMap.insert (Identifier.str "theta") (5 : T [2]) (DMap.mk Identifier T))

print "[1 1]"
vm_eval compute_grad_slow [Identifier.str "cost"]
                          [2] (Identifier.str "theta")
                          [⟨Identifier.str "cost", [[2]], [], Ops.Det.sum [2], [Identifier.str "theta"], rfl⟩]
                          (DMap.insert (Identifier.str "theta") (5 : T [2]) (DMap.mk Identifier T))

print "[5 5]"
vm_eval compute_grad_slow [Identifier.str "cost"]
                          [2] (Identifier.str "theta")
                          [⟨Identifier.str "cost", [[2]], [], Ops.Det.prod [2], [Identifier.str "theta"], rfl⟩]
                          (DMap.insert (Identifier.str "theta") (5 : T [2]) (DMap.mk Identifier T))

print "[25 25 25]"
vm_eval compute_grad_slow [Identifier.str "cost"]
                          [3] (Identifier.str "theta")
                          [⟨Identifier.str "cost", [[3]], [], Ops.Det.prod [3], [Identifier.str "theta"], rfl⟩]
                          (DMap.insert (Identifier.str "theta") (5 : T [3]) (DMap.mk Identifier T))

print "[25 25 25]"
vm_eval DVec.head (bprop [Identifier.str "cost"]
                         [[3]] [Identifier.str "theta"] rfl
                         [⟨Identifier.str "cost", [[3]], [], Ops.Det.prod [3], [Identifier.str "theta"], rfl⟩]
                         (DMap.insert (Identifier.str "theta") (5 : T [3]) (DMap.mk Identifier T)))

print "[1 1]"
vm_eval DVec.head (bprop [Identifier.str "cost_sum", Identifier.str "cost_prod"]
                         [[2], [3]] [Identifier.str "theta_sum", Identifier.str "theta_prod"] rfl
                         [⟨Identifier.str "cost_sum", [[2]], [], Ops.Det.sum [2], [Identifier.str "theta_sum"], rfl⟩,
                          ⟨Identifier.str "cost_prod", [[3]], [], Ops.Det.prod [3], [Identifier.str "theta_prod"], rfl⟩]
                         (DMap.insert (Identifier.str "theta_sum") (5 : T [2])
                                      (DMap.insert (Identifier.str "theta_prod") (5 : T [3]) (DMap.mk Identifier T))))

print "[25 25 25]"
vm_eval DVec.head₂ (bprop [Identifier.str "cost_sum", Identifier.str "cost_prod"]
                         [[2], [3]] [Identifier.str "theta_sum", Identifier.str "theta_prod"] rfl
                         [⟨Identifier.str "cost_sum", [[2]], [], Ops.Det.sum [2], [Identifier.str "theta_sum"], rfl⟩,
                          ⟨Identifier.str "cost_prod", [[3]], [], Ops.Det.prod [3], [Identifier.str "theta_prod"], rfl⟩]
                         (DMap.insert (Identifier.str "theta_sum") (5 : T [2])
                                      (DMap.insert (Identifier.str "theta_prod") (5 : T [3]) (DMap.mk Identifier T))))


/-
vm_eval AEVB.Programs.build_graph₁ (1 : T [3, 7]) ⟨0, sorry⟩ 2 [] []
-- {n_x x_dim : ℕ} (x_data : T [x_dim, n_x]) (x_idx : fin n_x) (z_dim : ℕ) (z_hiddens x_hiddens : List (ℕ × String)) : Graph := build_graph $ d
-/
end certigrad
