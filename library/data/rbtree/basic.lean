inductive color : Type | red, black
open color

inductive rbtree (A : Type) : color → ℕ → Type
| leaf {} : rbtree black 0
| red_node : ∀ {n}, rbtree black n → A -> rbtree black n → rbtree red n
| black_node : ∀ {n} (c₁ c₂ : color), rbtree c₁ n → A → rbtree c₂ n → rbtree black (n + 1)

namespace rbtree

def present {A : Type} (x : A) : Π {c : color} {n : ℕ}, rbtree A c n → Prop
| black 0 leaf := false
| red n (red_node m₁ a m₂) := present m₁ ∨ x = a ∨ present m₂
| black (n + 1) (black_node c₁ c₂ m₁ a m₂) := present m₁ ∨ x = a ∨ present m₂

inductive rtree (A : Type) : ℕ → Type
| red_node' : ∀ {n} c₁ c₂, rbtree A c₁ n → A → rbtree A c₂ n → rtree n

open rtree

def present' {A : Type} (x : A) : Π {n}, rtree A n → Prop
| n (red_node' _ _ m₁ a m₂) := present x m₁ ∨ x = a ∨ present x m₂

def balance₁ {A : Type} (data : A) :
  Π {n}, rtree A n →
  Π {c}, rbtree A c n →
  sigma (λ c, rbtree A c (n + 1))

| n (red_node' red _ (red_node m₂ a₂ m₂') a₁ m₁') cc₁ mm₁ :=
⟨red, red_node (black_node _ _ m₂ a₂ m₂') a₂ (black_node _ _ mm₁ data m₂')⟩

/-
Definition balance1 n (a : rtree n) (data : nat) c2 :=
  match a in rtree n return rbtree c2 n
    -> { c : color & rbtree c (S n) } with
    | RedNode' _ c0 _ t1 y t2 =>
      match t1 in rbtree c n return rbtree c0 n -> rbtree c2 n
        -> { c : color & rbtree c (S n) } with
        | RedNode _ a x b => fun c d =>
          {<RedNode (BlackNode a x b) y (BlackNode c data d)>}
        | t1' => fun t2 =>
          match t2 in rbtree c n return rbtree Black n -> rbtree c2 n
            -> { c : color & rbtree c (S n) } with
            | RedNode _ b x c => fun a d =>
              {<RedNode (BlackNode a y b) x (BlackNode c data d)>}
            | b => fun a t => {<BlackNode (RedNode a y b) data t>}
          end t1'
      end t2
  end.
-/



end rbtree
