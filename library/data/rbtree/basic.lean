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

end rbtree

inductive rtree (A : Type) : ℕ → Type
| red_node' : ∀ {n} c₁ c₂, rbtree A c₁ n → A → rbtree A c₂ n → rtree n

namespace rtree

def present {A : Type} (x : A) : Π {n}, rtree A n → Prop
| n (red_node' _ _ m₁ a m₂) := rbtree.present x m₁ ∨ x = a ∨ rbtree.present x m₂

end rtree
