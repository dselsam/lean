inductive color : Type | red, black
open color

inductive rbtree (A : Type) : color → ℕ → Type
| leaf {} : rbtree black 0
| red_node : ∀ {n}, rbtree black n → A → rbtree black n → rbtree red n
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
  Π {n}, rtree A n → Π {c}, rbtree A c n → sigma (λ c, rbtree A c (n + 1))

| n (red_node' red _ (red_node m₁ a₁ m₁') a m₂) _ m :=
⟨red, red_node (black_node _ _ m₁ a₁ m₁') a (black_node _ _ m data m₂)⟩

| n (red_node' _ red m₁ a (red_node m₂ a₂ m₂')) _ m :=
⟨red, red_node (black_node _ _ m₁ a m₂) a₂ (black_node _ _ m₂ data m₂)⟩

| 0 (red_node' black black leaf a leaf) _ m :=
⟨black, black_node _ _ (red_node leaf a leaf) data m⟩

| (n+1) (red_node' black black (black_node _ _ m₁ a₁ m₁') a (black_node _ _ m₂ a₂ m₂')) _ m :=
⟨black, black_node _ _ (red_node (black_node _ _ m₁ a₁ m₁') a (black_node _ _ m₂ a₂ m₂')) data m⟩



end rbtree
