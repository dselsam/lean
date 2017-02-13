inductive color : Type | red, black
open color

inductive rbtree_core (A : Type) : color → ℕ → Type
| leaf {} : rbtree_core black 0
| red_node : ∀ {n}, rbtree_core black n → A → rbtree_core black n → rbtree_core red n
| black_node : ∀ {n} (c₁ c₂ : color), rbtree_core c₁ n → A → rbtree_core c₂ n → rbtree_core black (n + 1)

namespace rbtree_core

def present {A : Type} (x : A) : Π {c : color} {n : ℕ}, rbtree_core A c n → Prop
| black 0 leaf := false
| red n (red_node m₁ a m₂) := present m₁ ∨ x = a ∨ present m₂
| black (n + 1) (black_node c₁ c₂ m₁ a m₂) := present m₁ ∨ x = a ∨ present m₂

inductive rtree (A : Type) : ℕ → Type
| red_node' : ∀ {n} c₁ c₂, rbtree_core A c₁ n → A → rbtree_core A c₂ n → rtree n

open rtree

def present' {A : Type} (x : A) : Π {n}, rtree A n → Prop
| n (red_node' _ _ m₁ a m₂) := present x m₁ ∨ x = a ∨ present x m₂

def balance₁ {A : Type} (data : A) :
  Π {n}, rtree A n → Π {c}, rbtree_core A c n → sigma (λ c, rbtree_core A c (n + 1))

| n (red_node' red _ (red_node m₁ a₁ m₁') a m₂) _ m :=
⟨red, red_node (black_node _ _ m₁ a₁ m₁') a (black_node _ _ m₂ data m)⟩

| n (red_node' _ red m₁ a (red_node m₂ a₂ m₂')) _ m :=
⟨red, red_node (black_node _ _ m₁ a m₂) a₂ (black_node _ _ m₂' data m)⟩

| 0 (red_node' black black leaf a leaf) _ m :=
⟨black, black_node _ _ (red_node leaf a leaf) data m⟩

| (n+1) (red_node' black black (black_node _ _ m₁ a₁ m₁') a (black_node _ _ m₂ a₂ m₂')) _ m :=
⟨black, black_node _ _ (red_node (black_node _ _ m₁ a₁ m₁') a (black_node _ _ m₂ a₂ m₂')) data m⟩

def balance₂ {A : Type} (data : A) :
  Π {c n}, rbtree_core A c n → rtree A n → sigma (λ c, rbtree_core A c (n + 1))

| _ n m (red_node' red _ (red_node m₁ a₁ m₁') a m₂) :=
⟨red, red_node (black_node _ _ m data m₁) a₁ (black_node _ _ m₁' a m₂)⟩

| _ n m (red_node' _ red m₁ a (red_node m₂ a₂ m₂')) :=
⟨red, red_node (black_node _ _ m data m₁) a (black_node _ _ m₂ a₂ m₂')⟩

| _ 0 m (red_node' black black leaf a leaf) :=
⟨black, black_node _ _ m data (red_node leaf a leaf)⟩

| _ (n+1) m (red_node' black black (black_node _ _ m₁ a₁ m₁') a (black_node _ _ m₂ a₂ m₂')) :=
⟨black, black_node _ _ m data (red_node (black_node _ _ m₁ a₁ m₁') a (black_node _ _ m₂ a₂ m₂'))⟩

@[reducible] def insert_helper_result (A : Type) : Π (c : color), ℕ → Type
| red n := rtree A n
| black n := sigma (λ (c' : color), rbtree_core A c' n)

def insert_helper {A : Type} [decidable_linear_order A] (x : A) : Π {c : color} {n : ℕ}, rbtree_core A c n → insert_helper_result A c n
| black 0 leaf :=
⟨red, red_node leaf x leaf⟩

| red n (red_node m₁ a m₁') :=
if x < a
then red_node' _ _ (insert_helper m₁)~>snd a m₁'
else red_node' _ _ m₁ a (insert_helper m₁')~>snd

| black (n+1) (black_node c₁ c₁' m₁ a m₁') :=
if x < a
then match c₁, insert_helper m₁ with
     | red, ins₁ := balance₁ a ins₁ m₁'
     | black, ins₁ := ⟨black, black_node _ _ ins₁~>snd a m₁'⟩
     end
else match c₁', insert_helper m₁' with
     | red, ins₁' := balance₂ a m₁ ins₁'
     | black, ins₁' := ⟨black, black_node _ _ m₁ a ins₁'~>snd⟩
     end

def insert_result (A : Type) : Π (c : color) (n : ℕ), Type
| red n := rbtree_core A black (n+1)
| black n := sigma (λ c', rbtree_core A c' n)


def mk_rbtree_core {A : Type} : Π {c : color} {n : ℕ}, insert_helper_result A c n → insert_result A c n
| red n (red_node' _ _ m₁ a m₂) := black_node _ _ m₁ a m₂
| black n ins := ins

def insert {A : Type} [decidable_linear_order A] (x : A) {c : color} {n : ℕ} (t : rbtree_core A c n) : insert_result A c n := mk_rbtree_core (insert_helper x t)

def lookup {A : Type} [decidable_linear_order A] (x : A) : Π {c : color} {n : ℕ}, rbtree_core A c n → option A
| black 0 leaf := none
| red n (red_node m₁ a m₂) :=
if x = a then some a else (if x < a then lookup m₁ else lookup m₂)
| black (n+1) (black_node _ _ m₁ a m₂) :=
if x = a then some a else (if x < a then lookup m₁ else lookup m₂)

end rbtree_core

structure rbset (A : Type) := (c : color) (n : ℕ) (t : rbtree_core A c n)

namespace finset

def mk (A : Type) : rbset A := ⟨black, 0, rbtree_core.leaf⟩

def insert {A : Type} [decidable_linear_order A] (x : A) : rbset A → rbset A
| ⟨red, n, t⟩ := ⟨black, n+1, rbtree_core.insert x t⟩
| ⟨black, n, t⟩ := match rbtree_core.insert x t with
                   | ⟨black, t'⟩ := ⟨black, n, t'⟩
                   | ⟨red, t'⟩ := ⟨red, n, t'⟩
                  end

end finset
