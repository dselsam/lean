inductive cmp_result : Type | lt, eq, gt

class has_cmp (A : Type) := (cmp : A → A → cmp_result)
def cmp {A : Type} [A_cmp : has_cmp A] : A → A → cmp_result := has_cmp.cmp

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
⟨red, red_node (black_node _ _ m₁ a₁ m₁') a (black_node _ _ m₂ data m)⟩

| n (red_node' _ red m₁ a (red_node m₂ a₂ m₂')) _ m :=
⟨red, red_node (black_node _ _ m₁ a m₂) a₂ (black_node _ _ m₂' data m)⟩

| 0 (red_node' black black leaf a leaf) _ m :=
⟨black, black_node _ _ (red_node leaf a leaf) data m⟩

| (n+1) (red_node' black black (black_node _ _ m₁ a₁ m₁') a (black_node _ _ m₂ a₂ m₂')) _ m :=
⟨black, black_node _ _ (red_node (black_node _ _ m₁ a₁ m₁') a (black_node _ _ m₂ a₂ m₂')) data m⟩

def balance₂ {A : Type} (data : A) :
  Π {c n}, rbtree A c n → rtree A n → sigma (λ c, rbtree A c (n + 1))

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
| black n := sigma (λ (c' : color), rbtree A c' n)

def insert_helper {A : Type} [has_cmp A] (x : A) : Π {c : color} {n : ℕ}, rbtree A c n → insert_helper_result A c n
| black 0 leaf :=
⟨red, red_node leaf x leaf⟩

| red n (red_node m₁ a m₁') :=
match cmp x a with
| cmp_result.lt := red_node' _ _ (insert_helper m₁)~>snd a m₁'
| cmp_result.eq := red_node' _ _ m₁ x m₁'
| cmp_result.gt := red_node' _ _ m₁ a (insert_helper m₁')~>snd
end

| black (n+1) (black_node c₁ c₁' m₁ a m₁') :=
match cmp x a with
| cmp_result.lt :=  match c₁, insert_helper m₁ with
                    | red, ins₁ := balance₁ a ins₁ m₁'
                    | black, ins₁ := ⟨black, black_node _ _ ins₁~>snd a m₁'⟩
                    end
| cmp_result.gt :=  match c₁', insert_helper m₁' with
                    | red, ins₁' := balance₂ a m₁ ins₁'
                    | black, ins₁' := ⟨black, black_node _ _ m₁ a ins₁'~>snd⟩
                    end
| cmp_result.eq := ⟨black, black_node _ _ m₁ x m₁'⟩
end

def insert_result (A : Type) : Π (c : color) (n : ℕ), Type
| red n := rbtree A black (n+1)
| black n := sigma (λ c', rbtree A c' n)


def mk_rbtree {A : Type} : Π {c : color} {n : ℕ}, insert_helper_result A c n → insert_result A c n
| red n (red_node' _ _ m₁ a m₂) := black_node _ _ m₁ a m₂
| black n ins := ins

def insert {A : Type} [has_cmp A] (x : A) {c : color} {n : ℕ} (t : rbtree A c n) : insert_result A c n := mk_rbtree (insert_helper x t)

def lookup {A : Type} [has_cmp A] (x : A) : Π {c : color} {n : ℕ}, rbtree A c n → option A
| black 0 leaf := none
| red n (red_node m₁ a m₂) :=
match cmp x a with
| cmp_result.lt := lookup m₁
| cmp_result.gt := lookup m₂
| cmp_result.eq := some a
end

| black (n+1) (black_node _ _ m₁ a m₂) :=
match cmp x a with
| cmp_result.lt := lookup m₁
| cmp_result.gt := lookup m₂
| cmp_result.eq := some a
end

def elems {A : Type} : Π {c : color} {n : ℕ}, rbtree A c n → list A
| black 0 leaf := []
| red n (red_node m₁ a m₂) := elems m₁ ++ (a :: elems m₂)
| black (n+1) (black_node _ _ m₁ a m₂) := elems m₁ ++ (a :: elems m₂)

end rbtree

structure rbset (A : Type) := (c : color) (n : ℕ) (t : rbtree A c n)

namespace rbset

def empty (A : Type) : rbset A := ⟨black, 0, rbtree.leaf⟩

def insert {A : Type} [has_cmp A] (x : A) : rbset A → rbset A
| ⟨red, n, t⟩ := ⟨black, n+1, rbtree.insert x t⟩
| ⟨black, n, t⟩ := match rbtree.insert x t with
                   | ⟨black, t'⟩ := ⟨black, n, t'⟩
                   | ⟨red, t'⟩ := ⟨red, n, t'⟩
                  end

def lookup {A : Type} [has_cmp A] (x : A) : rbset A → option A
| ⟨c, n, t⟩ := rbtree.lookup x t

def contains {A : Type} [has_cmp A] (x : A) : rbset A → bool
| ⟨c, n, t⟩ := match rbtree.lookup x t with
               | none := ff
               | some _ := tt
              end

def elems {A : Type} : rbset A → list A
| ⟨c, n, t⟩ := rbtree.elems t

end rbset

namespace rbmap
structure val (K V : Type) := (k : K) (v : V)
end rbmap

def rbmap (K V : Type) := rbset (rbmap.val K V)

namespace rbmap

def cmp {K V : Type} [decidable_linear_order K] : val K V → val K V → cmp_result
| ⟨k₁, _⟩ ⟨k₂, _⟩ := if k₁ < k₂ then cmp_result.lt else (if k₁ > k₂ then cmp_result.gt else cmp_result.eq)

instance (K V : Type) [decidable_linear_order K] : has_cmp (val K V) := ⟨cmp⟩

def mk (K V : Type) : rbmap K V := rbset.empty (val K V)

def insert {K V : Type} [decidable_linear_order K] (k : K) (v : V) (m : rbmap K V) : rbmap K V :=
rbset.insert ⟨k, v⟩ m

def lookup {K V : Type} [decidable_linear_order K] [inhabited V] (k : K) (m : rbmap K V) : option V :=
match rbset.lookup (rbmap.val.mk k (default V)) m with
| none := none
| some ⟨k', v'⟩ := some v'
end

def contains {K V : Type} [decidable_linear_order K] [inhabited V] (k : K) (m : rbmap K V) : Prop :=
match rbset.lookup (rbmap.val.mk k (default V)) m with
| none := false
| some ⟨k', v'⟩ := true
end

def keys {K V : Type} (m : rbmap K V) : list K := list.map val.k (rbset.elems m)

end rbmap

open rbmap
/-
def m₀ : rbmap ℕ ℕ := mk ℕ ℕ
eval lookup 1 (insert 6 66 (insert 5 5 (insert 5 5555 (insert 1 1111 (insert 3 33 (insert 2 222 (insert 1 11 (insert 2 22 (insert 1 111 (insert 4 44 m₀))))))))))
-/
