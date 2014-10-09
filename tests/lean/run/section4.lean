import logic

section
  universe k
  parameter A : Type

  section
    universe l
    universe u
    parameter B : Type
    definition foo (a : A) (b : B) := b

    inductive mypair :=
    mk : A → B → mypair
  end
  variable a : A
  check foo num a 0
  definition pr1 (p : mypair num) : A   := mypair.rec (λ a b, a) p
  definition pr2 (p : mypair num) : num := mypair.rec (λ a b, b) p
end
