definition mk_monomial [irreducible] {A : Type} [has_mul A] (c pp : A) : A := c * pp
notation `[` x `,` y `]` := mk_monomial x y


check λ x:nat, [1, x]
