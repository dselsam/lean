import logic
print "\n\n\n"
print hfunext
print "\n\n\n"
print hfunext_full


example {A : Type} : (λ a : A, a) == (λ a : A, a) :=
begin
apply (hfunext_full (eq.refl A)),
intro a a',
intro H, exact H
end
