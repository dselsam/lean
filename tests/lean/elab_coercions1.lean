set_option pp.all true
set_option pp.full_names false
set_option pp.universes false

namespace coe_arg
print "coe_arg"

constants (A B : Type.{1})  (coe : A → B) (a : A) (b : B)
attribute coe [coercion]

namespace no_implicits
print "no_implicits"
constants (C : Type) (op : B → B → C)
#elab op a b
#elab op b a

end no_implicits

namespace one_implicit
print "one_implicits"
constants (op : Π {X}, X → X → X)
#elab op a b
#elab op b a

end one_implicit

namespace inst_implicit
print "inst_implicit"
constants (T : Type → Type) (T_A : T A) (T_B : T B)
attribute T [class]
attribute T_A [instance]
attribute T_B [instance]

constants (op : Π {X : Type} [T_X : T X], X → X → X)
#elab op a b
#elab op b a

end inst_implicit

end coe_arg

namespace coe_arg_with_composite
print "coe_arg_with_composite"

constants (A B : Type.{1}) (coe : A → B) (a : A) (C : Type → Type) (bs : C B)
attribute coe [coercion]

namespace one_implicit
print "one_implicit"
constants (lcons : Π {X}, X → C X → C X) (rcons : Π {X}, C X → X → C X)

#elab lcons a bs
#elab rcons bs a

end one_implicit

namespace inst_implicit
print "one_implicit"
constants (T : Type → Type) (T_A : T A) (T_B : T B)
attribute T [class]
attribute T_A [instance]
attribute T_B [instance]

constants (lcons : Π {X : Type} [T_X : T X], X → C X → C X)
          (rcons : Π {X : Type} [T_X : T X], C X → X → C X)

#elab lcons a bs
#elab rcons bs a

end inst_implicit


end coe_arg_with_composite
