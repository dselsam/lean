constant N : Type.{1}
constant I : Type.{1}

namespace foo
  xinductive p (a : N) : Prop
  | intro : p
end foo

open foo

namespace bla
  xinductive p (a : I) : Prop
  | intro : p
end bla
