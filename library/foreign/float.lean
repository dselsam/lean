constant Float : Type

namespace Float

constants zero one : Float
constants neg exp log : Float → Float
constants add mul sub div : Float → Float → Float

end Float

namespace Test
open Float

noncomputable def f₁ : Float := exp (Float.add Float.one Float.one)
-- vm_eval log f₁
end Test
