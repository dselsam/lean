-- TODO(dhs): preferably we don't use 'meta' here
-- instance gave an error, not sure if it is justified
meta constant float : Type

namespace float

meta constants zero one : float
meta constants neg inv exp log : float → float
meta constants add mul sub div : float → float → float

meta constant to_string : float → string

meta instance : has_to_string float :=
has_to_string.mk float.to_string

end float

namespace Test
open float

vm_eval float.one

meta def f₁ : float := exp (float.add float.one float.one)

vm_eval log f₁

end Test
