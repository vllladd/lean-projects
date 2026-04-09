import Projects.Misc.NatPair.Basic

namespace NatPair

def equiv : ℕ × ℕ ≃ ℕ where
  toFun := f
  invFun := g
  left_inv := leftInverse_g_f
  right_inv := rightInverse_g_f