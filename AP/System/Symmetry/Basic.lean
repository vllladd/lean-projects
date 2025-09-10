import AP.System.Symmetry.Defs

namespace System.Symmetry

universe u
variable {S T : Type u} {sys : System S T}
variable {sym sym₁ sym₂ sym₃ : Symmetry sys}

instance : Group sys.Symmetry where
  mul_assoc := λ _ _ _ => rfl
  one_mul := λ _ => rfl
  mul_one := λ _ => rfl
  inv_mul_cancel := λ _ => ext Raw.inv_mul_cancel

instance : DivisionMonoid sys.Symmetry where
  mul_inv_rev := λ _ _ => rfl
  inv_eq_of_mul := λ _ _ => by
    simp only [Symmetry.ext_iff]; exact Raw.inv_eq_of_mul