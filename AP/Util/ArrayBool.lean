import AP.Util.Array
import AP.Util.ListBool

namespace Array

def decideArrayBool (p : Array Bool → Bool) (n : ℕ) : Bool :=
  List.decideListBool (p # ⟨·⟩) n

theorem decideArrayBool_iff {p : Array Bool → Prop} [hp : DecidablePred p] {n : ℕ} :
decideArrayBool p n ↔ ∀ (xs : Array Bool), xs.size = n → p xs := by
  rw [decideArrayBool, List.decideListBool_iff]
  apply Iff.intro
  · intro a xs a_1
    subst a_1
    simp_all only [length_toList]
  · intro a xs a_1
    subst a_1
    simp_all only [List.size_toArray]

instance {p : Array Bool → Prop} [hp : DecidablePred p] {n : ℕ} :
Decidable # ∀ (xs : Array Bool), xs.size = n → p xs :=
  decidable_of_bool (decideArrayBool p n) decideArrayBool_iff