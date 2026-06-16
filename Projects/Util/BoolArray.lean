import Projects.Util.Array
import Projects.Util.BoolList

namespace Array

def decideBoolArray (p : Array Bool → Bool) (n : ℕ) : Bool :=
  List.decideBoolList (p # ⟨·⟩) n

-----

theorem decideBoolArray_iff {p : Array Bool → Prop} [hp : DecidablePred p] {n : ℕ} :
decideBoolArray p n ↔ ∀ (xs : Array Bool), xs.size = n → p xs := by
  rw [decideBoolArray, List.decideBoolList_iff]
  apply Iff.intro
  · intro a xs a_1
    subst a_1
    simp_all only [length_toList]
  · intro a xs a_1
    subst a_1
    simp_all only [List.size_toArray]

instance {p : Array Bool → Prop} [hp : DecidablePred p] {n : ℕ} :
Decidable # ∀ (xs : Array Bool), xs.size = n → p xs :=
  decidable_of_bool (decideBoolArray p n) decideBoolArray_iff