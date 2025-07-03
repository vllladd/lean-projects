import AP.Util

@[ext]
structure Map.{u} (ι α : Type u) [LinearOrder ι] [DecidableEq α] : Type u where
  s : Finset # ι × α
  h : ∀ {x y}, x ∈ s → y ∈ s → x.1 = y.1 → x.2 = y.2

namespace Map

set_option linter.unusedVariables false
universe u
variable {ι α : Type u} [hhι : LinearOrder ι] [hhα : DecidableEq α]
set_option linter.unusedSectionVars true

def empty : Map ι α :=
  ⟨∅, by simp⟩

instance : EmptyCollection (Map ι α) := ⟨Map.empty⟩

protected def insert (mp : Map ι α) (i : ι) (x : α) : Map ι α := by
  use insert (i, x) # mp.s.filter # λ y => y.1 ≠ i
  rintro ⟨j, a⟩ ⟨k, b⟩
  simp
  rintro h₁ h₂ rfl
  by_cases h₃ : j = i
  · subst h₃
    simp at h₁ h₂
    rw [h₁, h₂]
  simp [h₃] at h₁ h₂
  exact mp.h h₁ h₂ rfl

-- #check 0 #exit

def ListType (ι α : Type u) : Type u :=
  {xs : List # ι × α // xs.Nodup ∧ (∀ {x y}, x ∈ xs → y ∈ xs → x.1 = y.1 → x.2 = y.2)}

def ListEquiv (xs ys : @ListType ι α) : Prop :=
  xs.1.Perm ys.1

omit hhι hhα
theorem equiv_list_equiv : Equivalence # @ListEquiv ι α := by
  unfold ListEquiv
  constructor
  · intro xs; simp
  · intro xs ys h; exact h.symm
  · intro xs ys zs h₁ h₂; exact h₁.trans h₂

def ListSetoid (ι α : Type u) : Setoid # ListType ι α :=
  ⟨_, equiv_list_equiv⟩

def ListQuot (ι α : Type u) : Type u :=
  Quotient # @ListSetoid ι α

-- def to_list_quot (mp : Map ι α) : ListQuot ι α := by
--   apply Quotient.mk
--   have h₁ := mp.1
--   refine' Quotient.liftOn mp.s.1 _ _
--   · intro xs

#check 0 #exit

def lookup (mp : Map ι α) (i : ι) : Option α := by
  obtain ⟨s, h⟩ := mp
  revert h
  apply s.val.lift # λ xs h => (xs.find? # λ (a : ι × α) => a.1 = i).map Prod.snd
  intro xs ys hx
  dsimp
  change xs.Perm ys at hx
  congr 1
  ext ⟨j, x⟩
  simp [List.find?_eq_some_iff_getElem]
  rintro rfl
  rw [List.perm_iff_count] at hx
  specialize hx ⟨j, x⟩
  have hd : xs.Nodup :=
    by
      have := s.2
  constructor
  · rintro ⟨k, h₁, h₂, h₃⟩
    have h₄ : xs.count (j, x) = 1 :=
      by
        apply List.count_eq_one_of_mem