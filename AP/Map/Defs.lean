import AP.Util

@[ext]
structure Map.{u} (ι α : Type u) [LinearOrder ι] [DecidableEq α] : Type u where
  s : Finset # ι × α
  h : ∀ {x y}, x ∈ s → y ∈ s → x.1 = y.1 → x.2 = y.2

namespace Map

set_option linter.unusedVariables false
universe u
variable {ι α : Type u} [hhι : LinearOrder ι] [hhα : DecidableEq α] (mp : Map ι α)
set_option linter.unusedSectionVars true

omit mp
def empty : Map ι α :=
  ⟨∅, by simp⟩

omit mp
instance : EmptyCollection (Map ι α) := ⟨Map.empty⟩

protected def insert (i : ι) (x : α) : Map ι α := by
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

def insert_prod (p : ι × α) : Map ι α :=
  mp.insert p.1 p.2

instance : Insert (ι × α) (Map ι α) :=
  ⟨λ p mp => mp.insert_prod p⟩

omit mp
def ofList' (mp : Map ι α) : List (ι × α) → Map ι α
| [] => mp
| (x :: xs) => (insert x mp).ofList' xs

omit mp
def ofList : List (ι × α) → Map ι α :=
  empty.ofList'

def lookup (i : ι) : Option α := by
  obtain ⟨⟨s, hs⟩, h⟩ := mp
  simp at h
  apply s.lift_out λ xs => (xs.find? λ a => a.1 = i).map Prod.snd
  intro xs ys hx hy
  ext x
  simp only [Option.map_eq_some_iff, List.find?_eq_some_iff_getElem, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Prod.exists,
    exists_eq_right, exists_eq_left]
  change List.Perm _ _ at hx hy
  have h₁ := hx.trans hy.symm
  
  have h₂ : (Quotient.out s).Nodup :=
    by
      unfold Multiset.Nodup at hs
      generalize_proofs h₂ at hs
      sorry
  
  have h₃ := List.Perm.nodup hx.symm h₂
  have h₄ := List.Perm.nodup hy.symm h₂
  
  -- rw [List.perm_iff_count] at hx hy h₁
  
  constructor
  · rintro ⟨n, hn, h₅, h₆⟩
    have h₇ : xs[n] ∈ ys :=
      by
        rw [List.Perm.mem_iff (l₂ := xs)]
        simp; exact h₁.symm
    rw [List.mem_iff_getElem] at h₇
    obtain ⟨n', hn', h₇⟩ := h₇
    use n', hn', by rwa [h₇]
    intro m' hm'
    rw [List.nodup_iff_getElem?_ne_getElem?] at h₄
    specialize h₄ m' n' hm' hn'
    rw [List.getElem?_eq_getElem # by linarith] at h₄
    rw [List.getElem?_eq_getElem # by linarith] at h₄
    simp at h₄
    contrapose! h₄
    
    have h₈ : ys[n'] ∈ s.out :=
      by
        rw [List.Perm.mem_iff (l₂ := ys)]
        simp; exact hy.symm
    have h₉ : ys[m'] ∈ s.out :=
      by
        rw [List.Perm.mem_iff (l₂ := ys)]
        simp; exact hy.symm
    rw [List.mem_iff_getElem] at h₈ h₉
    obtain ⟨k₁, hk₁, h₈⟩ := h₈
    obtain ⟨k₂, hk₂, h₉⟩ := h₉
    
    rw [←h₈]
    rw [←h₉] at h₄ ⊢
    specialize h i x
    
    sorry
  
  sorry

-- h₂ : ∀ (a b : List (ι × α)), (List.isSetoid (ι × α)) a b → a.Nodup = b.Nodup
-- hs : Quot.liftOn s List.Nodup h₂
-- ⊢ (Quotient.out s).Nodup