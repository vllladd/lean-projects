import AP.Util.Data.Trie.Raw

namespace Trie.Raw

open Std

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable {t t₁ t₂ t₃ : Raw α β}

def Equiv (t₁ t₂ : Raw α β) : Prop :=
  (∀ k a, t₁.get? k = some a → ∃ (b : Raw α β) (_ : t₂.get? k = some b), a.Equiv b) ∧
  (∀ k b, t₂.get? k = some b → ∃ (a : Raw α β) (_ : t₁.get? k = some a), a.Equiv b)
termination_by max (sizeOf t₁) (sizeOf t₂)
decreasing_by all_goals nm h₁ h₂; have h₁ := sizeOf_lt h₁; have h₂ := sizeOf_lt h₂; omega

@[refl, simp]
theorem Equiv.refl : t.Equiv t := by
  apply t.ind
  intro val mp wf ih
  unfold Equiv
  simp only [get?_eq_some_iff, Raw₀.mp_mk, exists_prop]
  split_ands; all_goals
    intro k a h
    use a, h, ih k a h

@[symm]
theorem Equiv.symm (h : t₁.Equiv t₂) : t₂.Equiv t₁ := by
  revert t₂
  apply t₁.ind
  intro val mp wf ih t₂ h
  unfold Equiv at h ⊢
  simp only [get?_eq_some_iff, Raw₀.mp_mk, exists_prop] at h ⊢
  rcases h with ⟨h₁, h₂⟩
  split_ands <;> intro k a h
  · specialize h₂ _ _ h
    choose b h₂ h₃ using h₂
    use b, h₂
    apply ih _ _ h₂ h₃
  · specialize h₁ _ _ h
    choose b h₁ h₃ using h₁
    use b, h₁
    apply ih _ _ h h₃

theorem Equiv.comm : t₁.Equiv t₂ ↔ t₂.Equiv t₁ :=
  ⟨Equiv.symm, Equiv.symm⟩

@[trans]
theorem Equiv.trans (h₁ : t₁.Equiv t₂) (h₂ : t₂.Equiv t₃) : t₁.Equiv t₃ := by
  revert t₂ t₃
  apply t₁.ind
  intro val mp wf ih t₂ t₃ h₁ h₂
  unfold Equiv at h₁ h₂ ⊢
  simp only [get?_eq_some_iff, Raw₀.mp_mk, exists_prop] at h₁ h₂ ⊢
  rcases h₁ with ⟨h₁, h₃⟩
  rcases h₂ with ⟨h₂, h₄⟩
  split_ands <;> intro k a h
  · clear h₃ h₄
    specialize h₁ _ _ h
    choose b h₁ h₃ using h₁
    specialize h₂ _ _ h₁
    choose c h₂ h₄ using h₂
    use c, h₂
    exact ih k a h h₃ h₄
  · clear h₁ h₂
    specialize h₄ _ _ h
    choose b h₄ h₂ using h₄
    specialize h₃ _ _ h₄
    choose c h₃ h₁ using h₃
    use c, h₃
    exact ih k c h₃ h₁ h₂

def Equiv.iseqv : Equivalence # Equiv (α := α) (β := β) where
  refl _ := Equiv.refl
  symm := Equiv.symm
  trans := Equiv.trans

instance Setoid : Setoid # Raw α β where
  r := Equiv
  iseqv := Equiv.iseqv

namespace Equiv

variable (H : t₁.Equiv t₂)
include H

theorem depth_eq : t₁.depth = t₂.depth := by
  classical
  revert t₂
  apply t₁.ind
  intro val mp wf ih t₂ h
  unfold Equiv at h
  simp only [get?_eq_some_iff, Raw₀.mp_mk, exists_prop] at h
  rcases h with ⟨h₁, h₂⟩
  rcases t₂ with ⟨⟨val', mp'⟩, wf'⟩
  dsimp at *
  
  simp
  simp_rw [DHashMap.Raw.foldWith_eq_foldlWith_toList]
  simp_rw [List.foldlWith_max_eq_max?_mapWith]
  congr 1
  apply List.max?_eq_max?_of_perm
  simp_rw [List.mapWith_eq_map]
  
  have wfmp := wf.mp
  have wfmp' := wf'.mp
  dsimp at wfmp wfmp'
  
  split_ifs with h₃ h₄ h₄
  · rfl
  ·
    exfalso
    cases h : mp'.toList; simp [h] at h₄
    nm x xs
    replace h := congrArg (x ∈ ·) h
    simp at h
    rw [DHashMap.Raw.mem_toList_iff_get?_eq_some wfmp'] at h
    rcases x with ⟨x, t₁⟩
    dsimp at h
    specialize h₂ _ ⟨_, wf'.get? h⟩ h
    choose y h₂ h₅ using h₂
    rw [←DHashMap.Raw.mem_toList_iff_get?_eq_some wfmp] at h₂
    simp [h₃] at h₂
  ·
    exfalso
    rename' h₃ => h₄, h₄ => h₃
    cases h : mp.toList; simp [h] at h₄
    nm x xs
    replace h := congrArg (x ∈ ·) h
    simp at h
    rw [DHashMap.Raw.mem_toList_iff_get?_eq_some wfmp] at h
    rcases x with ⟨x, t₁⟩
    dsimp at h
    specialize h₁ _ ⟨_, wf.get? h⟩ h
    choose y h₁ h₅ using h₁
    rw [←DHashMap.Raw.mem_toList_iff_get?_eq_some wfmp'] at h₁
    simp [h₃] at h₁
  
  sorry
  
  -- suffices h : ∀ (z₁ z₂ : ℕ),
  --   (λ (p : (_ : α) × Raw₀ α β) => if h₁ : p ∈ mp.toList then 1 + p.2.depth
  --     (wf := wf.of_mem_toList h₁) else z₁) =
  --   (λ (p : (_ : α) × Raw₀ α β) => if h₁ : p ∈ mp'.toList then 1 + p.2.depth
  --     (wf := wf'.of_mem_toList h₁) else z₂)
  -- ·
  --   
  --   rw [h, List.map_perm_map_iff_loc]; clear h
  --   · sorry