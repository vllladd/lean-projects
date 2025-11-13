import AP.Util.Data.Trie.Raw

namespace Trie.Raw

open Std

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable {t t' t₁ t₂ t₃ : Raw α β}

def Equiv (t₁ t₂ : Raw α β) : Prop :=
  (∀ k a, t₁.get? k = some a → ∃ (b : Raw α β) (_ : t₂.get? k = some b), a.Equiv b) ∧
  (∀ k b, t₂.get? k = some b → ∃ (a : Raw α β) (_ : t₁.get? k = some a), a.Equiv b)
termination_by max (depth t₁) (depth t₂)
decreasing_by all_goals nm h₁ h₂; have h₁ := depth_lt h₁; have h₂ := depth_lt h₂; omega

@[refl, simp]
theorem Equiv.refl : t.Equiv t := by
  apply t.ind
  intro val mp wf ih
  unfold Equiv
  simp only [get?_eq_some_iff, exists_prop]
  split_ands; all_goals
    intro k a h
    use a, h, ih k a h

@[symm]
theorem Equiv.symm (h : t₁.Equiv t₂) : t₂.Equiv t₁ := by
  revert t₂
  apply t₁.ind
  intro val mp wf ih t₂ h
  unfold Equiv at h ⊢
  simp only [get?_eq_some_iff, exists_prop] at h ⊢
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
  simp only [get?_eq_some_iff, exists_prop] at h₁ h₂ ⊢
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
  simp only [get?_eq_some_iff, exists_prop] at h
  rcases h with ⟨h₁, h₂⟩
  rcases t₂ with ⟨⟨val', mp'⟩, wf'⟩
  have wfmp := wf.mp
  have wfmp' := wf'.mp
  dsimp at *
  simp
  simp_rw [DHashMap.Raw.foldWith_eq_foldlWith_toList]
  simp_rw [List.foldlWith_max_eq_max?_mapWith]
  congr 1
  apply List.max?_eq_max?_of_mem_iff
  intro d
  simp
  constructor
  · rintro ⟨k, t₂, h₃, rfl⟩
    simp
    use k
    rw [DHashMap.Raw.mem_toList_iff_get?_eq_some wfmp] at h₃
    specialize h₁ k ⟨t₂, wf.get? h₃⟩ h₃
    obtain ⟨t₃, h₁, h₄⟩ := h₁
    use t₃.1
    use by rwa [DHashMap.Raw.mem_toList_iff_get?_eq_some wfmp']
    specialize @ih k ⟨t₂, wf.get? h₃⟩ h₃ t₃ h₄
    simp at ih
    simp [ih, ←depth_eq_depth_inner]
  · rintro ⟨k, t₂, h₃, rfl⟩
    simp
    use k
    rw [DHashMap.Raw.mem_toList_iff_get?_eq_some wfmp'] at h₃
    specialize h₂ k ⟨t₂, wf'.get? h₃⟩ h₃
    obtain ⟨t₃, h₂, h₄⟩ := h₂
    use t₃.1
    use by rwa [DHashMap.Raw.mem_toList_iff_get?_eq_some wfmp]
    rw [←depth_eq_depth_inner]
    specialize @ih k t₃ h₂ ⟨t₂, wf'.get? h₃⟩ h₄
    simp [ih]

theorem get? {k t} (h : t₁.get? k = some t) : ∃ t', t₂.get? k = some t' ∧ t'.Equiv t := by
  unfold Equiv at H
  replace H := H.1
  specialize H k t h
  choose t' h₁ h₂ using H
  use t', h₁, h₂.symm

theorem get?' {k t} (h : t₂.get? k = some t) : ∃ t', t₁.get? k = some t' ∧ t'.Equiv t := by
  unfold Equiv at H
  replace H := H.2
  specialize H k t h
  choose t' h₁ h₂ using H
  use t'

theorem mem {k} : k ∈ t₁.mp ↔ k ∈ t₂.mp := by
  iterate 2 rw [DHashMap.Raw.mem_iff_isSome_get? # by simp]
  simp [Option.isSome_iff_exists, get?_mp]
  constructor <;> rintro ⟨x, h⟩
  · choose y h₁ h₂ using H.get? h; use y
  · choose y h₁ h₂ using H.get?' h; use y

theorem size_mp : t₁.mp.size = t₂.mp.size := by
  apply DHashMap.Raw.size_eq_size_of_mem_iff_mem (by simp) (by simp)
  simp [H.mem]

omit H in
theorem iff_alt' : t₁.Equiv t₂ ↔ t₁.mp.size = t₂.mp.size ∧
∀ k x, t₁.get? k = some x → ∃ y, t₂.get? k = some y ∧ x.Equiv y := by
  nth_rw 1 [Equiv]
  simp
  constructor <;> rintro ⟨h₁, h₂⟩
  · have H : t₁.Equiv t₂
    · unfold Equiv
      simp
      exact ⟨h₁, h₂⟩
    use H.size_mp
  use h₂
  intro k y h₃
  suffices h₄ : k ∈ t₁.mp
  · rw [t₁.mp.mem_iff_isSome_get? # by simp] at h₄
    rw [Option.isSome_iff_exists] at h₄
    simp [get?_mp] at h₄
    choose x h₄ using h₄
    specialize h₂ _ _ h₄
    choose y' h₂ h₆ using h₂
    simp [h₃] at h₂
    subst h₂
    use x
  replace h₃ := mem_of_get?_eq_some h₃
  apply t₁.mp.subset_of_size_eq_and_subset (by simp) (by simp) h₁ _ h₃
  clear! k
  simp [mem_mp_iff_get?_eq_some]
  intro k x h
  specialize h₂ _ _ h
  choose y h₂ h₃ using h₂
  use y

omit H in
def Alt (t₁ t₂ : Raw α β) : Prop :=
  t₁.mp.size = t₂.mp.size ∧
  (∀ k a, t₁.get? k = some a → ∃ (b : Raw α β) (_ : t₂.get? k = some b), Alt a b)
termination_by max (depth t₁) (depth t₂)
decreasing_by all_goals nm h₁ h₂; have h₁ := depth_lt h₁; have h₂ := depth_lt h₂; omega

omit H in
theorem iff_alt : t₁.Equiv t₂ ↔ Alt t₁ t₂ := by
  fun_induction Equiv
  clear! t₁ t₂
  nm t₁ t₂ ih₁ ih₂
  unfold Alt
  rw [←Equiv, iff_alt']
  constructor <;> rintro ⟨h₁, h₂⟩
  all_goals
    use h₁
    intro k x h₃
    specialize h₂ _ _ h₃
    specialize ih₁ _ _ h₃
    choose y h₂ h₄ using h₂
    specialize ih₁ _ h₂
    use y, h₂
    tauto