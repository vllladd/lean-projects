import AP.Util.Option
import AP.Util.Fintype

noncomputable
def Set.Finite.toFintype {α : Type*}
{sa : Set α} (ha : sa.Finite) : Fintype sa := by
  unfold Set.Finite at ha; exact ha.toFintype

-----

namespace Set

variable {α β : Type*}
variable {s s' s₁ s₂ s₃ : Set α}

def erase (x : α) (s : Set α) := s \ {x}

@[simp]
theorem mem_erase {z x : α} : z ∈ s.erase x ↔ z ≠ x ∧ z ∈ s := by
  unfold erase; aesop

theorem erase_eq_of_not_mem {x : α} (h : x ∉ s) : s.erase x = s := by
  simpa [erase]

theorem insert_erase_eq_of_mem {x : α} (h : x ∈ s) : insert x (s.erase x) = s := by
  ext z; simp; apply Iff.intro <;> intro h₁
  rcases h₁ with rfl | ⟨h₁, h₂⟩ <;> assumption
  simp [h₁]; apply eq_or_ne

@[simp]
theorem finite_erase_iff {x : α} : (s.erase x).Finite ↔ s.Finite := by
  by_cases hx : x ∈ s
  case neg => simp [erase_eq_of_not_mem hx]
  symm; apply Iff.intro Finite.diff; intro h
  generalize hs' : s.erase x = s' at h
  have hs : s = insert x s' := by
    subst hs'; rw [insert_erase_eq_of_mem hx]
  rw [←erase, hs'] at h; rw [hs]
  apply Finite.insert; exact h

@[simp]
theorem infinite_erase_iff {x : α} : (s.erase x).Infinite ↔ s.Infinite := by
  simp [Set.Infinite]

theorem diff_upair (x y : α) (s : Set α) : s \ {x, y} = (s \ {x}) \ {y} := by
  ext z; simp; tauto

@[simp]
theorem univ_ne_univ_diff_insert {x : α} : univ ≠ univ \ (insert x s) := by
  simp [Set.ext_iff]; use x; simp

@[simp]
theorem univ_ne_univ_diff_singleton {x : α} : univ ≠ univ \ {x} := by
  simp [Set.ext_iff]

@[simp]
theorem univ_ne_erase {α : Type*} {x : α} : univ ≠ univ.erase x := by
  simp [erase]

theorem diff_erase_self_eq_of_mem {x : α} (h : x ∈ s) : s \ s.erase x = {x} := by
  simpa [erase]

@[simp]
theorem subsingleton_pair_iff {x y : α} : ({x, y} : Set _).Subsingleton ↔ x = y := by
  simp [Set.Subsingleton]; simp [eq_comm]

@[simp]
theorem not_nonempty_iff : ¬s.Nonempty ↔ s = ∅ :=
  not_nonempty_iff_eq_empty

@[simp]
theorem setOf_compl {P : α → Prop} : {x | P x}ᶜ = {x | ¬P x} := rfl

@[simp]
theorem univ_injOn_iff {f : α → β} : (univ : Set α).InjOn f ↔ f.Injective := by
  simp [Set.InjOn]; rfl

@[simp]
theorem diff_eq_empty' : s \ s' = ∅ ↔ s ⊆ s' := diff_eq_empty

@[simp]
theorem exists_mem {x} : ∃ (s : Set α), x ∈ s := by
  use {x}; simp

@[simp]
theorem iUnion_preimage {f : α → β} : ⋃ b, f ⁻¹' b = univ := by
  ext x; simp

theorem minimal_le_minimal_of_subset [ha : LinearOrder α] {x y : α}
(h₁ : s' ⊆ s) (h₂ : Minimal (· ∈ s') y) (h₃ : Minimal (· ∈ s) x) : x ≤ y := by
  dsimp [Minimal] at h₂ h₃
  rcases h₂ with ⟨h₂, h₄⟩
  rcases h₃ with ⟨h₃, h₅⟩
  have h₆ := h₁ h₂
  by_contra! h₇
  specialize h₅ h₆ (le_of_lt h₇)
  contrapose! h₇
  exact h₅

theorem eq_empty_iff : s = ∅ ↔ ∀ x, x ∉ s :=
  eq_empty_iff_forall_notMem

theorem ne_empty_iff : s ≠ ∅ ↔ ∃ x, x ∈ s := by
  simp [eq_empty_iff]

theorem ne_empty_of (x : α) (h : x ∈ s) : s ≠ ∅ := by
  simp [ne_empty_iff]; use x

@[simp]
theorem erase_singleton {x : α} : ({x} : Set α).erase x = ∅ := by
  ext; simp

def filter (s : Set α) (p : α → Prop) : Set α :=
  {x ∈ s | p x}

@[simp]
theorem mem_filter {p x} : x ∈ s.filter p ↔ x ∈ s ∧ p x := by
  simp [filter]

@[simp]
theorem filter_const_true : s.filter (λ _ => True) = s := by
  simp [filter]

@[simp]
theorem filter_const_false : s.filter (λ _ => False) = ∅ := by
  simp [filter]

theorem filter_fn_mem : s.filter (· ∈ s₁) = s ∩ s₁ := by
  simp [filter]

theorem forall_not_mem_iff : (∀ x, x ∉ s) ↔ s = ∅ := by
  grind

@[simp]
theorem not_finite_iff_infinite : ¬s.Finite ↔ s.Infinite := by
  rfl

theorem exi_mem_of_infinite (h : s.Infinite) : ∃ x, x ∈ s := by
  contrapose! h; rw [forall_not_mem_iff] at h; simp [h]

theorem exi_min [ha : LinearOrder α]
(h₁ : s.Finite) (h₂ : s.Nonempty) : ∃ x ∈ s, ∀ y ∈ s, x ≤ y :=
  exists_min_image _ id h₁ h₂

theorem exi_max [ha : LinearOrder α]
(h₁ : s.Finite) (h₂ : s.Nonempty) : ∃ x ∈ s, ∀ y ∈ s, y ≤ x :=
  exists_max_image _ id h₁ h₂