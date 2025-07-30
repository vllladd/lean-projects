import AP.Util.Fintype

noncomputable
def Set.Finite.toFintype {α : Type*}
{sa : Set α} (ha : sa.Finite) : Fintype sa := by
  unfold Set.Finite at ha; exact ha.toFintype

-----

namespace Set

def erase {α : Type*} (x : α) (s : Set α) := s \ {x}

@[simp]
theorem mem_erase {α : Type*} {z x : α} (s : Set α) :
z ∈ s.erase x ↔ z ≠ x ∧ z ∈ s := by
  unfold erase; aesop

theorem erase_eq_of_not_mem {α : Type*} {x : α} {s : Set α}
(h : x ∉ s) : s.erase x = s := by simpa [erase]

theorem insert_erase_eq_of_mem {α : Type*} {x : α} {s : Set α}
(h : x ∈ s) : insert x (s.erase x) = s := by
  ext z; simp; apply Iff.intro <;> intro h₁
  rcases h₁ with rfl | ⟨h₁, h₂⟩ <;> assumption
  simp [h₁]; apply eq_or_ne

theorem ne_none_of_eq_some {α : Type*} {m : Option α} {x : α}
(h : m = some x) : m ≠ none := by simp [h]

def List.snoc {α : Type*} (xs : List α) (x : α) := xs ++ [x]

@[simp]
theorem finite_erase_iff {α : Type*} {x : α} {s : Set α} :
(s.erase x).Finite ↔ s.Finite := by
  by_cases hx : x ∈ s
  case neg => simp [erase_eq_of_not_mem hx]
  symm; apply Iff.intro Finite.diff; intro h
  generalize hs' : s.erase x = s' at h
  have hs : s = insert x s' := by
    subst hs'; rw [insert_erase_eq_of_mem hx]
  rw [←erase, hs'] at h; rw [hs]
  apply Finite.insert; exact h

@[simp]
theorem infinite_erase_iff {α : Type*} {x : α} {s : Set α} :
(s.erase x).Infinite ↔ s.Infinite := by simp [Set.Infinite]

theorem diff_upair {α : Type*} (x y : α) (s : Set α) :
s \ {x, y} = (s \ {x}) \ {y} := by ext z; simp; tauto

@[simp]
theorem univ_ne_univ_diff_insert {α : Type*} {x : α} {s : Set α} :
univ ≠ univ \ (insert x s) := by
  simp [Set.ext_iff]; use x; simp

@[simp]
theorem univ_ne_univ_diff_singleton {α : Type*} {x : α} :
univ ≠ univ \ {x} := by simp [Set.ext_iff]

@[simp]
theorem univ_ne_erase {α : Type*} {x : α} :
univ ≠ univ.erase x := by simp [erase]

theorem diff_erase_self_eq_of_mem {α : Type*} {x : α} {s : Set α}
(h : x ∈ s) : s \ s.erase x = {x} := by simpa [erase]

theorem eq_empty_iff {α : Type*} {s : Set α} : s = ∅ ↔ ∀ x, x ∉ s :=
  eq_empty_iff_forall_notMem

@[simp]
theorem subsingleton_upair_iff {α : Type*} {x y : α} :
({x, y} : Set _).Subsingleton ↔ x = y := by
  simp [Set.Subsingleton]; simp [eq_comm]

@[simp]
theorem not_nonempty_iff {α : Type*} {s : Set α} :
¬s.Nonempty ↔ s = ∅ := not_nonempty_iff_eq_empty

@[simp]
theorem setOf_compl {α : Type*} {P : α → Prop} :
{x | P x}ᶜ = {x | ¬P x} := rfl

@[simp]
theorem univ_injOn_iff {α β : Type*} {f : α → β} :
(univ : Set α).InjOn f ↔ f.Injective := by simp [Set.InjOn]; rfl