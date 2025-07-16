import AP.Util.Data.Set.Defs

namespace Util.Data

universe u v w
variable {α : Type u} [hh₁ : LinearOrder α] [hh₂ : Hashable α]

namespace Set

def mem (s : Set α) (i : α) : Prop :=
  DMap.mem s i

instance : Membership α (Set α) := ⟨mem⟩

protected def insert (i : α) (s : Set α) : Set α :=
  DMap.insert s i ()

instance : Insert α (Set α) := ⟨Set.insert⟩

def toList (s : Set α) : List α :=
  (DMap.toList s).map (·.1)

def ofList (xs : List α) : Set α :=
  DMap.ofList # xs.map (⟨·, ()⟩)

def toDMap {β : α → Type v} (s : Set α) (f : (i : α) → β i) : DMap α β :=
  DMap.map s # @λ i _ => f i

def toMap {β : Type v} (s : Set α) (f : α → β) : Map α β :=
  DMap.map s # @λ i _ => f i

variable {s : Set α}

theorem mem_def {i} : i ∈ s ↔ DMap.mem s i := by rfl

instance {i} : Decidable (s.mem i) := by
  change Decidable (DMap.mem s i)
  infer_instance

instance {i} : Decidable (i ∈ s) := by
  change Decidable (s.mem i)
  infer_instance

@[simp]
theorem mem_toDMap {β : α → Type v} {f : (i : α) → β i} {i} :
i ∈ s.toDMap f ↔ i ∈ s := by simp [toDMap]

@[simp]
theorem not_mem_empty' {i} : ¬(∅ : Set α).mem i := by
  simp [empty_def, mem]; exact DMap.not_mem_empty'

@[simp]
theorem not_mem_empty {i} : i ∉ (∅ : Set α) :=
  not_mem_empty'

@[simp]
theorem toDMap_empty {β : α → Type v} {f : (i : α) → β i} :
(∅ : Set α).toDMap f = ∅ := by simp [DMap.eq_empty_iff]

-- theorem ext_iff {s₁ s₂ : Set α} : s₁ = s₂ ↔ ∀ i, i ∈ s₁ ↔ i ∈ s₂ := by
--   unfold Set at s₁ s₂
--   
-- 
-- #check 0 #exit
-- 
-- @[simp]
-- theorem toDMap_eq_empty_iff {β : α → Type v} {f : (i : α) → β i} :
-- s.toDMap f = ∅ ↔ s = ∅ := by
--   symm; constructor
--   · rintro rfl
--     simp
--   · intro h
--     simp at h