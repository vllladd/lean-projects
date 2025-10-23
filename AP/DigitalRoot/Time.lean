import AP.DigitalRoot.List

namespace Map

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp : Map α β}

@[simp]
theorem mem_push {mp : Map α ℕ} {x y : α} : y ∈ mp.push x ↔ y = x ∨ y ∈ mp := by
  simp [push]

-- #check 0 #exit

end Map

namespace Set'

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable [hb₁ : DecidableEq β] [hb₂ : Hashable β]
variable [hc₁ : DecidableEq γ] [hc₂ : Hashable γ]
variable {s s' s₁ s₂ s₃ : Set' α}

def toMap (s : Set' α) (f : α → β) : Map α β :=
  ⟨s.1.map # λ x _ => f x⟩

omit hb₁ hb₂ in @[simp]
theorem mem_toMap {f : α → β} {i} : i ∈ s.toMap f ↔ i ∈ s := by
  rcases s with ⟨m⟩
  simp [toMap, mem_def, Map.mem_def]

omit hb₁ hb₂ in @[simp]
theorem get?_toMap_eq_some_iff {f : α → β} {i x} :
(s.toMap f).get? i = some x ↔ i ∈ s ∧ f i = x := by
  rcases s with ⟨m⟩
  simp [toMap, Map.get?, mem_def]
  rintro rfl
  rw [Std.ExtDHashMap.mem_iff_get?_eq_some]
  simp [exi_unit_iff]

omit hb₁ hb₂ in @[simp]
theorem toMap_empty {f : α → β} : (∅ : Set' α).toMap f = ∅ := by
  ext i x; simp

#check 0 #exit

theorem fold_map_push_eq_toMap_map {f : α → β} :
s.fold (λ mp x => mp.push # f x) (∅ : Map β ℕ) Map.push_push_comm =
(s.map f).toMap (s.count # λ y => f y = ·) := by
  have Ha : LinearOrder α; sorry
  rw [fold_eq_foldl_toList]
  
  ext i x;
  simp
  
  generalize hn : s.size = n
  generalize hm : (∅ : Map β ℕ) = mp
  suffices H : List.foldl (λ mp x => mp.push (f x)) mp s.toList =
    (s.map f).toMap λ x => (mp.get? x).getD 0 + s.count λ y => f y = x
  · subst hm; simp at H; exact H
  clear hm
  
  induction n generalizing s mp
  
  · simp at hn
    subst hn
    simp

#check 0 #exit

theorem fold_map_push_eq_toMap :
s.fold (λ mp x => mp.push x) (∅ : Map α ℕ) Map.push_push_comm =
s.toMap (s.count # λ y => y = ·) := by
  convert s.fold_map_push_eq_toMap_map (f := id); simp

#check 0 #exit

end Set'

namespace DigitalRoot

structure Time : Type where
  hour : Fin 24
  minute : Fin 60
deriving Inhabited, DecidableEq, Fintype, Hashable

def Time.toList (t : Time) : List ℕ :=
  [t.hour, t.minute]

@[simp]
def timeSet : Set' Time := Set'.univ

def digRootTime (b : ℕ) (t : Time) : ℕ :=
  digRootList b t.toList

open Classical in noncomputable
def freqTimeDig (b : ℕ) : Option ℕ := choose? # λ d =>
  let f d₁ := timeSet.count (digRootTime b · = d₁)
  d ≤ b ∧ ∀ d', d' ≠ d → f d' < f d

def freqTimeDigFn (b : ℕ) (mp : Map ℕ ℕ) (t : Time) : Map ℕ ℕ :=
  mp.push # digRootTime b t

variable {b} [hb : Base b]

@[simp]
theorem digRootTime_lt_base {n} : digRootTime b n < b := by
  simp [digRootTime]

@[simp]
theorem digRootTime_le_base {n} : digRootTime b n ≤ b := by
  simp [digRootTime]

theorem freqTimeDigFn_freqTimeDigFn_comm {b} {mp : Map ℕ ℕ} {t₁ t₂ : Time} :
freqTimeDigFn b (freqTimeDigFn b mp t₁) t₂ = freqTimeDigFn b (freqTimeDigFn b mp t₂) t₁ :=
  Map.push_push_comm

def freqTimeMp (b : ℕ) : Map ℕ ℕ :=
  timeSet.fold (freqTimeDigFn b) ∅ freqTimeDigFn_freqTimeDigFn_comm

def freqTimeDig' (b : ℕ) : Option ℕ := do
  let res := freqTimeMp b
  let xs := res.toList.mergeSort # λ a b => b.2 ≤ a.2
  match xs with
  | (d₁, c₁) :: (_, c₂) :: _ => do
    guard # c₁ ≠ c₂
    pure d₁
  | _ => none

@[simp]
theorem mem_freqTimeMp {d} : d ∈ freqTimeMp b ↔ d < b := by
  have H := fintypeToLinearOrder (α := Time)
  unfold freqTimeMp freqTimeDigFn
  rw [Set'.fold_eq_foldl_toList]
  constructor
  · generalize timeSet.toList = xs
    generalize hz : (∅ : Map ℕ ℕ) = z
    replace hz : ∀ d ∈ z, d < b
    · simp [←hz]
    intro h
    induction xs generalizing z
    · simp at h; exact hz _ h
    nm x xs ih
    simp at h
    apply ih (z.push # digRootTime b x) _ h
    intro k hk
    simp at hk
    rcases hk with rfl | hk
    · simp
    exact hz _ hk
  · intro h
    

#check 0 #exit

theorem get?_freqTimeMp_eq {d} (hd : d < b) :
(freqTimeMp b).get? d = some (timeSet.count (digRootTime b · = d)) := by
  have H := fintypeToLinearOrder (α := Time)
  unfold freqTimeMp
  generalize timeSet = s
  -- generalize_proofs hh

#check 0 #exit

theorem freqTimeDig_eq_freqTimeDig' : freqTimeDig b = freqTimeDig' b := by
  have H := fintypeToLinearOrder (α := Time)
  ext d
  simp [freqTimeDig, freqTimeDig']
  constructor
  · rintro ⟨⟨h₁, h₂⟩, -⟩
    rw [Set'.fold_eq_foldl_toList]
    sorry
  · intro h
    split at h <;> simp at h
    nm xs d₁ c₁ d₂ c₂ ys h₁
    rcases h with ⟨h, rfl⟩
    apply and_of
    · constructor
      · sorry
      · intro d' h₂
        sorry
    rintro ⟨h₂, h₃⟩
    apply epsilon_eq_of ⟨h₂, h₃⟩
    rintro d₁' ⟨h₄, h₅⟩
    by_contra! h₆
    specialize h₃ _ h₆
    specialize h₅ _ # ne_symm' h₆
    linarith

#check 0 #exit

theorem freqTimeDig_10_eq_some_5 : freqTimeDig 10 = some 5 := by
  rw [freqTimeDig_eq_freqTimeDig']; native_decide