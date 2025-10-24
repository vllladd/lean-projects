import AP.DigitalRoot.List

namespace DigitalRoot

structure Time : Type where
  hour : Fin 24
  minute : Fin 60
deriving Inhabited, DecidableEq, Fintype, Hashable

def Time.toList (t : Time) : List ℕ :=
  [t.hour, t.minute]

def timeSet : Set' Time := Set'.univ

def digRootTime (b : ℕ) (t : Time) : ℕ :=
  digRootList b t.toList

def freqTimeCount (b d : ℕ) : ℕ :=
  timeSet.count (digRootTime b · = d)

open Classical in noncomputable
def freqTimeDig (b : ℕ) : Option ℕ := choose? # λ d =>
  d ≤ b ∧ ∀ d', d' ≠ d → freqTimeCount b d' < freqTimeCount b d

def freqTimeDigFn (b : ℕ) (mp : Map ℕ ℕ) (t : Time) : Map ℕ ℕ :=
  mp.push # digRootTime b t

variable {b} [hb : Base b]

@[simp]
theorem Time.toList_mk {hour minute} : (⟨hour, minute⟩ : Time).toList = [hour.1, minute.1] := rfl

@[simp]
theorem digRootTime_mk {hour minute} :
digRootTime b ⟨hour, minute⟩ = digRoot b (hour.1 + minute.1) := by
  simp [digRootTime]

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
theorem exi_digRootTime_eq_iff {n} : (∃ k, digRootTime 10 k = n) ↔ n < 10 := by
  constructor
  · rintro ⟨n, rfl⟩
    simp
  intro h
  use ⟨0, n, by linarith⟩
  simpa

@[simp]
theorem mem_freqTimeMp {d} : d ∈ freqTimeMp 10 ↔ d < 10 := by
  unfold freqTimeMp freqTimeDigFn
  rw [Set'.fold_map_push_eq_map_toMap]
  simp [timeSet]

theorem get?_freqTimeMp_eq {d} (hd : d < 10) :
(freqTimeMp 10).get? d = some (freqTimeCount 10 d) := by
  unfold freqTimeMp freqTimeDigFn
  rw [Set'.fold_map_push_eq_map_toMap]
  simpa [timeSet, freqTimeCount]

theorem freqTimeMp_eq : freqTimeMp 10 = Set'.toMap (Set'.ofFinset # Finset.range 10)
(λ d => freqTimeCount 10 d) := by
  ext d :1
  rw [Set'.get?_toMap_eq]
  simp
  by_cases h : d < 10
  · rw [get?_freqTimeMp_eq h]
    simpa
  push_neg at h
  rw [if_neg # by linarith]
  unfold freqTimeMp freqTimeDigFn
  rw [Set'.fold_map_push_eq_map_toMap]
  simpa [timeSet]

theorem freqTimeCount_eq_zero_of_base_le {n} (h : b ≤ n) : freqTimeCount b n = 0 := by
  simp [freqTimeCount, Set'.count_eq_zero_iff]
  intro t h₁
  apply ne_of_lt
  apply lt_of_lt_of_le _ h
  simp

@[simp]
theorem freqTimeCount_base_eq_zero : freqTimeCount b b = 0 :=
  freqTimeCount_eq_zero_of_base_le # by rfl

@[simp]
theorem freqTimeCount_base_add_eq_zero {n} : freqTimeCount b (b + n) = 0 :=
  freqTimeCount_eq_zero_of_base_le # by linarith

theorem freqTimeDig'_eq_some_of_freqTimeDig_eq_some {d}
(h : freqTimeDig 10 = some d) : freqTimeDig' 10 = some d := by
  unfold freqTimeDig at h; simp at h
  generalize hp : (λ d => d ≤ 10 ∧ ∀ d', ¬d' = d →
    freqTimeCount 10 d' < freqTimeCount 10 d) = p at h
  generalize hd₁ : Classical.epsilon p = d₁ at h
  rcases h with ⟨h₁, rfl⟩
  rename' d₁ => d
  clear! p
  rcases h₁ with ⟨h₁, h₂⟩
  simp [freqTimeDig']
  rw [freqTimeMp_eq]
  rw [le_iff_eq_or_lt] at h₁
  rcases h₁ with rfl | h₁
  · specialize h₂ 0; simp at h₂
  split
  · nm xs a b c e ys h₃
    simp
    clear xs
    generalize hx : (Set'.ofFinset (Finset.range 10) |>.toMap (freqTimeCount 10)
      |>.toList.mergeSort # λ a b => b.2 ≤ a.2) = xs at h₃
    have H : xs.Nodup
    · subst hx; simp
    have H₀ : ∀ x y, (x, y) ∈ xs ↔ x < 10 ∧ freqTimeCount 10 x = y
    · intro x y
      subst hx
      simp
    obtain ⟨H₁, H₂⟩ : freqTimeCount 10 a = b ∧ freqTimeCount 10 c = e
    · subst hx
      have h₄ := congrArg ((a, b) ∈ ·) h₃
      have h₅ := congrArg ((c, e) ∈ ·) h₃
      simp at h₄ h₅
      exact ⟨h₄.2, h₅.2⟩
    have H₃ : xs.Sorted # λ a b => b.2 ≤ a.2
    · have h₄ := @List.sorted_mergeSort (ℕ × ℕ) (λ a b => b.2 ≤ a.2)
        (by simp; intro a b c; apply le_trans') (by simp [le_total])
        (Set'.ofFinset (Finset.range 10) |>.toMap (freqTimeCount 10) |>.toList)
      simp at h₄; rwa [←hx]
    simp [h₃] at H₃
    rcases H₃ with ⟨⟨H₃, H₄⟩, H₅, H₆⟩
    have h₀ : (d, freqTimeCount 10 d) ∈ xs
    · rw [H₀]; use h₁
    symm; apply and_of
    · by_contra! h₄
      have h₅ := h₂ a h₄
      rw [H₁] at h₅
      simp [h₃, ne_symm' h₄] at h₀
      rcases h₀ with ⟨rfl, rfl⟩ | h₀
      · contrapose! H₃
        rw [←H₁]
        apply h₂
        exact h₄
      specialize H₅ _ _ h₀
      linarith
    suffices h : d = a → b ≠ e; simp [eq_comm] at h ⊢; exact h
    rintro rfl rfl
    specialize h₂ c
    simp [H₁, H₂] at h₂
    subst h₂
    simp [h₃] at H
  · nm xs h₃; clear xs
    exfalso
    simp at h₃
    generalize hx : (Set'.ofFinset (Finset.range 10) |>.toMap (freqTimeCount 10)
      |>.toList.mergeSort # λ a b => b.2 ≤ a.2) = xs at h₃
    contrapose! h₃; clear h₃
    have h₃ : xs.length = 10
    · subst hx
      simp
    iterate 2 cases xs; simp at h₃; nm x xs
    simp [Prod.ext_iff]

theorem freqTimeDig_eq_some_of_freqTimeDig'_eq_some {d}
(h : freqTimeDig' 10 = some d) : freqTimeDig 10 = some d := by
  unfold freqTimeDig; simp
  generalize hp : (λ d => d ≤ 10 ∧ ∀ d', ¬d' = d →
    freqTimeCount 10 d' < freqTimeCount 10 d) = p
  generalize hd₁ : Classical.epsilon p = d₁
  
  simp [freqTimeDig'] at h
  split at h <;> simp at h
  nm xs a b c e ys h₁; clear xs
  rcases h with ⟨h, h₂⟩
  symm at h₂; subst h₂
  
  have h₂ : ∃ d₁, p d₁
  · sorry
  
  have h₃ := Classical.epsilon_spec h₂
  rw [hd₁] at h₃; clear hd₁
  subst hp
  dsimp at h₂
  rcases h₃ with ⟨h₃, h₄⟩
  
  rw [le_iff_eq_or_lt] at h₃
  rcases h₃ with rfl | h₃
  · specialize h₄ 0
    simp at h₄
  
  sorry

-- #check 0 #exit

theorem freqTimeDig_eq_freqTimeDig' : freqTimeDig 10 = freqTimeDig' 10 := by
  ext d; constructor
  use freqTimeDig'_eq_some_of_freqTimeDig_eq_some
  use freqTimeDig_eq_some_of_freqTimeDig'_eq_some

theorem freqTimeDig_10_eq_some_5 : freqTimeDig 10 = some 5 := by
  rw [freqTimeDig_eq_freqTimeDig']; native_decide