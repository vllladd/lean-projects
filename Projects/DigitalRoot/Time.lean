import Projects.DigitalRoot.List

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
    have H₃ : xs.Pairwise # λ a b => b.2 ≤ a.2
    · have h₄ := @List.pairwise_mergeSort (ℕ × ℕ) (λ a b => b.2 ≤ a.2) (by simp) (by simp)
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

@[simp]
theorem freqTimeCount_eq_zero_iff {n} : freqTimeCount 10 n = 0 ↔ 10 ≤ n := by
  symm; use freqTimeCount_eq_zero_of_base_le
  intro h
  simp [freqTimeCount, Set'.count_eq_zero_iff] at h
  simp [timeSet] at h
  contrapose! h
  use ⟨⟨0, by simp⟩, ⟨n, by linarith⟩⟩
  simpa

@[simp]
theorem freqTimeCount_pos_iff {n} : 0 < freqTimeCount 10 n ↔ n < 10 := by
  rw [iff_iff_not']; simp

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
  
  generalize hA : (freqTimeMp 10).toList.mergeSort (λ a b => b.2 ≤ a.2) = A at h₁
  
  have H₁ : ∀ x y, (x, y) ∈ A → x < 10
  · intro x y h₃
    simp [←hA] at h₃
    replace h₃ := Map.mem_of_get?_eq_some h₃
    simp at h₃
    exact h₃
  
  have H₃ : ∀ x y, (x, y) ∈ A → freqTimeCount 10 x = y
  · intro x y h₃
    have h₃' := h₃
    simp [←hA] at h₃
    rw [get?_freqTimeMp_eq] at h₃
    simp at h₃; exact h₃
    exact H₁ _ y h₃'
  
  have H₂ : A.Pairwise (λ a b => b.2 ≤ a.2)
  ·
    rw [←hA]
    have h₂ := (freqTimeMp 10).toList.pairwise_mergeSort (le := λ a b => b.2 ≤ a.2)
    specialize h₂ _ _
    · simp only [decide_eq_true_eq, Prod.forall, forall_const]
      intro a b c h₂ h₃; exact h₃.trans h₂
    · simp only [Bool.or_eq_true, decide_eq_true_eq, le_total, implies_true]
    simp at h₂
    exact h₂
  
  suffices h₂ : p d
  · have h₃ := Classical.epsilon_spec ⟨_, h₂⟩
    rw [hd₁] at h₃; clear hd₁
    subst hp
    use h₂
    rcases h₂ with ⟨h₂, h₄⟩
    rcases h₃ with ⟨h₃, h₅⟩
    by_contra! h₆
    specialize h₄ _ h₆
    specialize h₅ _ # ne_symm' h₆
    linarith
  
  clear! d₁
  
  rw [←hp]
  dsimp
  split_ands
  · apply le_of_lt
    apply H₁ _ b
    simp [h₁]
  intro d' h₂
  
  by_cases h₀ : 10 ≤ d'
  · rw [freqTimeCount_eq_zero_of_base_le h₀]
    simp
    apply H₁ _ b
    simp [h₁]
  push_neg at h₀
  
  simp [h₁] at H₂
  have h₃ := H₃ d b
  simp [h₁] at h₃
  subst h₃
  rcases H₂ with ⟨⟨h₃, h₄⟩, h₅, h₆⟩
  
  have h₇ : (d', freqTimeCount 10 d') ∈ A
  · rw [←hA]
    simp
    rwa [get?_freqTimeMp_eq]
  
  replace h : e < freqTimeCount 10 d
  · omega
  clear h₃
  
  apply lt_of_le_of_lt _ h
  
  simp [h₁, h₂] at h₇
  rcases h₇ with ⟨h₇, h₈⟩ | h₇
  · rw [h₈]
  exact h₅ _ _ h₇

theorem freqTimeDig_eq_freqTimeDig' : freqTimeDig 10 = freqTimeDig' 10 := by
  ext d; constructor
  use freqTimeDig'_eq_some_of_freqTimeDig_eq_some
  use freqTimeDig_eq_some_of_freqTimeDig'_eq_some

theorem freqTimeDig_10_eq_some_5 : freqTimeDig 10 = some 5 := by
  rw [freqTimeDig_eq_freqTimeDig']; native_decide

theorem toList_freqTimeMp_eq : (freqTimeMp 10).toList =
(List.range 10).zip [1, 159, 159, 160, 161, 162, 161, 160, 159, 158] := by
  native_decide

theorem sum_freqTimeMp_eq_24_mul_60 : (freqTimeMp 10 |>.toList.map (·.snd) |>.sum) = 24 * 60 := by
  rw [toList_freqTimeMp_eq]; native_decide