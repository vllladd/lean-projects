import AP.DigitalRoot.List

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

theorem freqTimeDigFn_freqTimeDigFn_comm {b} {mp : Map ℕ ℕ} {t₁ t₂ : Time} :
freqTimeDigFn b (freqTimeDigFn b mp t₁) t₂ = freqTimeDigFn b (freqTimeDigFn b mp t₂) t₁ :=
  Map.push_push_comm

def freqTimeDig' (b : ℕ) : Option ℕ := do
  let res : Map ℕ ℕ := timeSet.fold (freqTimeDigFn b) ∅
    freqTimeDigFn_freqTimeDigFn_comm
  let xs := res.toList.mergeSort # λ a b => b.2 ≤ a.2
  match xs with
  | (d₁, c₁) :: (_, c₂) :: _ => do
    guard # c₁ ≠ c₂
    pure d₁
  | _ => none

-- variable {b} [hb : Base b]

-- #check 0 #exit

theorem freqTimeDig_eq_freqTimeDig' {b} : freqTimeDig b = freqTimeDig' b := by
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

-- #check 0 #exit

theorem freqTimeDig_10_eq_some_5 : freqTimeDig 10 = some 5 := by
  rw [freqTimeDig_eq_freqTimeDig']; native_decide