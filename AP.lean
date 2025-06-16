import AP.Main

structure Accessor (α : Type) : Type where
  xs : List α
  i : ℕ
  valid : Bool
  h₁ : valid ↔ xs ≠ []
  h₂ : valid → i < xs.length

@[simp]
def mk_accessor {α : Type} [DecidableEq α] (xs : List α) : Accessor α :=
  { xs := xs
  , i := 0
  , valid := xs ≠ []
  , h₁ := by simp
  , h₂ := by cases xs <;> simp
  }

@[simp]
def Accessor.get {α : Type} [Inhabited α] [DecidableEq α] (a : Accessor α) : α :=
  if h : a.valid then
    by
      refine' a.xs[a.i]'_
      exact a.h₂ h
  else default

@[simp]
def Accessor.invalid {α : Type} [Inhabited α] [DecidableEq α] : Accessor α :=
  { xs := []
  , i := 0
  , valid := false
  , h₁ := by simp
  , h₂ := by simp
  }

@[simp]
def Accessor.next {α : Type} [Inhabited α] [DecidableEq α] (a : Accessor α) :
(Accessor α) :=
  if h : a.xs.length ≤ a.i + 1
  then Accessor.invalid else
    { a with
      i := a.i + 1
    , h₁ :=
      by
        have h₂ := a.h₂
        simp [a.h₁] at h₂ ⊢
    , h₂ :=
      by
        intro hv
        have h₂ := a.h₂
        specialize h₂ hv
        linarith
    }

def fn' (acc : ℕ) (a : Accessor ℕ) : ℕ :=
  if a.valid then fn' (acc + a.get) a.next else acc
termination_by a.xs.length - a.i + if a.valid then 1 else 0
decreasing_by
  nm h; simp [h]
  rw [a.h₁] at h
  split_ifs with h₁ h₂ h₂
  · exfalso; revert h₂; decide
  · simp [Accessor.invalid]
  · simp at h₁ h₂ ⊢
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h₁
    simp [hk]
    ring_nf
    omega
  · simp [a.h₁, h] at h₂

-- #check 0 #exit

@[simp]
def fn (xs : List ℕ) : ℕ :=
  fn' 0 # mk_accessor xs

def x : ℕ :=
  fn [1, 2, 3, 4, 5]

@[simp]
theorem fn'_eq {acc xs i valid h₁ h₂} :
fn' acc ⟨xs, i, valid, h₁, h₂⟩ =
if valid then fn' (acc + Accessor.get ⟨xs, i, valid, h₁, h₂⟩)
(Accessor.next ⟨xs, i, valid, h₁, h₂⟩) else acc := by
  nth_rewrite 1 [fn']; rfl

theorem x_eq : x.repr = "15" := by
  suffices x = 15 by rw [this]; rfl
  reduce
  simp

def main : IO Unit := do
  IO.println x.repr