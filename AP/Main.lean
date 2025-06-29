import AP.Basic

namespace AP

def get_ps (r : ℕ) : List Point := do
  let d : ℕ := r * 2 + 1
  let cs := (List.range d).map # λ i => (i : ℤ) - (r : ℤ)
  let y ← cs
  let x ← cs
  return ⟨x, y⟩

def fa (s : State) : Point :=
  let ⟨x, y⟩ := s.a_pos
  ⟨1 - x, y⟩

def fd (s : State) : Point :=
  let xs := do
    let p ← get_ps 3
    guard # s.d_valid_move p
    return p
  match xs with
  | [] => s.choose_d_move
  | (p :: _) => p

def f (s : State) : Point :=
  match s.turn with
  | .A => fa s
  | .D => fd s

instance : ToString Point := by
  constructor
  rintro ⟨x, y⟩
  exact toString (x, y)

def State.to_str (s : State) : String := String.mk # do
  let d := 5
  let p ← get_ps 5
  let ⟨x, y⟩ := p
  let sp := do
    guard # x + d = 0 ∧ y + d ≠ 0
    return '\n'
  let c := if p = s.a_pos then '@'
    else if p ∈ s.taken then '#'
    else '.'
  sp ++ [c]

instance : ToString State := ⟨State.to_str⟩

def logb : IO Unit := do
  IO.println ""
  IO.println # String.mk # List.replicate 100 '='
  IO.println ""

namespace _root_

def f' (P : ℕ → Prop) [DecidablePred P] : (n : ℕ) → (∃ k, n ≤ k ∧ P k ∧ ∀ r < k, ¬P r) → ℕ
| n, h => if hn : P n then n else f' P (n + 1) # by
  rcases h with ⟨k, h₁, h₂, h₃⟩
  refine' ⟨k, _, h₂, h₃⟩
  rw [Nat.succ_le_iff, lt_iff_le_and_ne]
  use h₁
  rintro rfl
  contradiction
termination_by n h => h.choose - n
decreasing_by
  nm a ha; clear a ha
  generalize_proofs h₁
  obtain ⟨h₂, h₃, h₄⟩ := h.choose_spec
  obtain ⟨h₅, h₆, h₇⟩ := h₁.choose_spec
  generalize h.choose = a at *
  generalize h₁.choose = b at *
  clear h h₁
  cases b <;> simp at h₅
  nm b
  simp at ⊢
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h₂
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h₅
  clear h₂ h₅
  simp
  by_contra! h₁
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h₁
  clear h₁
  specialize h₇ (n + a) # by linarith
  contradiction

def f {P : ℕ → Prop} [DecidablePred P] (h : ∃ n, P n) :=
  f' P 0 # by
    nm hp
    simp
    obtain ⟨n, hn⟩ := h
    induction n using Nat.strong_induction_on
    nm n ih
    by_cases h₁ : ∃ m < n, P m
    · obtain ⟨m, h₁, h₂⟩ := h₁
      exact ih m h₁ h₂
    simp at h₁
    use n, hn

theorem f_spec {P : ℕ → Prop} [DecidablePred P] {h : ∃ n, P n} : P (f h) ∧ ∀ k < f h, ¬P k := by
  nm hp
  obtain ⟨n, hn⟩ := h
  unfold f
  suffices h₁ : ∀ a h, P (f' P a h) ∧ ∀ k < f' P a h, ¬P k
    by
      specialize h₁ 0 _
      · clear h₁
        simp
        induction n using Nat.strong_induction_on
        nm n ih
        by_cases h₁ : ∃ m < n, P m
        · obtain ⟨m, h₁, h₂⟩ := h₁
          exact ih m h₁ h₂
        simp at h₁
        use n, hn
      exact h₁
  clear! n
  rintro k ⟨n, h₁, h₂, h₃⟩
  induction h₁ using Nat.decreasingInduction
  rotate_left
  · rw [f']
    simpa [h₂]
  clear k
  nm k h₁ ih
  rw [f']
  split_ifs with h₄
  · cases h₃ _ h₁ h₄
  exact ih

theorem f_eq_nat_find {P : ℕ → Prop} [DecidablePred P] {h : ∃ n, P n} : f h = Nat.find h := by
  nm hp
  have h₁ := Nat.find_spec h
  have h₂ : ∀ k < Nat.find h, ¬P k := λ k => Nat.find_min h
  obtain ⟨h₄, h₅⟩ : P (f h) ∧ ∀ k < f h, ¬P k := f_spec
  generalize f h = a at *
  generalize Nat.find h = b at *
  clear hp h
  by_contra h₆
  wlog h₇ : a < b with ih
  · apply @ih P b h₁ h₂ a h₄ h₅ <;> omega
  clear h₆
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt h₇
  clear h₇
  specialize h₂ a # by linarith
  contradiction

def _root_.main : IO Unit := do
  IO.println # f (by sorry : ∃ n, n * 24 = 888)
  -- let n := 100
  -- let (res, k) := Rules.simulate f (init_state 1) n
  -- IO.println # toString n ++ " ---> " ++ toString k
  -- logb
  -- IO.println # res