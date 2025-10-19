import AP.RealAnalysis.BolzanoWeierstrass

namespace RealAnalysis

def monoLe (a : ℕ → ℝ) : Prop :=
  ∀ i j, i ≤ j → a i ≤ a j

def monoLt (a : ℕ → ℝ) : Prop :=
  ∀ i j, i < j → a i < a j

def monoGe (a : ℕ → ℝ) : Prop :=
  ∀ i j, i ≤ j → a j ≤ a i

def monoGt (a : ℕ → ℝ) : Prop :=
  ∀ i j, i < j → a j < a i

theorem monoLe_iff_le_succ {a} : monoLe a ↔ ∀ n, a n ≤ a (n + 1) := by
  use λ h n => h n (n + 1) # by simp
  intro h k n hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk; clear hk
  induction n; simp; nm n ih
  rw [←Nat.add_assoc]
  exact ih.trans # h _

theorem monoLt_iff_lt_succ {a} : monoLt a ↔ ∀ n, a n < a (n + 1) := by
  use λ h n => h n (n + 1) # by simp
  intro h k n hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk; clear hk
  induction n; simp [h]; nm n ih
  rw [←Nat.add_assoc]
  exact ih.trans # h _

theorem monoGe_iff_succ_le {a} : monoGe a ↔ ∀ n, a (n + 1) ≤ a n := by
  use λ h n => h n (n + 1) # by simp
  intro h k n hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk; clear hk
  induction n; simp; nm n ih
  rw [←Nat.add_assoc]
  exact ih.trans' # h _

theorem monoGt_iff_succ_lt {a} : monoGt a ↔ ∀ n, a (n + 1) < a n := by
  use λ h n => h n (n + 1) # by simp
  intro h k n hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk; clear hk
  induction n; simp [h]; nm n ih
  rw [←Nat.add_assoc]
  exact ih.trans' # h _

theorem iterate_gap' {a : ℕ → ℝ} {τ σ : ℕ → ℕ} {ε : ℝ} {i k : ℕ}
(ha : monoLe a) (hτ : ∀ n, n ≤ τ n) (h : ∀ n, ε ≤ a (σ n) - a (τ n)) :
k * ε ≤ a (σ^[k] i) - a i := by
  induction k; simp; nm k ih
  rw [Function.iterate_succ']
  simp [add_mul]
  suffices : ε ≤ a (σ # σ^[k] i) - a (σ^[k] i); linarith; clear ih
  generalize σ^[k] i = n; clear k
  specialize h n
  suffices H : a n ≤ a (τ n); linarith
  apply ha
  apply hτ

theorem iterate_gap {a : ℕ → ℝ} {τ σ : ℕ → ℕ} {ε : ℝ} {i k : ℕ}
(ha : monoLe a) (hτ : ∀ n, n ≤ τ n) (hσ : ∀ n, τ n ≤ σ n)
(h : ∀ n, ε ≤ |a (σ n) - a (τ n)|) : k * ε ≤ a (σ^[k] i) - a i := by
  apply iterate_gap' ha hτ
  intro n
  specialize h n
  rw [abs_of_nonneg] at h; exact h
  simp
  apply ha
  apply hσ

theorem misc₁ {a : ℕ → ℝ} {τ σ : ℕ → ℕ} {ε : ℝ} {k : ℕ}
(hε : 0 < ε) (hσ : ∀ n, τ n ≤ σ n) (h : ∀ n, ε ≤ |a (σ n) - a (τ n)|) : τ k < σ k := by
  apply lt_of_le_of_ne; apply hσ
  intro h₁
  specialize h k
  simp [h₁] at h
  linarith

theorem monoLe_of_monoLt {a} (h : monoLt a) : monoLe a := by
  intro i j h₁; rw [le_iff_eq_or_lt] at h₁; rcases h₁ with rfl | h₁
  rfl; apply le_of_lt; apply h; exact h₁

theorem monoGe_of_monoGt {a} (h : monoGt a) : monoGe a := by
  intro i j h₁; rw [le_iff_eq_or_lt] at h₁; rcases h₁ with rfl | h₁
  rfl; apply le_of_lt; apply h; exact h₁

@[simp]
theorem monoLe_neg {a} : monoLe (-a) ↔ monoGe a := by
  unfold monoLe monoGe; simp

@[simp]
theorem monoLt_neg {a} : monoLt (-a) ↔ monoGt a := by
  unfold monoLt monoGt; simp

@[simp]
theorem monoGe_neg {a} : monoGe (-a) ↔ monoLe a := by
  unfold monoLe monoGe; simp

@[simp]
theorem monoGt_neg {a} : monoGt (-a) ↔ monoLt a := by
  unfold monoLt monoGt; simp

theorem misc₂ : ¬∀ {a : ℕ → ℝ} {τ σ : ℕ → ℕ} {ε : ℝ}
(_ : monoLe a) (_ : ∀ n, n ≤ τ n) (_ : ∀ n, τ n ≤ σ n)
(_ : ∀ n, ε ≤ |a (σ n) - a (τ n)|), subseq τ ∨ subseq σ := by
  push_neg
  use (·)
  use λ n => n + if Even n then 1 else 0
  use λ n => n * 2 + if Even n then 2 else 0
  use 1
  split_ands
  · simp [monoLe]
  · omega
  · intro n; split_ifs <;> linarith
  · intro n
    rw [abs_of_pos]
    · simp; split_ifs with h; linarith
      simp at h⊢
      cases n; simp at h
      nm n; simp
      linarith
    simp
    split_ifs with h; linarith
    simp
    cases n; simp at h
    nm n; simp; linarith
  · simp [subseq]
    use 0, 1, by norm_num
    simp
  · simp [subseq]
    use 0, 1, by norm_num
    simp