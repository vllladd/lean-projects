import AP.RealAnalysis.RationalFn

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
(_ : ∀ n, ε ≤ |a (σ n) - a (τ n)|), Subseq τ ∨ Subseq σ := by
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
  · simp [Subseq]
    use 0, 1, by norm_num
    simp
  · simp [Subseq]
    use 0, 1, by norm_num
    simp

theorem subseq_iff_lt_add_one {σ : ℕ → ℕ} :
Subseq σ ↔ ∀ n, σ n < σ (n + 1) := by
  constructor
  · intro h n
    apply h
    simp
  intro h k n h₁
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h₁; clear h₁
  induction n generalizing k
  · apply h
  nm n ih
  simp [←add_assoc]
  apply ih _ |>.trans
  apply h

theorem subseq_iterate_of_id_lt {σ : ℕ → ℕ}
(h : ∀ n, n < σ n) {n} : Subseq (σ^[·] n) := by
  rw [subseq_iff_lt_add_one]
  intro k
  rw [Function.iterate_succ']
  apply h

theorem exi_Subseq_of_forall_exi_gt {p : ℕ → Prop}
(h : ∀ N, ∃ n, N < n ∧ p n) : ∃ σ, Subseq σ ∧ ∀ n, p (σ n) := by
  choose σ h₁ h₂ using h
  use (σ^[· + 1] 0)
  constructor
  · apply subseq_iterate_of_id_lt
    intro n; apply h₁
  intro n
  rw [Function.iterate_succ']
  apply h₂

theorem exi_Subseq_of_forall_exi_le {p : ℕ → Prop}
(h : ∀ N, ∃ n, N ≤ n ∧ p n) : ∃ σ, Subseq σ ∧ ∀ n, p (σ n) := by
  apply exi_Subseq_of_forall_exi_gt
  intro N
  specialize h # N + 1
  obtain ⟨n, h₁, h₂⟩ := h
  use n, by linarith

theorem subseq_comp {σ₁ σ₂} (h₁ : Subseq σ₁) (h₂ : Subseq σ₂) : Subseq (σ₁ ∘ σ₂) := by
  rw [subseq_iff_lt_add_one]
  intro n
  apply h₁
  apply h₂
  simp

theorem forall_exi_le_or_forall_exi_ge {a : ℕ → ℝ} {L : ℝ} :
(∀ N, ∃ n, N ≤ n ∧ a n ≤ L) ∨ (∀ N, ∃ n, N ≤ n ∧ L ≤ a n) := by
  rw [or_iff_not_imp_left]
  intro h₁ N
  push_neg at h₁
  obtain ⟨N₁, h₁⟩ := h₁
  use N + N₁, by linarith
  apply le_of_lt
  apply h₁
  linarith

@[simp] theorem monoLe_const {M : ℝ} : monoLe (λ _ => M) := by simp [monoLe]
@[simp] theorem monoGe_const {M : ℝ} : monoGe (λ _ => M) := by simp [monoGe]

@[simp]
theorem not_monoLt_const {M : ℝ} : ¬monoLt (λ _ => M) := by
  simp [monoLt]; use 0, 1; norm_num

@[simp]
theorem not_monoGt_const {M : ℝ} : ¬monoGt (λ _ => M) := by
  simp [monoGt]; use 0, 1; norm_num

def DivergesToInf (a : ℕ → ℝ) : Prop :=
  ∀ M, 0 < M → eventually (λ n => M < a n)

theorem divergesToInf_mul_left {a b : ℕ → ℝ} {L : ℝ} (ha : DivergesToInf a)
(hb : tendsTo b L) (hL : 0 < L) : DivergesToInf (a * b) := by
  intro M hM
  specialize hb (L / 2) (by bound)
  choose N hb using hb
  specialize ha (M / L * 2) (by bound)
  choose N1 ha using ha
  use N + N1
  intro n hn
  specialize ha n (by linarith)
  specialize hb n (by linarith)
  rw [abs_lt] at hb
  replace hb : L / 2 < b n := by linarith
  have h₁ : M / L * 2 * (L / 2) < a n * b n
  · apply mul_lt_mul_of_pos <;> bound
  field_simp at h₁
  exact h₁