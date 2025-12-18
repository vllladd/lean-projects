import AP.RealAnalysis.Completeness

namespace RealAnalysis

def series (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, a i

def AbsConv (a : ℕ → ℝ) : Prop :=
  converges # series (|a ·|)

-----

theorem series_eq {a} : series a = λ n => ∑ i ∈ Finset.range n, a i := rfl

@[simp]
theorem series_zero {a} : series a 0 = 0 := by
  simp [series]

theorem series_succ {a n} : series a (n + 1) = series a n + a n := by
  simp [series, Finset.sum_range_succ]

@[simp]
theorem series_const {x n} : series (λ _ => x) n = n * x := by
  simp [series]

theorem tendsTo_zero_of_converges_series {a} (h : converges (series a)) : tendsTo a 0 := by
  choose S h using h
  intro e he
  simp
  unfold eventually
  specialize h (e / 2) (by positivity)
  choose N h using h
  dsimp at h
  use N
  intro n hn
  have h₁ := h n hn
  have h₂:= h (n + 1) (by omega)
  clear h
  rw [series_succ] at h₂
  replace h₂ : |series a n - S + a n| < e / 2; ring_nf at h₂ ⊢; exact h₂
  generalize series a n - S = x at h₁ h₂
  by_contra! h₃
  suffices : e < e; linarith
  calc
  _ ≤ |a n| := h₃
  _ = |a n + x - x| := by simp
  _ ≤ |a n + x| + |x| := by rw [sub_eq_add_neg]; apply abs_add_le _ _ |>.trans; simp
  _ < _ := by rw [add_comm _ x]; linarith

@[simp]
theorem inv_add_tendsTo_zero {x : ℝ} : tendsTo (λ n => (n + x)⁻¹) 0 := by
  rw [tendsTo_iff_eps_lt_one]
  intro e he he₁
  simp
  choose N h₁ using exists_nat_gt # e⁻¹ + |x|
  use N
  intro n hn
  replace hn : (N : ℝ) ≤ n; exact_mod_cast hn
  have h₃ : e⁻¹ < n - |x|
  · calc
    _ < n - |x| := by linarith
    _ ≤ _ := by simp
  have h₄ : e⁻¹ < n + x
  · apply lt_of_lt_of_le h₃
    rw [sub_eq_add_neg, add_le_add_iff_left]
    exact neg_abs_le x
  have h₂ : 0 < n + x
  · calc
    _ < e⁻¹ := by positivity
    _ ≤ _ := by linarith
  rw [inv_lt_iff_one_lt_mul₀, abs_of_pos] <;> try positivity
  calc
  _ = e * e⁻¹ := by rw [mul_inv_cancel₀]; positivity
  _ < _ := by nlinarith

theorem add_div_add_tendsTo_one_aux₁ {x y : ℝ} (hy : 0 < y) :
tendsTo (λ n => (n + x) / (n + y)) 1 := by
  rw [show x = y + (x - y) by ring_nf]
  simp_rw [←add_assoc]
  have h : ∀ (n : ℕ) x, (n + y + x) / (n + y) = 1 + x / (n + y)
  · intro n x
    rw [same_add_div]
    positivity
  simp_rw [h]; clear h
  nth_rw 2 [show (1 : ℝ) = 1 + 0 by norm_num]
  apply tendsTo_add # by simp
  rw [show 0 = (x - y) * 0 by simp]
  apply tendsTo_mul # by simp
  simp

@[simp]
theorem add_div_add_tendsTo_one {x y : ℝ} : tendsTo (λ n => (n + x) / (n + y)) 1 := by
  choose k hk using exists_nat_gt |y|
  rw [←tendsTo_drop_iff (k := k)]
  simp [add_comm k, add_assoc]
  apply add_div_add_tendsTo_one_aux₁
  rw [abs_lt] at hk
  linarith

@[simp]
theorem add_div_tendsTo_one {x : ℝ} : tendsTo (λ n => (n + x) / n) 1 := by
  convert add_div_add_tendsTo_one (y := 0); simp

@[simp]
theorem div_add_tendsTo_one {x : ℝ} : tendsTo (λ n => n / (n + x)) 1 := by
  convert add_div_add_tendsTo_one (x := 0); simp

theorem leibniz_sum {n} : ∑ i ∈ Finset.range n, (1 : ℝ) / ((i + 1) * (i + 2)) = n / (n + 1) := by
  induction n
  · simp
  nm n ih
  rw [Finset.sum_range_succ, ih]; clear ih
  simp
  field_simp
  ring_nf

theorem leibniz_sum' {n} : ∑ i ∈ Finset.range n,
(1 : ℝ) / ((i + 1) * (i + 2)) = 1 - 1 / (n + 1) := by
  rw [leibniz_sum]; field_simp; simp

theorem leibniz_series_tendsTo : tendsTo (series λ n => 1 / ((n + 1) * (n + 2))) 1 := by
  simp_rw [series_eq, leibniz_sum]; simp

theorem series_le_of_le {a b n} (h₁ : ∀ n, a n ≤ b n) : series a n ≤ series b n := by
  dsimp [series]
  apply Finset.sum_le_sum
  intro n hn
  apply h₁

theorem converges_of_monoLe_and_forall_le_add {a b x} (h₁ : converges b)
(h₂ : monoLe a) (h₃ : ∀ n, a n ≤ b n + x) : converges a := by
  apply converges_of_monoLe_and_bounded_top h₂; use ub b + x; intro n
  apply h₃ n |>.trans # le_of_lt _; simp; apply lt_ub_of_converges h₁

theorem converges_of_monoLe_and_forall_le {a b} (h₁ : converges b)
(h₂ : monoLe a) (h₃ : ∀ n, a n ≤ b n) : converges a := by
  convert converges_of_monoLe_and_forall_le_add (x := 0) h₁ h₂ _; simpa

theorem series_add {a n k} : series a (n + k) =
series a n + series (a # n + ·) k := by
  simp [series, Finset.sum_range_add]

theorem series_add' {a n k} : series a (n + k) =
series a k + series (a # k + ·) n := by
  rw [add_comm, series_add]

theorem converges_basel {x} : converges # series # λ n => (1 / (n + x) ^ 2) := by
  choose k hk using exists_nat_gt # |x| + 2
  generalize hy : ∑ i ∈ Finset.range k, (1 : ℝ) / (i + x) ^ 2 = y
  rw [←converges_drop_iff (k := k)]
  apply converges_of_monoLe_and_forall_le_add (x := y) ⟨_, leibniz_series_tendsTo⟩
  · rw [monoLe_iff_le_succ]; intro n
    simp [Nat.add_one_add, series_succ]
  intro n
  rw [add_comm, series_add, add_comm _ y]
  rw [←series] at hy
  rw [hy]
  simp
  apply series_le_of_le
  clear n
  intro n
  field_simp
  have h₁ := add_abs_nonneg x
  rw [div_le_iff₀ # by rw [sq_pos_iff]; linarith]
  ring_nf
  nlinarith

@[simp]
theorem subseq_add_right {k : ℕ} : Subseq (· + k) := by
  rw [subseq_iff_lt_add_one]; omega

@[simp]
theorem subseq_add_left {k : ℕ} : Subseq (k + ·) := by
  rw [subseq_iff_lt_add_one]; omega

@[simp]
theorem subseq_mul_right {k : ℕ} (h : k ≠ 0) : Subseq (· * k) := by
  rw [subseq_iff_lt_add_one]; cases k; simp at h; ring_nf; omega

@[simp]
theorem subseq_mul_left {k : ℕ} (h : k ≠ 0) : Subseq (k * ·) := by
  rw [subseq_iff_lt_add_one]; cases k; simp at h; ring_nf; omega

theorem pow_tendsTo_zero_of_pos_and_lt_one {x : ℝ}
(h₁ : 0 < x) (h₂ : x < 1) : tendsTo (x ^ ·) 0 := by
  generalize ha : (x ^ ·) = a
  replace ha : ∀ n, a n = x ^ n
  · simp [←ha]
  have h₃ : monoGt a
  · rw [monoGt_iff_succ_lt]
    intro n
    simp [ha]
    rw [pow_lt_pow_iff_right_of_lt_one₀] <;> linarith
  have h₄ : ∀ n, 0 < a n
  · intro n
    rw [ha]
    positivity
  have h₅ := converges_of_monoGt_and_bounded_bottom h₃
  specialize h₅ _
  · use 0
    intro n
    exact le_of_lt # h₄ n
  choose L h₅ using h₅
  have h₆ : tendsTo (λ n => a # n * 2) L
  · apply tendsTo_subseq h₅
    simp
  have h₇ : tendsTo (λ n => a # n * 2) (L ^ 2)
  · simp_rw [ha, pow_mul, ←ha]
    exact tendsTo_pow h₅
  have h := tendsTo_unique h₆ h₇
  convert h₅
  symm
  replace h : L * (L - 1) = 0
  · nlinarith
  simp at h
  rcases h with h | h; exact h
  exfalso
  simp [sub_eq_iff_eq_add] at h
  subst h
  contrapose h₅; clear h₅
  simp [tendsTo, eventually]
  use 1 - x, by linarith
  intro N
  use N + 1, by simp
  rw [ha]
  rw [abs_of_neg]
  rotate_left
  · simp
    rwa [pow_lt_one_iff_of_nonneg]
    linarith; simp
  simp
  suffices h : x ^ (N + 1) ≤ x ^ 1
  · linarith
  rw [pow_le_pow_iff_right_of_lt_one₀ h₁ h₂]
  simp

theorem geom_series_eq {x : ℝ} {n : ℕ} (h : x ≠ 1) :
series (x ^ ·) n = (1 - x ^ n) / (1 - x) := by
  rw [series, Finset.sum_geom_eq h]

theorem geom_series_eq_ext {x : ℝ} (h : x ≠ 1) :
series (x ^ ·) = λ n => (1 - x ^ n) / (1 - x) := by
  ext n; exact geom_series_eq h

theorem geom_series_tendsTo {x : ℝ} (h₁ : 0 < x) (h₂ : x < 1) :
tendsTo (series (x ^ ·)) # 1 / (1 - x) := by
  rw [geom_series_eq_ext # by linarith]
  apply tendsTo_div
  · linarith
  · nth_rw 2 [show (1 : ℝ) = 1 - 0 by norm_num]
    apply tendsTo_sub # by simp
    exact pow_tendsTo_zero_of_pos_and_lt_one h₁ h₂
  · simp

theorem limit_le_limit_of_forall_le {a b L M} (h₁ : tendsTo a L) (h₂ : tendsTo b M)
(h₃ : ∀ n, a n ≤ b n) : L ≤ M := by
  have h₄ := tendsTo_sub h₂ h₁
  have h₅ : 0 ≤ M - L
  · apply le_limit_of_forall_le h₄; simpa
  linarith

example : ¬∀ {a L}, tendsTo (|a ·|) L ↔ 0 ≤ L ∧ tendsTo a L := by
  push_neg
  use λ n => if Even n then 1 else -1
  use 1
  simp
  left
  split_ands
  · simp_rw [apply_ite]
    simp
  intro h
  replace h := converges_of_tendsTo h
  contrapose h
  apply not_converges_alternating
  norm_num

theorem tendsTo_zero_of_abs_tendsTo {a} (h : tendsTo (|a ·|) 0) : tendsTo a 0 := by
  intro e he
  specialize h e he
  choose N h using h
  use N
  intro n hn
  specialize h n hn
  simp at h ⊢; exact h

theorem abs_tendsTo_zero_iff {a} : tendsTo (|a ·|) 0 ↔ tendsTo a 0 := by
  use tendsTo_zero_of_abs_tendsTo; convert tendsTo_abs; simp

theorem le_limit_of_monoLe' {a L n} (h₁ : monoLe a) (h₂ : tendsTo a L) : a n ≤ L := by
  by_contra! h₃
  specialize h₂ ((a n - L) / 2) (by linarith)
  choose N h₂ using h₂
  specialize h₂ (N + n) (by linarith)
  have h₄ : a n ≤ a (N + n)
  · apply h₁; simp
  rw [abs_of_pos # by linarith] at h₂
  linarith

theorem limit_le_of_monoGe' {a L n} (h₁ : monoGe a) (h₂ : tendsTo a L) : L ≤ a n := by
  replace h₁ : monoLe (-a); simpa
  replace h₂ := tendsTo_neg h₂
  suffices h : (-a) n ≤ -L
  · simp at h; exact h
  exact le_limit_of_monoLe' h₁ h₂

theorem le_limit_of_monoLe {a L} (h₁ : monoLe a) (h₂ : tendsTo a L) : ∀ n, a n ≤ L :=
  λ _ => le_limit_of_monoLe' h₁ h₂

theorem limit_le_of_monoGe {a L} (h₁ : monoGe a) (h₂ : tendsTo a L) : ∀ n, L ≤ a n :=
  λ _ => limit_le_of_monoGe' h₁ h₂

@[simp]
theorem monoLe_series_abs {a : ℕ → ℝ} : monoLe # series (|a ·|) := by
  simp [monoLe_iff_le_succ, series_succ]

@[simp]
theorem monoLe_series_abs' {a : ℕ → ℝ} : monoLe # series |a| :=
  monoLe_series_abs

theorem abs_series_le_series_abs {a : ℕ → ℝ} {n} : |series a n| ≤ series (|a ·|) n :=
  Finset.abs_sum_le_sum_abs _ _

theorem converges_series_of_absConv {a} (h : AbsConv a) : converges (series a) := by
  rw [AbsConv] at h
  rw [converges_iff_isCauchy, isCauchy_iff_alt₁] at h ⊢
  intro e he
  specialize h e he
  choose N h using h
  use N
  intro n hn
  specialize h n hn
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn; clear hn
  rw [series_add] at h ⊢
  ring_nf at h ⊢
  apply lt_of_le_of_lt abs_series_le_series_abs
  apply lt_of_le_of_lt _ h
  apply le_abs_self

theorem series_sub_series_of_le {a n m} (h : n ≤ m) :
series a m - series a n = ∑ i ∈ Finset.Ico n m, a i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
  rw [series_add]
  ring_nf
  rw [series, Finset.range_eq_Ico, Finset.sum_Ico_add, add_comm m]
  simp

theorem sum_range_mul_two_alternating {a : ℕ → ℝ} {m : ℕ} :
∑ k ∈ Finset.range (m * 2), (-1) ^ k * a k =
∑ k ∈ Finset.range m, (a (k * 2) - a (k * 2 + 1)) := by
  induction m
  · simp
  nm m ih
  simp [Nat.succ_mul, Finset.sum_range_succ]
  rw [ih]; clear ih
  rw [Finset.sum_sub_distrib]
  ring_nf

theorem subseq_lt_of_lt {σ i j} (h₁ : Subseq σ)  (h₂ : i < j) : σ i < σ j :=
  h₁ _ _ h₂

theorem subseq_le_of_le {σ i j} (h₁ : Subseq σ)  (h₂ : i ≤ j) : σ i ≤ σ j := by
  rw [le_iff_eq_or_lt] at h₂
  rcases h₂ with rfl | h₂; rfl
  exact le_of_lt # subseq_lt_of_lt h₁ h₂

theorem subseq_eq_of_eq {σ : ℕ → ℕ} {i j} (h₂ : i = j) : σ i = σ j := by
  rw [h₂]

theorem eq_of_subseq_eq {σ i j} (h₁ : Subseq σ) (h₂ : σ i = σ j) : i = j := by
  contrapose! h₂
  rw [ne_iff_lt_or_gt] at h₂ ⊢
  rcases h₂ with h₂ | h₂
  · left; exact subseq_lt_of_lt h₁ h₂
  · right; exact subseq_lt_of_lt h₁ h₂

theorem subseq_eq_iff {σ i j} (h₁ : Subseq σ) : σ i = σ j ↔ i = j :=
  ⟨eq_of_subseq_eq h₁, subseq_eq_of_eq⟩

theorem lt_of_subseq_lt {σ i j} (h₁ : Subseq σ) (h₂ : σ i < σ j) : i < j := by
  contrapose! h₂; exact subseq_le_of_le h₁ h₂

theorem subseq_lt_iff {σ i j} (h₁ : Subseq σ) : σ i < σ j ↔ i < j :=
  ⟨lt_of_subseq_lt h₁, subseq_lt_of_lt h₁⟩

theorem le_of_subseq_le {σ i j} (h₁ : Subseq σ) (h₂ : σ i ≤ σ j) : i ≤ j := by
  contrapose! h₂; exact subseq_lt_of_lt h₁ h₂

theorem subseq_le_iff {σ i j} (h₁ : Subseq σ) : σ i ≤ σ j ↔ i ≤ j :=
  ⟨le_of_subseq_le h₁, subseq_le_of_le h₁⟩

theorem subseq_ne_of_ne {σ i j} (h₁ : Subseq σ) (h₂ : i ≠ j) : σ i ≠ σ j := by
  simpa [subseq_eq_iff h₁]

theorem ne_of_subseq_ne {σ i j} (h₁ : Subseq σ) (h₂ : σ i ≠ σ j) : i ≠ j := by
  simp [subseq_eq_iff h₁] at h₂; exact h₂

theorem subseq_ne_iff {σ i j} (h₁ : Subseq σ) : σ i ≠ σ j ↔ i ≠ j :=
  ⟨ne_of_subseq_ne h₁, subseq_ne_of_ne h₁⟩

theorem monoLe_subseq {a σ} (h₁ : monoLe a) (h₂ : Subseq σ) : monoLe (a # σ ·) := by
  intro i j h; apply h₁; exact subseq_le_of_le h₂ h

theorem monoGe_subseq {a σ} (h₁ : monoGe a) (h₂ : Subseq σ) : monoGe (a # σ ·) := by
  intro i j h; apply h₁; exact subseq_le_of_le h₂ h

theorem monoLt_subseq {a σ} (h₁ : monoLt a) (h₂ : Subseq σ) : monoLt (a # σ ·) := by
  intro i j h; apply h₁; apply h₂; exact h

theorem monoGt_subseq {a σ} (h₁ : monoGt a) (h₂ : Subseq σ) : monoGt (a # σ ·) := by
  intro i j h; apply h₁; apply h₂; exact h

theorem limit_eq_of_sub_tendsTo_zero {a b L M} (h₁ : tendsTo a L) (h₂ : tendsTo b M)
(h₃ : tendsTo (a - b) 0) : L = M := by
  linarith [tendsTo_unique h₃ # tendsTo_sub h₁ h₂]

theorem converges_series_alternating_of_monoGe.aux₁ {a n} (h₁ : monoGe a) (h₂ : tendsTo a 0) :
0 ≤ a n := limit_le_of_monoGe' h₁ h₂

theorem converges_series_alternating_of_monoGe.aux₂ {a n} {f : ℕ → ℕ} (h₁ : monoGe a) :
0 ≤ ∑ k ∈ Finset.range n, (a (f k) - a (f k + 1)) := by
  apply Finset.sum_nonneg
  intro n hn
  simp
  apply h₁
  simp

theorem converges_series_alternating_of_monoGe.aux₃ {a n} (h₁ : monoGe a) (h₂ : tendsTo a 0) :
0 ≤ ∑ k ∈ Finset.range n, (-1) ^ k * a k := by
  induction n using Nat.mod_2_ind <;> nm m
  · rw [sum_range_mul_two_alternating]; exact aux₂ h₁
  · rw [Finset.sum_range_succ, sum_range_mul_two_alternating]
    apply le_add_of_le_of_nonneg
    · exact aux₂ h₁
    · simp; apply aux₁ h₁ h₂

theorem converges_series_alternating_of_monoGe.aux₄ {a n} (h₁ : monoGe a) (h₂ : tendsTo a 0) :
∑ k ∈ Finset.range n, (-1) ^ k * a k ≤ a 0 := by
  cases n
  · simp; exact aux₁ h₁ h₂
  nm n
  induction n using Nat.mod_2_ind <;> nm m
  · rw [Finset.sum_range_succ']
    simp [pow_succ]
    rw [sum_range_mul_two_alternating]
    exact aux₂ h₁
  · rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp
    trans 0
    rotate_left; exact aux₁ h₁ h₂
    simp [pow_succ]
    rw [sum_range_mul_two_alternating]
    exact aux₂ h₁

theorem converges_series_alternating_of_monoGe {a} (h₁ : monoGe a) (h₂ : tendsTo a 0) :
converges # series # λ n => (-1) ^ n * a n := by
  have h₃ := @converges_series_alternating_of_monoGe.aux₁ (h₁ := h₁) (h₂ := h₂)
  have h₄ : ∀ (ε : ℝ), 0 < ε → ∃ N, ∀ n, N ≤ n → a n < ε
  · intro e he
    specialize h₂ e he
    choose N h₂ using h₂
    use N
    intro n hn
    specialize h₂ n hn
    simp at h₂
    rw [abs_of_nonneg # h₃ n] at h₂
    exact h₂
  have h₅ := @converges_series_alternating_of_monoGe.aux₂ (h₁ := h₁)
  have h₆ := @converges_series_alternating_of_monoGe.aux₃ (h₁ := h₁) (h₂ := h₂)
  have h₇ := @converges_series_alternating_of_monoGe.aux₄ (h₁ := h₁) (h₂ := h₂)
  have h₈ : ∀ (m n : ℕ), m * 2 ≤ n →
    |∑ k ∈ Finset.range (m * 2), (-1) ^ k * a k -
    ∑ k ∈ Finset.range n, (-1) ^ k * a k| ≤ a (m * 2)
  · intro m n hn
    generalize hx : ∑ k ∈ Finset.range (m * 2), (-1) ^ k * a k = x
    generalize hb : (a # m * 2 + ·) = b
    obtain ⟨σ, H₁, H₂⟩ : ∃ σ, Subseq σ ∧ b = (a # σ ·)
    · use (m * 2 + ·); simp [hb]
    have H₃ : monoGe b
    · rw [H₂]; exact monoGe_subseq h₁ H₁
    have H₄ : tendsTo b 0
    · rw [H₂]; exact tendsTo_subseq h₂ H₁
    have H₅ : ∀ n, ∑ k ∈ Finset.range (m * 2 + n), (-1) ^ k * a k =
      x + ∑ k ∈ Finset.range n, (-1) ^ k * b k
    · clear! n
      intro n
      rw [←hb]
      cases n
      · simpa
      nm n
      simp
      rw [Finset.sum_range_add, hx]
      simp [pow_add]
    have H₆ : b 0 = a (m * 2)
    · simp [←hb]
    have H₇ := @converges_series_alternating_of_monoGe.aux₂ (h₁ := H₃)
    have H₈ := @converges_series_alternating_of_monoGe.aux₃ (h₁ := H₃) (h₂ := H₄)
    have H₉ := @converges_series_alternating_of_monoGe.aux₄ (h₁ := H₃) (h₂ := H₄)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn; clear hn
    rw [H₅]
    simp
    rw [abs_of_nonneg # H₈ _, ←H₆]
    apply H₉
  rw [converges_iff_isCauchy, isCauchy_iff_alt₁]
  intro e he
  specialize h₄ e he
  choose N h₄ using h₄
  use N * 2
  intro n hn
  have h₉ := h₄ n (by linarith)
  simp only [series]
  apply lt_of_le_of_lt (b := a (N * 2))
  rotate_left
  · apply h₄; simp
  specialize h₈ N n (by linarith)
  rwa [abs_sub_comm]

@[simp]
theorem neg_series' {a} : -series a = series (-a) := by
  ext n; simp [series]

@[simp]
theorem neg_series {a n} : -series a n = series (-a) n := by
  simp [series]

theorem converges_series_alternating_of_monoLe {a} (h₁ : monoLe a) (h₂ : tendsTo a 0) :
converges # series # λ n => (-1) ^ n * a n := by
  replace h₁ := monoGe_neg.mpr h₁
  replace h₂ := tendsTo_neg h₂
  simp at h₂
  have h₃ := converges_series_alternating_of_monoGe h₁ h₂
  simp at h₃
  rw [←converges_neg]
  simpa

theorem converges_series_alternating_of_monoGt {a} (h₁ : monoGt a) (h₂ : tendsTo a 0) :
converges # series # λ n => (-1) ^ n * a n :=
  converges_series_alternating_of_monoGe (monoGe_of_monoGt h₁) h₂

theorem converges_series_alternating_of_monoLt {a} (h₁ : monoLt a) (h₂ : tendsTo a 0) :
converges # series # λ n => (-1) ^ n * a n :=
  converges_series_alternating_of_monoLe (monoLe_of_monoLt h₁) h₂

theorem series_drop_eq {a N} :
series (a # N + ·) = λ n => series a (N + n) - series a N := by
  ext n
  simp_rw [series]
  trans ∑ k ∈ Finset.Ico N (N + n), a k
  · simp [Finset.sum_Ico_eq_sum_range]
  · simp [Finset.sum_Ico_eq_sub]

theorem series_drop_tendsTo_of {a L N} (h : tendsTo (series a) L) :
tendsTo (series (a # N + ·)) (L - series a N) := by
  rw [series_drop_eq]; apply tendsTo_sub # tendsTo_drop_of h; simp

theorem series_drop_tendsTo_iff {a L N} :
tendsTo (series (a # N + ·)) L ↔ tendsTo (series a) (L + series a N) := by
  rw [series_drop_eq]
  constructor <;> intro h
  · nth_rw 1 [show series a = (λ n => series a n - series a N + series a N) by simp]
    apply tendsTo_add _ # by simp
    rwa [←tendsTo_drop_iff (a := λ n => series a n - series a N) (k := N)]
  · rw [show L = L + series a N - series a N by simp]
    apply tendsTo_add _ # by simp
    exact tendsTo_drop_of h

theorem converges_series_drop_iff {a N} :
converges (series (a # N + ·)) ↔ converges (series a) := by
  constructor <;> rintro ⟨L, h⟩
  · rw [series_drop_tendsTo_iff] at h; exact ⟨_, h⟩
  · use L - series a N; simpa [series_drop_tendsTo_iff]

theorem converges_series_alternating_of_monoLe_drop {a N}
(h₁ : monoLe (a # N + ·)) (h₂ : tendsTo a 0) : converges # series # λ n => (-1) ^ n * a n := by
  replace h₂ := tendsTo_drop_of h₂ (k := N)
  rw [←converges_series_drop_iff (N := N)]
  have h₃ := converges_series_alternating_of_monoLe h₁ h₂ (a := λ n => a # N + n)
  simp at h₃
  induction N using Nat.mod_2_ind <;> nm N <;> simp [pow_add]; exact h₃
  replace h₃ := converges_neg.mpr h₃; simp at h₃; exact h₃

theorem converges_series_alternating_of_monoGe_drop {a N}
(h₁ : monoGe (a # N + ·)) (h₂ : tendsTo a 0) : converges # series # λ n => (-1) ^ n * a n := by
  replace h₁ := monoLe_neg.mpr h₁
  replace h₂ := tendsTo_neg h₂
  simp at h₂
  have h₃ := converges_series_alternating_of_monoLe_drop h₁ h₂
  simp at h₃ ⊢; apply converges_neg.mp; simpa

theorem converges_series_alternating_of_monoLt_drop {a N}
(h₁ : monoLt (a # N + ·)) (h₂ : tendsTo a 0) : converges # series # λ n => (-1) ^ n * a n :=
  converges_series_alternating_of_monoLe_drop (monoLe_of_monoLt h₁) h₂

theorem converges_series_alternating_of_monoGt_drop {a N}
(h₁ : monoGt (a # N + ·)) (h₂ : tendsTo a 0) : converges # series # λ n => (-1) ^ n * a n :=
  converges_series_alternating_of_monoGe_drop (monoGe_of_monoGt h₁) h₂

theorem tendsTo_even_of {a L} (h : tendsTo a L) : tendsTo (a # · * 2) L := by
  apply tendsTo_subseq h; simp

theorem tendsTo_odd_of {a L} (h : tendsTo a L) : tendsTo (a # · * 2 + 1) L := by
  apply tendsTo_subseq h; intro; simp