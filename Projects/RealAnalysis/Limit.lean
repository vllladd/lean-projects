import Projects.Util

namespace RealAnalysis

def tendsTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε, 0 < ε → eventually (|a · - L| < ε)

def converges (a : ℕ → ℝ) : Prop :=
  ∃ L, tendsTo a L

noncomputable
def limit (a : ℕ → ℝ) : ℝ :=
  τ L, tendsTo a L

noncomputable def someLt (x : ℝ) : ℝ :=
  τ y, y < x

noncomputable def someGt (x : ℝ) : ℝ :=
  τ y, x < y

noncomputable def glb (a : ℕ → ℝ) : ℝ :=
  ⨅ i, a i

noncomputable def lub (a : ℕ → ℝ) : ℝ :=
  ⨆ i, a i

noncomputable def lb (a : ℕ → ℝ) : ℝ :=
  someLt # glb a

noncomputable def ub (a : ℕ → ℝ) : ℝ :=
  someGt # lub a

-----

theorem tendsTo_unique {a L₁ L₂}
(h₁ : tendsTo a L₁) (h₂ : tendsTo a L₂) : L₁ = L₂ := by
  by_contra! h₃
  wlog h₄ : L₁ < L₂ with ih
  · push Not at h₄; apply ne_symm' at h₃
    apply ih h₂ h₁ h₃; exact lt_of_le_of_ne h₄ h₃
  clear h₃
  generalize he : (L₂ - L₁) / 2 = e
  have h₅ : 0 < e; linarith
  specialize h₁ e (by linarith)
  specialize h₂ e (by linarith)
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  specialize h₁ (max N₁ N₂) (by simp)
  specialize h₂ (max N₁ N₂) (by simp)
  generalize a (max N₁ N₂) = x at h₁ h₂
  replace h₁ := abs_lt.mp h₁ |>.2
  replace h₂ := abs_lt.mp h₂ |>.1
  simp at h₂
  linarith

theorem tendsTo_const {L} : tendsTo (λ _ => L) L := by
  intro e he; use 0; simpa

@[simp]
theorem tendsTo_const_iff {L M} : tendsTo (λ _ => L) M ↔ L = M := by
  have h₁ := @tendsTo_const L
  symm; constructor; rintro rfl; exact h₁
  intro h₂; exact tendsTo_unique h₁ h₂

@[simp]
theorem tendsTo_const_nat_iff {n : ℕ} {L} : tendsTo ofNat(n) L ↔ ofNat(n) = L :=
  tendsTo_const_iff

theorem tendsTo_drop_iff' {a L k} : tendsTo (a # · + k) L ↔ tendsTo a L := by
  constructor
  · intro h e he
    specialize h e he
    obtain ⟨N, h⟩ := h
    dsimp at h
    use N + k
    intro n hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
    clear hn
    specialize h (n + N) (by linarith)
    ring_nf at h ⊢
    exact h
  · intro h e he
    specialize h e he
    obtain ⟨N, h⟩ := h
    dsimp
    use N
    intro n hn
    specialize h (n + k) (by linarith)
    exact h

theorem converges_drop_iff {a k} : converges (a # · + k) ↔ converges a :=
  exists_congr # λ _ => tendsTo_drop_iff'

theorem tendsTo_one_div : tendsTo (1 / ·) 0 := by
  intro e he
  obtain ⟨N, hN⟩ := exists_nat_gt # 1 / e
  use N
  intro n hn
  simp
  have h₁ : 0 < (n : ℝ)
  · cases n
    · simp at hn; simp [hn] at hN; linarith
    · simp; linarith
  replace hn : (N : ℝ) ≤ n; exact_mod_cast hn
  rw [inv_lt_iff_one_lt_mul₀ h₁]
  replace hN : 1 < N * e
  · rwa [←mul_inv_lt_iff₀ he]
  nlinarith

theorem tendsTo_one_div_succ : tendsTo (λ n => 1 / (n + 1)) 0 := by
  have h := tendsTo_drop_iff' (a := (1 / ·)) (k := 1) (L := 0)
  push_cast at h; rw [h]; exact tendsTo_one_div

theorem not_converges_alternating {x y : ℝ} (h : x ≠ y) :
¬converges (if Even · then x else y) := by
  simp only [eventually, converges, tendsTo, not_exists, not_forall, not_lt]
  intro L
  wlog h₁ : L ≠ x with ih
  · apply ne_symm' at h
    specialize ih h L _
    · simp at h₁
      subst h₁
      exact ne_symm' h
    obtain ⟨e, he, ih⟩ := ih
    use e, he
    intro N
    specialize ih N
    obtain ⟨n, hn, ih⟩ := ih
    use n + 1, by linarith
    simp_rw [Nat.even_succ_iff, ←Nat.not_even_iff_odd, ite_not]
    exact ih
  use |L - x|, by simp [sub_ne_zero_of_ne h₁]
  intro N
  use N * 2, by simp
  simp
  rw [abs_sub_comm]

theorem not_converges_minus_one_pow : ¬converges ((-1 : ℝ) ^ ·) := by
  convert not_converges_alternating (x := 1) (y := -1) (by norm_num)
  nm n; induction n using Nat.mod_2_ind <;> simp

theorem ofNat_seq_eq {n : ℕ} : (OfNat.ofNat n : ℕ → ℝ) = λ _ => ↑n := by
  ext i; iterate 2 cases n; simp; nm n
  change ((n + 2 : ℕ) : ℝ) = _; ring_nf

theorem cast_seq_eq {n : ℕ} : (n : ℕ → ℝ) = λ _ => ↑n := by
  ext i; iterate 2 cases n; simp; nm n
  change ((n + 2 : ℕ) : ℝ) = _; ring_nf

theorem tendsTo_neg {a L} (h : tendsTo a L) : tendsTo (-a) (-L) := by
  intro e he; specialize h e he; obtain ⟨N, h⟩ := h
  use N; intro n hn; specialize h n hn; simp
  convert h using 1; rw [←abs_neg, add_comm]; simp; rfl

theorem tendsTo_add {a₁ a₂ L₁ L₂} (h₁ : tendsTo a₁ L₁)
(h₂ : tendsTo a₂ L₂) : tendsTo (a₁ + a₂) (L₁ + L₂) := by
  intro e he
  dsimp
  specialize h₁ (e / 2) (by simpa)
  specialize h₂ (e / 2) (by simpa)
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  use max N₁ N₂
  intro n hn
  specialize h₁ n # le_of_max_le_left hn
  specialize h₂ n # le_of_max_le_right hn
  calc
    _ = |(a₁ n - L₁) + (a₂ n - L₂)| := by ring_nf
    _ ≤ |a₁ n - L₁| + |a₂ n - L₂| := by apply abs_add_le
  linarith

theorem tendsTo_sub {a₁ a₂ L₁ L₂} (h₁ : tendsTo a₁ L₁)
(h₂ : tendsTo a₂ L₂) : tendsTo (a₁ - a₂) (L₁ - L₂) :=
  tendsTo_add h₁ # tendsTo_neg h₂

theorem tendsTo_iff_eps_lt_one {a L} :
tendsTo a L ↔ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (N : ℕ),
∀ (n : ℕ), N ≤ n → |a n - L| < ε := by
  use λ h e h₁ _ => h e h₁
  intro h e he
  specialize h (min e # 1 / 2) (by simpa) (by norm_num)
  obtain ⟨N, h⟩ := h
  use N
  intro n hn
  specialize h n hn
  simp at h
  exact h.1

theorem eventually_ne_of_ne_limit {a L M} (h₁ : tendsTo a L)
(h₂ : M ≠ L) : eventually (a · ≠ M) := by
  specialize h₁ (|M - L| / 2) _
  · simp; contrapose! h₂; linarith
  obtain ⟨N, h₁⟩ := h₁
  use N
  intro n hn
  specialize h₁ n hn
  contrapose! h₁
  simp [h₁]

theorem drop_ne_of_ne_limit {a L M} (h₁ : tendsTo a L) (h₂ : M ≠ L) :
∃ k, tendsTo (a # · + k) L ∧ ∀ n, a (n + k) ≠ M := by
  obtain ⟨k, h₃⟩ := eventually_ne_of_ne_limit h₁ h₂
  use k
  rw [tendsTo_drop_iff']; use h₁
  intro n
  specialize h₃ (n + k) (by linarith)
  exact h₃

theorem tendsTo_inv_aux₁ {x y : ℝ} (h : |x - y| < |y| / 2) : |y| / 2 < |x| := by
  suffices h₆ : 2 * |y| < 3 / 2 * |y| + |x|; linarith; calc
  _ = |x - y - x - y| := by
    simp; ring_nf; simp [abs_neg, abs_mul]
  _ = |(x - y) - (x + y)| := by ring_nf
  _ ≤ |x - y| + |x + y| := by apply abs_sub
  _ < |y| / 2 + |x + y| := by simpa
  _ ≤ |y| / 2 + |x| + |y| := by
    simp only [add_assoc, add_le_add_iff_left]
    apply abs_add_le
  _ = _ := by ring_nf

theorem tendsTo_inv_aux₂ {a L} (h₁ : ∀ n, a n ≠ 0) (h₂ : L ≠ 0)
(h₃ : tendsTo a L) : ∃ (x : ℝ), 0 < x ∧ ∀ n, x ≤ |a n| := by
  specialize h₃ (|L| / 2) (by positivity)
  obtain ⟨N, h⟩ := h₃
  generalize hx : (List.range N |>.map (|a ·|)
    |>.cons (|L| / 2) |>.min?) = x
  cases x; simp at hx
  nm x
  use x
  rw [List.min?_eq_some_iff₁] at hx
  simp at hx
  rcases hx with ⟨rfl | ⟨k, hk, rfl⟩, h₃, h₄⟩
  · clear h₃
    simp [h₂]
    intro n
    by_cases h₅ : n < N
    · exact h₄ _ h₅
    · push Not at h₅
      exact le_of_lt # tendsTo_inv_aux₁ # h _ h₅
  use by simp [h₁]
  intro n
  by_cases h₅ : n < N
  · exact h₄ _ h₅
  push Not at h₅
  specialize h _ h₅
  by_contra! h₆
  have h₇ : |a n| < |L| / 2; linarith
  contrapose! h₇; exact le_of_lt # tendsTo_inv_aux₁ h

theorem tendsTo_inv_aux₃ {a L} (h₁ : ∀ n, a n ≠ 0) (h₂ : L ≠ 0)
(h₃ : tendsTo a L) : tendsTo a⁻¹ L⁻¹ := by
  intro e he
  obtain ⟨x, hx, h₄⟩ := tendsTo_inv_aux₂ h₁ h₂ h₃
  specialize h₃ (x * e * |L|) (by positivity)
  obtain ⟨N, h₃⟩ := h₃
  use N
  intro n hn
  specialize h₃ n hn
  have H : 0 < |a n * L|
  · simp [h₁, h₂]
  apply lt_of_lt_of_le (b := x * e * |L| / |a n * L|)
  · calc
    _ = |1 / a n - 1 / L| := by simp
    _ = |(L - a n) / (a n * L)| := by
      rw [div_sub_div _ _ (h₁ _) h₂]; simp
    _ = |L - a n| / |a n * L| := by apply abs_div
    _ = |a n - L| / |a n * L| := by rw [abs_sub_comm]
    _ < x * e * |L| / |a n * L| := by
      rwa [div_lt_div_iff_of_pos_right H]
  calc
  _ = x * e * |L| / (|a n| * |L|) := by rw [abs_mul]
  _ = x * e / |a n| := mul_div_mul_right _ _ # by positivity
  _ ≤ |a n| * e / |a n| := by
    rw [div_le_div_iff_of_pos_right # by simp [h₁]]
    rw [mul_le_mul_iff_of_pos_right he]; apply h₄
  _ = e := by rw [mul_div_cancel_left₀ _ # by simp [h₁]]

theorem tendsTo_inv {a L} (h₁ : L ≠ 0) (h₂ : tendsTo a L) : tendsTo a⁻¹ L⁻¹ := by
  obtain ⟨k, h₃, h₄⟩ := drop_ne_of_ne_limit h₂ h₁.symm
  rw [←tendsTo_drop_iff' (k := k)]
  exact tendsTo_inv_aux₃ h₄ h₁ h₃

@[simp]
theorem someLt_lt {x} : someLt x < x :=
  τ_spec (p := (· < x)) # exists_lt _

@[simp]
theorem lt_someGt {x} : x < someGt x :=
  τ_spec (p := (x < ·)) # exists_gt _

theorem converges_of_tendsTo {a L} (h : tendsTo a L) : converges a := ⟨_, h⟩

theorem bddBelow_of_converges {a} (h : converges a) : BddBelow (Set.range a) := by
  obtain ⟨L, h⟩ := h
  specialize h 1 (by norm_num)
  simp [bddBelow_range]
  obtain ⟨N, h⟩ := h
  generalize hm : (List.range N |>.map a |>.cons (L - 1) |>.min?.get!) = m
  simp at hm
  use m
  intro i
  cases h₁ : List.map a (List.range N) |>.min? <;> simp [h₁] at hm
  · simp at h₁
    subst h₁ hm
    specialize h i (by simp)
    rw [abs_lt] at h
    linarith
  nm m; subst hm
  simp [List.min?_eq_some_iff₁] at h₁
  rcases h₁ with ⟨⟨j, h₁, rfl⟩, h₂⟩
  by_cases h₃ : i < N
  · exact inf_le_of_right_le # h₂ i h₃
  push Not at h₃
  specialize h i h₃
  apply inf_le_of_left_le
  rw [abs_lt] at h
  linarith

@[simp]
theorem converges_neg {a} : converges (-a) ↔ converges a := by
  constructor <;> rintro ⟨L, h⟩ <;> use -L <;> convert tendsTo_neg h; simp

theorem bddAbove_of_converges {a} (h : converges a) : BddAbove (Set.range a) := by
  replace h : converges (-a); simpa
  replace h := bddBelow_of_converges h
  rwa [←bddBelow_range_neg]

theorem glb_le_of_tendsTo {a L} (h : tendsTo a L) :
(∀ i, glb a ≤ a i) ∧ glb a ≤ L := by
  apply and_of
  · intro i; unfold glb
    apply ciInf_le_of_le _ i (by rfl)
    apply bddBelow_of_converges # converges_of_tendsTo h
  intro h₁
  by_contra! h₂
  generalize glb a = m at h₁ h₂
  specialize h (m - L) (by linarith)
  obtain ⟨N, h⟩ := h
  specialize h N (by rfl)
  specialize h₁ N
  rw [abs_lt] at h
  linarith

theorem le_lub_of_tendsTo {a L} (h : tendsTo a L) :
(∀ i, a i ≤ lub a) ∧ L ≤ lub a := by
  apply and_of
  · intro i; unfold lub
    apply le_ciSup_of_le _ i (by rfl)
    apply bddAbove_of_converges # converges_of_tendsTo h
  intro h₁
  by_contra! h₂
  generalize lub a = m at h₁ h₂
  specialize h (L - m) (by linarith)
  obtain ⟨N, h⟩ := h
  specialize h N (by rfl)
  specialize h₁ N
  rw [abs_lt] at h
  linarith

theorem le_glb_of_le {a m} (h : ∀ i, m ≤ a i) : m ≤ glb a := le_ciInf h
theorem lub_le_of_le {a m} (h : ∀ i, a i ≤ m) : lub a ≤ m := ciSup_le h

theorem glb_neg {a : ℕ → ℝ} (h : converges a) :
glb (-a) = -lub a := by
  obtain ⟨L, h₁⟩ := h
  have h₂ := tendsTo_neg h₁
  obtain ⟨h₃, h₄⟩ := le_lub_of_tendsTo h₁
  obtain ⟨h₅, h₆⟩ := glb_le_of_tendsTo h₂
  simp at h₅
  apply le_antisymm
  · rw [←neg_le_neg_iff]; simp; apply lub_le_of_le; intro i; specialize h₅ i; linarith
  · apply le_glb_of_le; intro i; specialize h₃ i; simp; linarith

theorem lub_neg {a : ℕ → ℝ} (h : converges a) : lub (-a) = -glb a := by
  nth_rw 2 [←neg_neg a]; rw [glb_neg] <;> simp [h]

@[simp] theorem lb_lt_glb {a} : lb a < glb a := by simp [lb]
@[simp] theorem lub_lt_ub {a} : lub a < ub a := by simp [ub]

theorem lb_lt_of_tendsTo {a L} (h : tendsTo a L) :
(∀ i, lb a < a i) ∧ lb a < L := by
  obtain ⟨h₁, h₂⟩ := glb_le_of_tendsTo h; constructor
  · intro i; apply lt_of_lt_of_le lb_lt_glb # h₁ i
  · apply lt_of_lt_of_le lb_lt_glb h₂

theorem lt_ub_of_tendsTo {a L} (h : tendsTo a L) :
(∀ i, a i < ub a) ∧ L < ub a := by
  obtain ⟨h₁, h₂⟩ := le_lub_of_tendsTo h; constructor
  · intro i; apply lt_of_le_of_lt (h₁ i) lub_lt_ub
  · apply lt_of_le_of_lt h₂ lub_lt_ub

theorem tendsTo_mul_aux₁ {a₁ a₂ L₁ L₂} (h₁ : tendsTo a₁ L₁)
(h₂ : tendsTo a₂ L₂) (h₄' : ∀ i, 1 < a₂ i)
(h₅' : 1 < L₁) (h₆' : 1 < L₂) : tendsTo (a₁ * a₂) (L₁ * L₂) := by
  have h₁' := h₁
  have h₂' := h₂
  have h₄ : ∀ i, 0 < a₂ i; intro i; specialize h₄' i; linarith
  have h₅ : 0 < L₁; linarith
  have h₆ : 0 < L₂; linarith
  intro e he
  generalize hx : e / 2 / ub a₂ = x
  generalize hy : e / 2 / L₁ = y
  have hxp : 0 < x
  · subst hx
    apply div_pos; positivity
    apply h₆.trans
    exact lt_ub_of_tendsTo h₂ |>.2
  have hyp : 0 < y
  · subst hy; positivity
  specialize h₁ x hxp
  specialize h₂ y hyp
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  dsimp
  use max N₁ N₂
  intro n hn
  simp at hn
  rcases hn with ⟨hn₁, hn₂⟩
  specialize h₁ n (by linarith)
  specialize h₂ n (by linarith)
  specialize h₄ n; specialize h₄' n
  have h₇ : |a₁ n * a₂ n - L₁ * L₂| < a₂ n * x + L₁ * y
  · calc
    _ = |a₂ n * (a₁ n - L₁) + L₁ * (a₂ n - L₂)| := by ring_nf
    _ ≤ |a₂ n * (a₁ n - L₁)| + |L₁ * (a₂ n - L₂)| := by apply abs_add_le
    _ = |a₂ n| * |a₁ n - L₁| + |L₁| * |a₂ n - L₂| := by simp [abs_mul]
    _ = a₂ n * |a₁ n - L₁| + L₁ * |a₂ n - L₂| := by
      congr; exact abs_of_pos h₄; exact abs_of_pos h₅
    _ < a₂ n * x + L₁ * |a₂ n - L₂| := by simpa [mul_lt_mul_iff_right₀ h₄]
    _ < a₂ n * x + L₁ * y := by simpa [mul_lt_mul_iff_right₀ h₅]
  apply h₇.trans; clear h₇
  subst hx hy
  calc
  _ < e / 2 + L₁ * (e / 2 / L₁) := by
    simp
    rw [←mul_comm_div]
    apply mul_lt_of_lt_one_left; positivity
    rw [div_lt_one_iff]
    left
    use h₆.trans # lt_ub_of_tendsTo h₂' |>.2
    exact lt_ub_of_tendsTo h₂' |>.1 n
  _ = e / 2 + e / 2 := by
    simp
    rw [←mul_comm_div]
    rw [div_self # by linarith]
    simp
  _ = e := by simp

theorem tendsTo_mul {a₁ a₂ L₁ L₂} (h₁ : tendsTo a₁ L₁)
(h₂ : tendsTo a₂ L₂) : tendsTo (a₁ * a₂) (L₁ * L₂) := by
  generalize hm : 3 + max |lb a₁| |lb a₂| = m
  generalize hb₁ : a₁ + (λ _ => m) = b₁
  generalize hb₂ : a₂ + (λ _ => m) = b₂
  have H₁ : ∀ i, 2 < b₁ i
  · intro i; simp [←hb₁, ←hm]
    have H := lb_lt_of_tendsTo h₁ |>.1 i
    simp [max_eq_ite]; split_ifs with h₃
    · rw [abs_eq_ite]; split_ifs <;> linarith
    · push Not at h₃
      have H₃ := abs_nonneg # lb a₂
      suffices H₁ : 0 < a₁ i + |lb a₁| + 1; linarith
      rw [abs_eq_ite]; split_ifs <;> linarith
  have H₂ : ∀ i, 2 < b₂ i
  · intro i; simp [←hb₂, ←hm]
    have H := lb_lt_of_tendsTo h₂ |>.1 i
    simp [max_eq_ite]; split_ifs with h₃
    · have H₃ := abs_nonneg # lb a₁
      suffices H₁ : 0 < a₂ i + |lb a₂| + 1; linarith
      rw [abs_eq_ite]; split_ifs <;> linarith
    · rw [abs_eq_ite]; split_ifs <;> linarith
  have H₃ : 2 < m
  · rw [←hm]
    suffices : 0 < 1 + max |lb a₁| |lb a₂|; linarith
    suffices : 0 ≤ max |lb a₁| |lb a₂|; linarith
    simp
  have h₃ := @tendsTo_add a₁ (λ _ => m) L₁ m h₁ # by simp
  have h₄ := @tendsTo_add a₂ (λ _ => m) L₂ m h₂ # by simp
  rw [hb₁] at h₃
  rw [hb₂] at h₄
  have H₄ : 1 < L₁ + m
  · by_contra! h₅
    specialize h₃ (1 / 2) (by positivity)
    obtain ⟨N, h₃⟩ := h₃
    specialize h₃ N (by rfl)
    specialize H₁ N
    rw [abs_lt] at h₃
    rcases h₃ with ⟨h₃, h₆⟩
    linarith
  have H₅ : 1 < L₂ + m
  · by_contra! h₅
    specialize h₄ (1 / 2) (by positivity)
    obtain ⟨N, h₄⟩ := h₄
    specialize h₄ N (by rfl)
    specialize H₂ N
    rw [abs_lt] at h₄
    rcases h₄ with ⟨h₄, h₆⟩
    linarith
  replace H₁ : ∀ i, 1 < b₁ i; intro i; specialize H₁ i; linarith
  replace H₂ : ∀ i, 1 < b₂ i; intro i; specialize H₂ i; linarith
  replace H₃ : 1 < m; linarith
  have h₅ : a₁ * a₂ = b₁ * b₂ - (λ _ => m) * (b₁ + b₂) + (λ _ => m ^ 2)
  · calc
    _ = (b₁ - (λ _ => m)) * (b₂ - (λ _ => m)) := by subst hb₁ hb₂; ring_nf
    _ = b₁ * b₂ - (λ _ => m) * (b₁ + b₂) + (λ _ => m) ^ 2 := by ring_nf
    _ = _ := by ext x; simp
  rw [h₅]; clear h₅
  have h₅ : L₁ * L₂ = (L₁ + m) * (L₂ + m) -
    m * ((L₁ + m) + (L₂ + m)) + m ^ 2; ring_nf
  rw [h₅]; clear h₅
  have h₅ : tendsTo b₁ (L₁ + m); subst hb₁; exact tendsTo_add h₁ # by simp
  have h₆ : tendsTo b₂ (L₂ + m); subst hb₂; exact tendsTo_add h₂ # by simp
  apply tendsTo_add _ # by simp
  apply tendsTo_sub
  rotate_left
  · apply tendsTo_mul_aux₁ (by simp) (tendsTo_add h₅ h₆) _ H₃
    · linarith
    · intro i
      specialize H₁ i
      specialize H₂ i
      simp [←hb₁, ←hb₂] at H₁ H₂ ⊢
      linarith
  apply tendsTo_mul_aux₁ h₅ h₆ H₂ H₄ H₅

theorem tendsTo_div {a₁ a₂ L₁ L₂} (h₁ : L₂ ≠ 0) (h₂ : tendsTo a₁ L₁)
(h₃ : tendsTo a₂ L₂) : tendsTo (a₁ / a₂) (L₁ / L₂) :=
  tendsTo_mul h₂ # tendsTo_inv h₁ h₃

theorem squeeze {a b c : ℕ → ℝ} {L} (h₁ : ∀ n, a n ≤ b n) (h₂ : ∀ n, b n ≤ c n)
(h₃ : tendsTo a L) (h₄ : tendsTo c L) : tendsTo b L := by
  intro e he; specialize h₃ e he; specialize h₄ e he
  obtain ⟨N₁, h₃⟩ := h₃; obtain ⟨N₂, h₄⟩ := h₄
  use N₁ + N₂; intro n hn; specialize h₁ n; specialize h₂ n
  specialize h₃ n (by linarith); specialize h₄ n (by linarith)
  rw [abs_lt] at h₃ h₄ ⊢; constructor <;> linarith

theorem eventually_pos_of_limit_pos {a L} (h₁ : 0 < L) (h₂ : tendsTo a L) :
eventually (0 < a ·) := by
  specialize h₂ (L / 2) # by linarith
  obtain ⟨N, h₂⟩ := h₂; use N; intro n hn
  specialize h₂ n hn; replace h₂ := abs_lt.mp h₂; linarith

theorem eventually_neg_of_limit_neg {a L} (h₁ : L < 0) (h₂ : tendsTo a L) :
eventually (a · < 0) := by
  specialize h₂ (-L / 2) # by linarith
  obtain ⟨N, h₂⟩ := h₂; use N; intro n hn
  specialize h₂ n hn; replace h₂ := abs_lt.mp h₂; linarith

theorem eventually_abs_limit_div_two_lt_aux₁ {a L} (h₁ : 0 < L) (h₂ : ∀ n, 0 < a n)
(h₃ : tendsTo a L) : eventually (|L| / 2 < |a ·|) := by
  specialize h₃ (L / 2) # by positivity
  obtain ⟨N, h₃⟩ := h₃; use N; intro n hn
  specialize h₂ n; specialize h₃ n hn
  rw [abs_of_pos h₁, abs_of_pos h₂]; rw [abs_lt] at h₃; linarith

theorem eventually_abs_limit_div_two_lt_aux₂ {a L} (h₁ : 0 < L) (h₂ : tendsTo a L) :
eventually (|L| / 2 < |a ·|) := by
  obtain ⟨N, h₃⟩ := eventually_pos_of_limit_pos h₁ h₂
  rw [←tendsTo_drop_iff' (k := N)] at h₂
  replace h₃ : ∀ n, 0 < a (n + N); aesop
  obtain ⟨N₁, h₄⟩ := eventually_abs_limit_div_two_lt_aux₁ h₁ h₃ h₂
  use N + N₁; intro n hn
  replace h₄ : ∀ n, |L| / 2 < |a # n + N + N₁|
  · intro k; specialize h₄ (k + N₁) # by simp
    ring_nf at h₄ ⊢; exact h₄
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  specialize h₄ n; ring_nf at h₄ ⊢; exact h₄

theorem eventually_abs_limit_div_two_lt {a L} (h₁ : L ≠ 0) (h₂ : tendsTo a L) :
eventually (|L| / 2 < |a ·|) := by
  replace h₁ := lt_or_gt_of_ne # ne_symm' h₁
  rcases h₁ with h₁ | h₁; exact eventually_abs_limit_div_two_lt_aux₂ h₁ h₂
  replace h₁ : 0 < -L; linarith; replace h₂ := tendsTo_neg h₂
  have h₃ := eventually_abs_limit_div_two_lt_aux₂ h₁ h₂; simp at h₃; exact h₃

theorem eventually_abs_limit_div_two_le {a L} (h : tendsTo a L) :
eventually (|L| / 2 ≤ |a ·|) := by
  by_cases h₁ : L = 0; simp [eventually, h₁]
  obtain ⟨N, h₂⟩ := eventually_abs_limit_div_two_lt h₁ h
  use N; dsimp at h₂ ⊢; intro n hn
  specialize h₂ n hn; exact le_of_lt h₂

theorem tendsTo_abs {a L} (h : tendsTo a L) : tendsTo (|a ·|) |L| := by
  intro e he; specialize h e he; obtain ⟨N, h⟩ := h
  use N; intro n hn; specialize h n hn; dsimp
  apply lt_of_le_of_lt _ h; apply abs_abs_sub_abs_le

theorem lt_ub_of_converges {a n} (h : converges a) : a n < ub a := by
  obtain ⟨L, h⟩ := h; exact lt_ub_of_tendsTo h |>.1 _

theorem lb_lt_of_converges {a n} (h : converges a) : lb a < a n := by
  obtain ⟨L, h⟩ := h; exact lb_lt_of_tendsTo h |>.1 _

def boundedBy (a : ℕ → ℝ) (m : ℝ) : Prop :=
  ∀ n, |a n| ≤ m

def bounded (a : ℕ → ℝ) : Prop :=
  ∃ m, boundedBy a m

def bounded' (a : ℕ → ℝ) : Prop :=
  ∃ m, 0 < m ∧ boundedBy a m

theorem bounded'_iff_bounded {a : ℕ → ℝ} : bounded' a ↔ bounded a := by
  constructor
  · rintro ⟨m, hm, h⟩; use m
  · rintro ⟨m, h⟩; use m + 1; constructor
    · suffices : 0 ≤ m; linarith; trans |a 0|; simp; exact h 0
    · intro n; specialize h n; linarith

theorem bounded_of_converges {a} (h : converges a) : bounded a := by
  use max |lb a| |ub a|; intro n; simp; by_cases h₁ : 0 ≤ a n
  · rw [abs_of_nonneg h₁]; right
    trans ub a; rotate_left; apply le_abs_self
    exact le_of_lt # lt_ub_of_converges h
  · push Not at h₁; rw [abs_of_neg h₁]; left
    have h₂ := lb_lt_of_converges h (n := n)
    rw [neg_le, abs_of_neg] <;> linarith

theorem not_converges_of_not_bounded {a} (h : ¬bounded a) : ¬converges a := by
  contrapose! h; exact bounded_of_converges h

theorem not_bounded_id : ¬bounded (·) := by
  simp [bounded, boundedBy]; intro m; use ⌈m⌉₊ + 1; simp; linarith [Nat.le_ceil m]

theorem boundedBy_zero_iff_const_zero {a : ℕ → ℝ} : boundedBy a 0 ↔ a = 0 := by
  simp only [boundedBy, abs_nonpos_iff]; symm
  constructor; rintro rfl; simp; intro h; ext; simp [h]

theorem limit_eq_of_tendsTo {a L} (h : tendsTo a L) : limit a = L :=
  τ_eq_of h # λ _ h₁ => tendsTo_unique h₁ h

theorem tendsTo_limit_of_tendsTo {a L} (h : tendsTo a L) : tendsTo a (limit a) := by
  rwa [limit_eq_of_tendsTo h]

theorem tendsTo_limit_of_converges {a} (h : converges a) : tendsTo a (limit a) := by
  obtain ⟨L, h⟩ := h; exact tendsTo_limit_of_tendsTo h

theorem converges_add {a b} (ha : converges a) (hb : converges b) :
converges (a + b) := by
  obtain ⟨L, ha⟩ := ha; obtain ⟨M, hb⟩ := hb; use L + M; exact tendsTo_add ha hb

theorem converges_sub {a b} (ha : converges a) (hb : converges b) :
converges (a - b) := by
  obtain ⟨L, ha⟩ := ha; obtain ⟨M, hb⟩ := hb; use L - M; exact tendsTo_sub ha hb

theorem converges_mul {a b} (ha : converges a) (hb : converges b) :
converges (a * b) := by
  obtain ⟨L, ha⟩ := ha; obtain ⟨M, hb⟩ := hb; use L * M; exact tendsTo_mul ha hb

theorem converges_div {a b} (ha : converges a) (hb : converges b)
(h : limit b ≠ 0) : converges (a / b) := by
  obtain ⟨L, ha⟩ := ha; obtain ⟨M, hb⟩ := hb; use L / M
  rw [limit_eq_of_tendsTo hb] at h; exact tendsTo_div h ha hb

theorem converges_inv {a} (ha : converges a) (h : limit a ≠ 0) : converges a⁻¹ := by
  obtain ⟨L, ha⟩ := ha; rw [limit_eq_of_tendsTo ha] at h
  use L⁻¹; exact tendsTo_inv h ha

theorem tendsTo_pow {a L} {k : ℕ} (h : tendsTo a L) : tendsTo (a ^ k) (L ^ k) := by
  induction k; simp; nm k hk; simp [pow_add]; exact tendsTo_mul hk h

theorem converges_pow {a} {k : ℕ} (ha : converges a) : converges (a ^ k) := by
  obtain ⟨L, ha⟩ := ha; use L ^ k, tendsTo_pow ha

theorem seq_ofNat_eq {n} : (OfNat.ofNat n : ℕ → ℝ) = n := by
  iterate 2 cases n; simp; nm n;; rfl

theorem limit_le_of_forall_le {a L K} (h₁ : tendsTo a L) (h₂ : ∀ n, a n ≤ K) : L ≤ K := by
  by_contra! h₃; specialize h₁ ((L - K) / 2) # by linarith
  obtain ⟨N, h₁⟩ := h₁; specialize h₁ N # by rfl
  specialize h₂ N; rw [abs_lt] at h₁; linarith

theorem le_limit_of_forall_le {a L K} (h₁ : tendsTo a L) (h₂ : ∀ n, K ≤ a n) : K ≤ L := by
  have h₃ := limit_le_of_forall_le (K := -K) # tendsTo_neg h₁; simp at h₃; exact h₃ h₂

def Subseq (σ : ℕ → ℕ) : Prop :=
  ∀ i j, i < j → σ i < σ j

theorem nat_le_of_forall_lt_apply_succ {σ : ℕ → ℕ} {n}
(h : ∀ n, σ n < σ (n + 1)) : n ≤ σ n := by
  induction n; simp; nm n ih; rw [Nat.succ_le_iff]; exact lt_of_le_of_lt ih # h _

theorem nat_le_of_subseq {σ n} (h : Subseq σ) : n ≤ σ n := by
  apply nat_le_of_forall_lt_apply_succ; intro k; apply h; simp

theorem tendsTo_subseq {a σ L} (h₁ : tendsTo a L)
(h₂ : Subseq σ) : tendsTo (a ∘ σ) L := by
  intro e he; specialize h₁ e he; obtain ⟨N, h₁⟩ := h₁
  use N; intro n hn; apply h₁; clear h₁; clear! e
  rw [←Nat.lt_succ_iff, Nat.succ_eq_add_one] at hn ⊢
  apply lt_of_lt_of_le hn; simp; exact nat_le_of_subseq h₂

theorem exi_subseq_tendsTo_of_neg_one_pow :
∃ σ L, Subseq σ ∧ tendsTo (((-1 : ℝ) ^ ·) ∘ σ) L := by
  use (· * 2), 1, λ i j h => by linarith, by simp

theorem bounded_drop_iff {a k} : bounded (a # · + k) ↔ bounded a := by
  symm; constructor <;> rintro ⟨M, h⟩
  · use M; intro n; apply h
  use M + ∑ i ∈ Finset.range k, |a i|
  intro n
  by_cases hk : k ≤ n
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    clear hk
    specialize h n
    dsimp at h
    rw [add_comm k]
    apply h.trans
    simp
    positivity
  push Not at hk
  specialize h 0
  simp at h
  have hM := nonneg_of_abs_le h
  suffices H : |a n| ≤ ∑ i ∈ Finset.range k, |a i|; linarith
  exact Finset.le_sum_range hk

theorem le_lub_of_bounded_top {a : ℕ → ℝ} {n : ℕ}
(ha : ∃ m, ∀ n, a n ≤ m) : a n ≤ lub a := by
  obtain ⟨m, ha⟩ := ha; apply le_ciSup; use m
  intro x; simp; rintro i rfl; apply ha

theorem glb_le_of_bounded_bottom {a : ℕ → ℝ} {n : ℕ}
(ha : ∃ m, ∀ n, m ≤ a n) : glb a ≤ a n := by
  obtain ⟨m, ha⟩ := ha; apply ciInf_le; use m
  intro x; simp; rintro i rfl; apply ha

theorem exi_lub_sub_lt_of_bounded_top {a : ℕ → ℝ} {ε : ℝ}
(ha : ∃ m, ∀ n, a n ≤ m) (he : 0 < ε) : ∃ n, lub a - a n < ε := by
  replace ha := λ n => le_lub_of_bounded_top (n := n) ha
  by_contra! h₁; replace h₁ : ∀ n, a n ≤ lub a - ε
  intro n; linarith [h₁ n]; linarith [lub_le_of_le h₁]

theorem exi_sub_glb_lt_of_bounded_bottom {a : ℕ → ℝ} {ε : ℝ}
(ha : ∃ m, ∀ n, m ≤ a n) (he : 0 < ε) : ∃ n, a n - glb a < ε := by
  replace ha := λ n => glb_le_of_bounded_bottom (n := n) ha
  by_contra! h₁; replace h₁ : ∀ n, glb a + ε ≤ a n
  intro n; linarith [h₁ n]; linarith [le_glb_of_le h₁]

theorem tendsTo_drop_iff {a L k} : tendsTo (a # k + ·) L ↔ tendsTo a L := by
  simp_rw [add_comm k, tendsTo_drop_iff']

theorem tendsTo_drop_of {a L k} (h : tendsTo a L) : tendsTo (a # k + ·) L :=
  tendsTo_drop_iff.mpr h

@[simp]
theorem tendsTo_limit_iff_converges {a} : tendsTo a (limit a) ↔ converges a := by
  constructor <;> intro h
  · use limit a
  · exact tendsTo_limit_of_converges h

@[simp]
theorem converges_const {x : ℝ} : converges (λ _ => x) :=
  ⟨x, by simp⟩

@[simp]
theorem converges_const_nat {n : ℕ} : converges ofNat(n) :=
  converges_const