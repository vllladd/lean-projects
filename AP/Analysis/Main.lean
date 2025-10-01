import AP.Util

namespace RealAnalysis

def tendsTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |a n - L| < ε

def converges (a : ℕ → ℝ) : Prop :=
  ∃ L, tendsTo a L

noncomputable def someLt (x : ℝ) : ℝ :=
  Classical.epsilon (· < x)

noncomputable def someGt (x : ℝ) : ℝ :=
  Classical.epsilon (x < ·)

noncomputable def glb (a : ℕ → ℝ) : ℝ :=
  ⨅ i, a i

noncomputable def lub (a : ℕ → ℝ) : ℝ :=
  ⨆ i, a i

noncomputable def lb (a : ℕ → ℝ) : ℝ :=
  someLt # glb a

noncomputable def ub (a : ℕ → ℝ) : ℝ :=
  someGt # lub a

-----

theorem tendsTo_const {L} : tendsTo (λ _ => L) L := by
  intro e he; use 0; simpa

theorem tendsTo_unique {a L₁ L₂}
(h₁ : tendsTo a L₁) (h₂ : tendsTo a L₂) : L₁ = L₂ := by
  by_contra! h₃
  wlog h₄ : L₁ < L₂ with ih
  · push_neg at h₄; apply ne_symm' at h₃
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

theorem tendsTo_drop_iff {a L k} : tendsTo (a # · + k) L ↔ tendsTo a L := by
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
  exists_congr # λ _ => tendsTo_drop_iff

theorem tendsTo_one_div : tendsTo (1 / ·) 0 := by
  intro e he
  obtain ⟨N, hN⟩ := exists_nat_gt # 1 / e
  use N
  intro n hn
  simp
  rw [abs_of_nonneg # by simp]
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
  have h := tendsTo_drop_iff (a := (1 / ·)) (k := 1) (L := 0)
  push_cast at h; rw [h]; exact tendsTo_one_div

theorem not_converges_alternating {x y : ℝ} (h : x ≠ y) :
¬converges (if Even · then x else y) := by
  simp only [converges, tendsTo, not_exists, not_forall, not_lt]
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

theorem tendsTo_const_ofNat {n : ℕ} : tendsTo (OfNat.ofNat n) n := by
  simp [ofNat_seq_eq, tendsTo_const]

theorem tendsTo_const_cast {n : ℕ} : tendsTo n n := by
  simp [cast_seq_eq, tendsTo_const]

theorem tendsTo_const_ofNat_iff {n : ℕ} {L : ℝ} :
tendsTo (OfNat.ofNat n) L ↔ L = n := by
  have h := @tendsTo_const_ofNat n
  use λ h₁ => tendsTo_unique h₁ h
  rintro rfl; exact h

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
    _ ≤ |a₁ n - L₁| + |a₂ n - L₂| := by apply abs_add
  linarith

theorem tendsTo_sub {a₁ a₂ L₁ L₂} (h₁ : tendsTo a₁ L₁)
(h₂ : tendsTo a₂ L₂) : tendsTo (a₁ - a₂) (L₁ - L₂) :=
  tendsTo_add h₁ # tendsTo_neg h₂

theorem tendsTo_iff_eps_lt_one {a L} :
tendsTo a L ↔ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (N : ℕ),
∀ (n : ℕ), N ≤ n → |a n - L| < ε := by
  use λ h e h₁ _ => h e h₁
  intro h
  intro e he
  specialize h (min e # 1 / 2) (by simpa) (by norm_num)
  obtain ⟨N, h⟩ := h
  use N
  intro n hn
  specialize h n hn
  simp at h
  exact h.1

theorem tendsTo_inv_aux₁ {x y : ℝ} (h : |x - y| < |y| / 2) : |y| / 2 < |x| := by
  suffices h₆ : 2 * |y| < 3 / 2 * |y| + |x|; linarith; calc
  _ = |x - y - x - y| := by
    simp; ring_nf; simp [abs_neg, abs_mul]
  _ = |(x - y) - (x + y)| := by ring_nf
  _ ≤ |x - y| + |x + y| := by apply abs_sub
  _ < |y| / 2 + |x + y| := by simpa
  _ ≤ |y| / 2 + |x| + |y| := by
    simp only [add_assoc, add_le_add_iff_left]
    apply abs_add
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
  rw [List.min?_eq_some_iff_1] at hx
  simp at hx
  rcases hx with ⟨rfl | ⟨k, hk, rfl⟩, h₃, h₄⟩
  · clear h₃
    simp [h₂]
    intro n
    by_cases h₅ : n < N
    · exact h₄ _ h₅
    · push_neg at h₅
      exact le_of_lt # tendsTo_inv_aux₁ # h _ h₅
  use by simp [h₁]
  intro n
  by_cases h₅ : n < N
  · exact h₄ _ h₅
  push_neg at h₅
  specialize h _ h₅
  by_contra! h₆
  have h₇ : |a n| < |L| / 2; linarith
  contrapose! h₇; exact le_of_lt # tendsTo_inv_aux₁ h

theorem tendsTo_inv {a L} (h₁ : ∀ n, a n ≠ 0) (h₂ : L ≠ 0)
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

@[simp]
theorem someLt_lt {x} : someLt x < x :=
  Classical.epsilon_spec (p := (· < x)) # exists_lt _

@[simp]
theorem lt_someGt {x} : x < someGt x :=
  Classical.epsilon_spec (p := (x < ·)) # exists_gt _

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
  simp [List.min?_eq_some_iff_1] at h₁
  rcases h₁ with ⟨⟨j, h₁, rfl⟩, h₂⟩
  by_cases h₃ : i < N
  · exact inf_le_of_right_le # h₂ i h₃
  push_neg at h₃
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
    _ ≤ |a₂ n * (a₁ n - L₁)| + |L₁ * (a₂ n - L₂)| := by apply abs_add
    _ = |a₂ n| * |a₁ n - L₁| + |L₁| * |a₂ n - L₂| := by simp [abs_mul]
    _ = a₂ n * |a₁ n - L₁| + L₁ * |a₂ n - L₂| := by
      congr; exact abs_of_pos h₄; exact abs_of_pos h₅
    _ < a₂ n * x + L₁ * |a₂ n - L₂| := by simpa [mul_lt_mul_left h₄]
    _ < a₂ n * x + L₁ * y := by simpa [mul_lt_mul_left h₅]
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
    · push_neg at h₃
      have H₃ := abs_nonneg # lb a₂
      suffices H₁ : 0 < a₁ i + |lb a₁| + 1; linarith
      rw [abs_eq_ite]; split_ifs <;> linarith
  have H₂ : ∀ i, 2 < b₂ i
  · intro i; simp [←hb₂, ←hm]
    have H := lb_lt_of_tendsTo h₂ |>.1 i
    simp [max_eq_ite]; split_ifs with h₃
    · push_neg at h₃
      have H₃ := abs_nonneg # lb a₁
      suffices H₁ : 0 < a₂ i + |lb a₂| + 1; linarith
      rw [abs_eq_ite]; split_ifs <;> linarith
    · rw [abs_eq_ite]; split_ifs <;> linarith
  have H₃ : 2 < m
  · rw [←hm]
    suffices : 0 < 1 + max |lb a₁| |lb a₂|; linarith
    suffices : 0 ≤ max |lb a₁| |lb a₂|; linarith
    simp
  have h₃ := @tendsTo_add a₁ (λ _ => m) L₁ m h₁ tendsTo_const
  have h₄ := @tendsTo_add a₂ (λ _ => m) L₂ m h₂ tendsTo_const
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
  have h₅ : tendsTo b₁ (L₁ + m); subst hb₁; exact tendsTo_add h₁ tendsTo_const
  have h₆ : tendsTo b₂ (L₂ + m); subst hb₂; exact tendsTo_add h₂ tendsTo_const
  apply tendsTo_add _ tendsTo_const
  apply tendsTo_sub
  rotate_left
  · apply tendsTo_mul_aux₁ tendsTo_const (tendsTo_add h₅ h₆) _ H₃
    · linarith
    · intro i
      specialize H₁ i
      specialize H₂ i
      simp [←hb₁, ←hb₂] at H₁ H₂ ⊢
      linarith
  apply tendsTo_mul_aux₁ h₅ h₆ H₂ H₄ H₅

theorem tendsTo_div {a₁ a₂ L₁ L₂} (h₁ : ∀ n, a₂ n ≠ 0) (h₂ : L₂ ≠ 0)
(h₃ : tendsTo a₁ L₁) (h₄ : tendsTo a₂ L₂) : tendsTo (a₁ / a₂) (L₁ / L₂) :=
  tendsTo_mul h₃ # tendsTo_inv h₁ h₂ h₄

theorem squeeze {a b c : ℕ → ℝ} {L} (h₁ : ∀ n, a n ≤ b n) (h₂ : ∀ n, b n ≤ c n)
(h₃ : tendsTo a L) (h₄ : tendsTo c L) : tendsTo b L := by
  intro e he
  specialize h₃ e he
  specialize h₄ e he
  obtain ⟨N₁, h₃⟩ := h₃
  obtain ⟨N₂, h₄⟩ := h₄
  use N₁ + N₂
  intro n hn
  specialize h₁ n
  specialize h₂ n
  specialize h₃ n # by linarith
  specialize h₄ n # by linarith
  rw [abs_lt] at h₃ h₄ ⊢
  constructor <;> linarith