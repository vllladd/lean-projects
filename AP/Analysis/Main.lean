import AP.Util

section util

theorem min_eq_ite {α : Type*} [ha : LinearOrder α] {x y : α} :
min x y = if x ≤ y then x else y := by
  split_ifs with h₁; exact min_eq_left h₁; push_neg at h₁; exact min_eq_right_of_lt h₁

theorem bddBelow_range_of_forall_le {ι α : Type*} [ha : LinearOrder α]
{f : ι → α} (x) (h : ∀ i, x ≤ f i) : BddBelow (Set.range f) := by
  use x; simpa [lowerBounds]

theorem bddAbove_range_of_forall_le {ι α : Type*} [ha : LinearOrder α]
{f : ι → α} (x) (h : ∀ i, f i ≤ x) : BddAbove (Set.range f) := by
  use x; simpa [upperBounds]

theorem bddBelow_range {ι α : Type*} [ha : LinearOrder α] {f : ι → α} :
BddBelow (Set.range f) ↔ ∃ x, ∀ i, x ≤ f i := by
  constructor
  · intro h; rcases h with ⟨x, h⟩; simp [lowerBounds] at h; use x
  · rintro ⟨x, h⟩; exact bddBelow_range_of_forall_le x h

theorem bddAbove_range {ι α : Type*} [ha : LinearOrder α] {f : ι → α} :
BddAbove (Set.range f) ↔ ∃ x, ∀ i, f i ≤ x := by
  constructor
  · intro h; rcases h with ⟨x, h⟩; simp [upperBounds] at h; use x
  · rintro ⟨x, h⟩; exact bddAbove_range_of_forall_le x h

theorem bddBelow_range_neg {ι α : Type} [ha₁ : LinearOrder α] [ha₂ : Ring α]
[ha₃ : AddLeftMono α] [ha₄ : AddRightMono α] {f : ι → α} :
BddBelow (Set.range (-f)) ↔ BddAbove (Set.range f) := by
  simp [bddBelow_range, bddAbove_range]
  constructor <;> rintro ⟨x, hx⟩ <;> use -x <;> intro i <;> specialize hx i
  · rwa [←neg_neg # f i, neg_le_neg_iff]
  · rwa [neg_le_neg_iff]

theorem bddAbove_range_neg {ι α : Type} [ha₁ : LinearOrder α] [ha₂ : Ring α]
[ha₃ : AddLeftMono α] [ha₄ : AddRightMono α] {f : ι → α} :
BddAbove (Set.range (-f)) ↔ BddBelow (Set.range f) := by
  nth_rw 2 [←neg_neg f]; rw [bddBelow_range_neg]

-- #check 0 #exit

end util

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

-- #check 0 #exit

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

theorem lub_neg {a : ℕ → ℝ} (h : converges a) :
lub (-a) = -glb a := by
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

-- #check 0 #exit

theorem tendsTo_mul {a₁ a₂ L₁ L₂} (h₁ : tendsTo a₁ L₁)
(h₂ : tendsTo a₂ L₂) : tendsTo (a₁ * a₂) (L₁ * L₂) := by
  sorry

-- #check 0 #exit

theorem tendsTo_div {a₁ a₂ L₁ L₂}
(h₁ : ∀ n, a₂ n ≠ 0) (h₂ : L₂ ≠ 0) (h₃ : tendsTo a₁ L₁)
(h₄ : tendsTo a₂ L₂) : tendsTo (a₁ / a₂) (L₁ / L₂) :=
  tendsTo_mul h₃ # tendsTo_inv h₁ h₂ h₄