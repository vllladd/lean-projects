import AP.Util.Function

namespace Nat

noncomputable
def find! (p : ℕ → Prop) : ℕ :=
  haveI := Classical.propDecidable
  if h : ∃ n, p n ∧ ∀ k < n, ¬p k then h.choose else 0

-----

theorem rec_const (n m : ℕ) : n.rec m (λ _ a => a) = m := by
  induction n <;> simp_all only [rec_zero]

theorem rec_succ' {α : Type*} {z : α} (f : ℕ → α → α) {n : ℕ} :
@rec (λ _ => α) z f (n + 1) =
@rec (λ _ => α) (f 0 z) (λ m => f (m + 1)) n := by
  induction n generalizing z f; simp
  nm n ih; exact congrArg (f (n + 1)) (ih f)

theorem infi_eq_zero_of {f : ℕ → ℕ} k (h : f k = 0) : ⨅ x, f x = 0 := by
  rw [iInf, sInf_eq_zero]; left; simp; use k

theorem le_sub_add_of {a b c : ℕ} (h : a ≤ b) : a ≤ b - c + c := by
  trans b; exact h; exact le_tsub_add

theorem le_sub_add_add_of {a b c d : ℕ} (h : a ≤ b) : a ≤ b - c + d + c := by
  rw [add_assoc]; nth_rewrite 2 [add_comm]
  rw [←add_assoc]; trans b - c + c
  exact le_sub_add_of h; apply le_add_right

theorem rec_le_of_sub_sub {n z : ℕ} (f g : ℕ → ℕ) :
@rec (λ _ => ℕ) z (λ k x => x - f k - g k) n ≤
@rec (λ _ => ℕ) z (λ k x => x - f k) n := by
  induction n <;> simp
  nm n ih; exact le_sub_add_add_of ih

@[simp]
theorem ite_11_iff : ∀ {P Q h₁ h₂},
@ite _ P h₁ 1 0 = @ite _ Q h₂ 1 0 ↔ (P ↔ Q) := by
  apply prop_ind <;> apply prop_ind <;> simp

@[simp]
theorem ite_00_iff : ∀ {P Q h₁ h₂},
@ite _ P h₁ 0 1 = @ite _ Q h₂ 0 1 ↔ (P ↔ Q) := by
  apply prop_ind <;> apply prop_ind <;> simp

@[simp]
theorem ite_10_iff : ∀ {P Q h₁ h₂},
@ite _ P h₁ 1 0 = @ite _ Q h₂ 0 1 ↔ (P ↔ ¬Q) := by
  apply prop_ind <;> apply prop_ind <;> simp

@[simp]
theorem ite_01_iff : ∀ {P Q h₁ h₂},
@ite _ P h₁ 0 1 = @ite _ Q h₂ 1 0 ↔ (P ↔ ¬Q) := by
  apply prop_ind <;> apply prop_ind <;> simp

theorem rec_sub {n k m : ℕ} {f : ℕ → ℕ} :
@rec (λ _ => ℕ) (n - k) (λ k a => a - f k) m =
@rec (λ _ => ℕ) n (λ k a => a - f k) m - k := by
  induction m <;> simp
  nm m ih; rw [ih]; apply Nat.sub_right_comm

@[simp]
theorem add_succ_max_ne_left {x a b : ℕ} :
x + (max a b + 1) ≠ a := by
  simp; apply ne_of_gt; apply Nat.lt_add_left
  apply lt_add_one_of_le; apply le_max_left

@[simp]
theorem add_succ_max_ne_right {x a b : ℕ} : x + (max a b + 1) ≠ b := by
  rw [max_comm]; simp

@[simp]
theorem left_lt_succ_max {a b : ℕ} : a < max a b + 1 := by
  simp

@[simp]
theorem right_lt_succ_max {a b : ℕ} : b < max a b + 1 := by
  simp

theorem add_add_sub_cancel {a b c : ℕ} : a + b + c - b = a + c := by
  rw [add_assoc, Nat.add_sub_assoc] <;> simp

theorem add_succ_ne_right {a b : ℕ} : a + (b + 1) ≠ b := by
  nth_rewrite 2 [add_comm]; rw [←add_assoc]; simp

theorem fn_set_add {a b : ℕ} {f : ℕ → ℕ} {x : ℕ} :
fn_set a (f a + b) f x = f x + if x = a then b else 0 := by
  rw [fn_set_eq]; aesop

theorem eq_add_of_sub_eq_succ {a b c} (h : a - b = c + 1) :
a = c + 1 + b := by
  rw [Nat.sub_eq_iff_eq_add] at h; exact h; by_contra! h₁
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h₁
  rw [add_assoc, sub_add_eq] at h; simp at h

theorem eq_add_iff_sub_eq_succ {a b c} :
a = c + 1 + b ↔ a - b = c + 1 := by
  apply Iff.intro <;> intro h; simp [h]
  exact eq_add_of_sub_eq_succ h

theorem eq_add_of_one_eq_sub {a b : ℕ} (h : 1 = a - b) : a = b + 1 := by
  have h₁ : b ≤ a := by
    apply le_of_lt; apply Nat.lt_of_sub_pos; simp [←h]
  have h₂ : b + 1 = b + (a - b) := by rw [h]
  rw [←Nat.add_sub_assoc h₁] at h₂
  simp at h₂; exact h₂.symm

theorem one_eq_sub_iff {a b : ℕ} : 1 = a - b ↔ a = b + 1 :=
  ⟨eq_add_of_one_eq_sub, by rintro rfl; simp⟩

@[simp]
theorem not_lt_sub {a b : ℕ} : ¬(a < a - b) := by simp

theorem sub_eq_left_iff {a b : ℕ} : a - b = a ↔ a = 0 ∨ b = 0 := by
  cases a <;> simp; cases b <;> simp
  exact ne_of_lt # sub_lt_of_lt # by simp

@[simp]
theorem ite_10_le_one {P : Prop} [Decidable P] : ite P 1 0 ≤ 1 := by
  split_ifs <;> simp

@[simp]
theorem ite_01_le_one {P : Prop} [Decidable P] : ite P 0 1 ≤ 1 := by
  split_ifs <;> simp

theorem even_iff_exi {n : ℕ} : Even n ↔ ∃ k, n = k * 2 := by
  rw [Even]; ring_nf

theorem odd_iff_exi {n : ℕ} : Odd n ↔ ∃ k, n = k * 2 + 1 := by
  rw [Odd]; ring_nf

theorem mod_2_ind {p : ℕ → Prop}
(h₁ : ∀ n, p (n * 2)) (h₂ : ∀ n, p (n * 2 + 1)) (n : ℕ) : p n := by
  rcases even_or_odd n with h | h
  · obtain ⟨k, rfl⟩ := even_iff_exi.mp h; apply h₁
  · obtain ⟨k, rfl⟩ := odd_iff_exi.mp h; apply h₂

theorem not_even_mul_2_succ {n : ℕ} : ¬Even (n * 2 + 1) := by simp

@[simp]
theorem not_odd_mul_2 {n : ℕ} : ¬Odd (n * 2) := by simp

@[simp]
theorem even_succ_iff {n : ℕ} : Even (n + 1) ↔ Odd n := by
  simp [even_add_one]

@[simp]
theorem odd_succ_iff {n : ℕ} : Odd (n + 1) ↔ Even n := by
  simp [odd_add_one]

theorem even_of_succ_div_2_eq {n : ℕ}
(h : (n + 1) / 2 = n / 2) : Even n := by
  contrapose! h; simp [odd_iff_exi] at h
  obtain ⟨n, rfl⟩ := h; rw [div_eq]
  simp; induction n; simp; nm n ih; contrapose! ih; ring_nf at ih ⊢
  have h₁ : (n * 2 + 1 + 2) / 2 = (n * 2 + 1) / 2 + 1 := by simp
  ring_nf at h₁; rw [h₁, add_comm] at ih; nth_rewrite 2 [add_comm] at ih
  rw [add_comm]; exact succ_inj.mp ih

theorem odd_of_succ_div_2_eq {n : ℕ}
(h : (n + 1) / 2 = n / 2 + 1) : Odd n := by
  contrapose! h; simp [even_iff_exi] at h;
  obtain ⟨n, rfl⟩ := h; rw [div_eq]; induction n; trivial
  nm n ih; cases n; trivial; nm n; simp [add_mul] at ih ⊢
  change (_ + (1 + 2)) / _ ≠ _; rw [←add_assoc]; simpa

theorem le_one_iff {n : ℕ} : n ≤ 1 ↔ n = 0 ∨ n = 1 := by
  cases n; simp; nm n; cases n <;> simp

theorem of_between_succ {a b : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ a + 1) :
b = a ∨ b = a + 1 := by
  obtain ⟨k, rfl⟩ := exists_add_of_le h₁
  simp at h₂ ⊢; rw [le_one_iff] at h₂; exact h₂

theorem succ_div_2_eq_or_eq (n : ℕ) :
(n + 1) / 2 = n / 2 ∨ (n + 1) / 2 = n / 2 + 1 := by
  have h₁ := add_div_le_add_div n 1 2
  have h₂ := add_div_le_add_div (n + 1) 1 2
  simp [add_assoc] at h₁ h₂; exact of_between_succ h₁ h₂

@[simp]
theorem succ_div_2_eq_div_iff {n : ℕ} :
(n + 1) / 2 = n / 2 ↔ Even n := by
  refine' ⟨even_of_succ_div_2_eq, _⟩
  intro h; contrapose h; simp
  apply odd_of_succ_div_2_eq
  rcases succ_div_2_eq_or_eq n with h₃ | h₃
  contradiction; exact h₃

@[simp]
theorem succ_div_2_eq_div_iff' {n : ℕ} :
n / 2 = (n + 1) / 2 ↔ Even n := by
  rw [eq_comm]; exact succ_div_2_eq_div_iff

@[simp]
theorem succ_div_2_eq_div_succ_iff {n : ℕ} :
(n + 1) / 2 = n / 2 + 1 ↔ Odd n := by
  cases n; simp; nm n; simp [add_assoc]

@[simp]
theorem succ_div_2_eq_div_succ_iff' {n : ℕ} :
n / 2 + 1 = (n + 1) / 2 ↔ Odd n := by
  rw [eq_comm]; exact succ_div_2_eq_div_succ_iff

@[simp]
theorem mul_2_succ_div_2_eq (n : ℕ) : (n * 2 + 1) / 2 = n := by
  suffices (n * 2 + 1) / 2 = n * 2 / 2 by simp at this; assumption
  rw [succ_div_2_eq_div_iff]; simp

theorem find!_eq {p} :
haveI := Classical.propDecidable
find! p = if h : ∃ n, p n then Nat.find h else 0 := by
  classical
  unfold find!
  symm
  by_cases h₁ : ∃ n, p n
  · have h₂ : ∃ n, p n ∧ ∀ k < n, ¬p k :=
      by
        use Nat.find h₁
        rw [←Nat.find_eq_iff h₁]
    simp [h₁, h₂]
    generalize_proofs
    rw [Nat.find_eq_iff h₁]
    exact h₂.choose_spec
  split_ifs with h₂
  · simp at h₁
    obtain ⟨n, h₂⟩ := h₂
    cases h₁ n h₂.1
  rfl

theorem find!_spec' {p : ℕ → Prop} (h : ∃ n, p n) : p (find! p) ∧
∀ k, p k → find! p ≤ k := by
  classical
  simp [find!_eq, h]
  use Nat.find_spec h
  intro k hk
  use k

theorem find!_spec {p : ℕ → Prop} (h : ∃ n, p n) : p (find! p) := by
  exact (find!_spec' h).1

theorem find!_eq_of {p : ℕ → Prop} {n} (h₁ : p n) (h₂ : ∀ k < n, ¬p k) :
find! p = n := by
  classical
  rw [find!_eq]
  split_ifs with h₃
  · rw [Nat.find_eq_iff]
    tauto
  simp at h₃
  specialize h₃ n
  contradiction

theorem find!_eq_zero_of {p : ℕ → Prop} (h : ∀ n, ¬p n) : find! p = 0 := by
  rw [find!_eq]
  split_ifs with h₁
  · contrapose! h
    exact h₁
  rfl

theorem find!_eq_iff {p : ℕ → Prop} {n} : by classical exact (
find! p = n ↔ ite (∃ n, p n) (p n ∧ ∀ k < n, ¬p k) (n = 0)) := by
  split_ifs with h₁
  · rw [find!_eq]; simp [h₁, Nat.find_eq_iff]
  simp at h₁
  rw [find!_eq_zero_of h₁, eq_comm]

theorem find!_min {p : ℕ → Prop} {n} (h : n < find! p) : ¬p n := by
  classical
  rw [find!_eq] at h
  split_ifs at h with h₁
  · exact Nat.find_min h₁ h
  simp at h

theorem find!_eq_of_not_ap_zero {p : ℕ → Prop}
(h₁ : ∃ n, p n) (h₂ : ¬p 0) : find! p = find! (λ m => p # m + 1) + 1 := by
  apply find!_eq_of
  · apply @find!_spec (p # · + 1)
    obtain ⟨n, hn⟩ := h₁
    cases n
    · contradiction
    nm n
    use n
  intro k hk
  cases k
  · exact h₂
  nm k
  simp at hk
  apply @find!_min (p # · + 1)
  exact hk

theorem find!_eq_of_not_ap_le {p : ℕ → Prop}
(n : ℕ) (h₁ : ∃ n, p n) (h₂ : ∀ k ≤ n, ¬p k) :
find! p = find! (λ m => p (n + m)) + n := by
  classical
  induction n generalizing p
  · simp
  nm n ih
  have h₃ : ¬p 0 :=
    by
      apply h₂; simp
  specialize @ih (p # · + 1) _ _ <;> try dsimp
  · obtain ⟨k, hk⟩ := h₁
    cases k
    · contradiction
    nm k
    use k
  · intro k hk
    apply h₂
    simpa
  rw [find!_eq_of_not_ap_zero h₁ h₃, ih]; clear ih
  ring_nf

theorem add_one_add {a b : ℕ} : a + 1 + b = a + b + 1 := by ring

theorem add_one_sub {a b : ℕ} (h : b ≤ a) : a + 1 - b = a - b + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  ring_nf; simp [add_add_sub_cancel]

theorem le_exp_left {a b : ℕ} (h : 2 ≤ b) : a ≤ b ^ a := by
  induction a; simp; rename_i a ha; simp [pow_succ]
  replace ha := Nat.add_le_add_right ha 1; apply ha.trans
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h; simp [mul_add, mul_two]
  suffices 1 ≤ (2 + b) ^ a + (2 + b) ^ a * b by linarith
  by_contra h; simp at h

theorem le_exp_right {a b : ℕ} (h : b ≠ 0) : a ≤ a ^ b := by
  cases b; simp at h; rename_i b; simp [pow_add]; cases a
  simp; rename_i a; cases b; simp; rename_i b
  simp [pow_add]; by_contra h₁; simp at h₁

theorem find_le_find_of_imp {P Q : ℕ → Prop}
[hp : DecidablePred P] [hq : DecidablePred Q]
{h₁ : ∃ n, P n} {h₂ : ∃ n, Q n} (h₃ : ∀ n, Q n → P n) :
Nat.find h₁ ≤ Nat.find h₂ := by
  apply Nat.find_le; apply h₃; exact Nat.find_spec h₂

@[simp]
theorem le_self_mul_iff {a b : ℕ} : a ≤ a * b ↔ a = 0 ∨ b ≠ 0 := by
  constructor
  · intro h; rw [or_iff_not_imp_left]
    rintro h₁ rfl; simp at h; contradiction
  rintro (rfl | h); simp
  cases b; simp at h; nm b
  simp [mul_succ]

@[simp]
theorem lt_self_add_iff {a b : ℕ} : a < a + b ↔ 0 < b :=
  Nat.lt_add_right_iff_pos

@[simp]
theorem div_mul_sub_one_le {n k} : n / k * (k - 1) ≤ n / k * k := by
  rw [Nat.mul_sub]; simp

@[simp] theorem div_mul_le_self' {m n : ℕ} : m / n * n ≤ m := div_mul_le_self _ _
@[simp] theorem mod_add_div₁ {m k : ℕ} : m % k + k * (m / k) = m := mod_add_div _ _
@[simp] theorem mod_add_div₂ {m k : ℕ} : m % k + (m / k) * k = m := mod_add_div' _ _
@[simp] theorem div_add_mod₁ {m k : ℕ} : k * (m / k) + m % k = m := div_add_mod _ _
@[simp] theorem div_add_mod₂ {m k : ℕ} : (m / k) * k + m % k = m := div_add_mod' _ _

theorem div_mul_le_of_le {a b c : ℕ} (h : c ≤ b) : a / b * c ≤ a := by
  by_cases hc : c = 0; simp [hc]
  rw [←le_div_iff_mul_le # zero_lt_of_ne_zero hc]
  exact Nat.div_le_div (by rfl) h hc

theorem add_sub_lt_add_of_sub_lt {a b c d : ℕ} (h : b - c < d) : a + b - c < a + d := by
  omega

theorem mod_self_sub_one_eq_one {n} (h : 3 ≤ n) : n % (n - 1) = 1 := by
  cases n; simp at h; nm n; simp at h ⊢; apply Nat.mod_eq_of_lt; linarith

theorem ne_zero_of_mod_ne_zero {n k} (h : n % k ≠ 0) : n ≠ 0 := by
  contrapose! h; simp [h]

@[simp]
theorem even_or_odd₁ {n : ℕ} : Even n ∨ Odd n :=
  even_or_odd n

@[simp]
theorem odd_or_even₁ {n : ℕ} : Odd n ∨ Even n :=
  even_or_odd₁.symm

theorem ite_odd {α : Type*} {n : ℕ} {x y : α} : ite (Odd n) x y = ite (Even n) y x := by
  simp_rw [←not_odd_iff_even, ite_not]

theorem ite_even {α : Type*} {n : ℕ} {x y : α} : ite (Even n) x y = ite (Odd n) y x :=
  ite_odd.symm

theorem exi_least_of_exi {p : ℕ → Prop} (h : ∃ n, p n) : ∃ n, p n ∧ ∀ k, k < n → ¬p k := by
  use Nat.find! p; convert Nat.find!_spec' h using 1
  constructor <;> intro h k hk
  · by_contra! h₁; exact h _ h₁ hk
  · intro h₁; specialize h _ h₁; linarith

theorem exi_iff_exi_least {p : ℕ → Prop} : (∃ n, p n) ↔ ∃ n, p n ∧ ∀ k, k < n → ¬p k := by
  constructor; use exi_least_of_exi; tauto

@[simp]
theorem le_self_sub_add_one_iff {a b : ℕ} : a ≤ a - (b + 1) ↔ a = 0 := by
  omega

theorem find!_pos_of {p} (h₁ : ¬p 0) (h₂ : ∃ n, p n) : 0 < find! p := by
  choose h₃ h₄ using Nat.find!_spec' h₂
  cases h₅ : find! p
  · simp [h₁, h₅] at h₃
  · simp