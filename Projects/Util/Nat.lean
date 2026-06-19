import Projects.Util.Function

namespace Nat

noncomputable
def find! (p : ℕ → Prop) : ℕ :=
  haveI := Classical.propDecidable
  if h : ∃ n, p n ∧ ∀ k < n, ¬p k then h.choose else 0

def powTwo (n : ℕ) : Bool :=
  if n = 1 then true
  else if n = 0 ∨ Odd n then false
  else powTwo (n / 2)

def chkLe (n : ℕ) (p : ℕ → Bool) : Bool :=
  p n && match n with
  | 0 => true
  | n + 1 => chkLe n p

def chkLt (n : ℕ) (p : ℕ → Bool) : Bool :=
  match n with
  | 0 => true
  | n + 1 => chkLe n p

-----

attribute [simp] mod_one mod_le

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
  rw [add_assoc]; nth_rw 2 [add_comm]
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
  nth_rw 2 [add_comm]; rw [←add_assoc]; simp

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
  ring_nf at h₁; rw [h₁, add_comm] at ih; nth_rw 2 [add_comm] at ih
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
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h; simp [mul_add]
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

attribute [simp] Nat.sub_pos_iff_lt

theorem odd_add_two {n} : Odd (n + 2) ↔ Odd n := by
  simp

theorem even_add_two {n} : Even (n + 2) ↔ Even n := by
  simp

@[simp]
theorem odd_sub_one_iff {n} : Odd (n - 1) ↔ n ≠ 0 ∧ Even n := by
  grind

@[simp]
theorem even_sub_one_iff {n} : Even (n - 1) ↔ n = 0 ∨ Odd n := by
  grind

theorem mul_div_mul {a b c : ℕ} (hb : b ≠ 0) : a * b / (b * c) = a / c := by
  by_cases hc : c = 0; simp [hc]
  have h : a * b * c = a * (b * c); rw [mul_assoc]
  replace h := congrArg (· / c / (b * c)) h
  rw [Nat.mul_div_cancel _ # by omega] at h
  rw [h, Nat.div_right_comm, Nat.mul_div_cancel _ # by positivity]

@[simp]
theorem mul_div_mul_succ {a b c : ℕ} : a * (b + 1) / ((b + 1) * c) = a / c :=
  mul_div_mul # by simp

theorem one_le_of_odd {n : ℕ} (h : Odd n) : 1 ≤ n := by
  by_contra h₁; simp at h₁; simp [h₁] at h

attribute [simp] lt_one_add_iff

@[simp]
theorem fn_max_zero : max 0 = id := by
  funext; simp

@[simp]
theorem odd_two_pow_iff {n : ℕ} : Odd (2 ^ n) ↔ n = 0 := by
  grind

@[simp]
theorem powTwo_eq_true_iff {n} : powTwo n ↔ ∃ k, 2 ^ k = n := by
  fun_induction powTwo; simp
  · nm n h₁ h₂
    simp
    rintro k rfl
    simp_all
  nm n h₁ h₂ ih
  simp at h₂
  rw [ih]; clear ih
  rw [even_iff_exi] at h₂
  rcases h₂ with ⟨h₂, n, rfl⟩
  simp
  cases n
  · simp at h₂
  nm n
  constructor <;> rintro ⟨k, h₃⟩
  · use k + 1
    omega
  · cases k
    · omega
    nm k
    use k
    omega

@[simp]
theorem powTwo_eq_false_iff {n} : powTwo n = false ↔ ∀ k, 2 ^ k ≠ n := by
  contrapose!; simp

instance {n : ℕ} : Decidable (∃ k, 2 ^ k = n) :=
  decidable_of_iff' (powTwo n) (by simp)

instance {n : ℕ} : Decidable (∀ k, 2 ^ k ≠ n) :=
  decidable_of_iff' (!powTwo n) (by simp)

@[simp]
theorem chkLe_eq_true_iff {n p} : chkLe n p ↔ ∀ k ≤ n, p k := by
  induction n <;> simp [chkLe]; grind

@[simp]
theorem chkLe_eq_false_iff {n p} : chkLe n p = false ↔ ∃ k ≤ n, !p k := by
  induction n <;> simp [chkLe]; grind

@[simp]
theorem chkLt_eq_true_iff {n p} : chkLt n p ↔ ∀ k < n, p k := by
  induction n <;> simp [chkLt]

@[simp]
theorem chkLt_eq_false_iff {n p} : chkLt n p = false ↔ ∃ k < n, !p k := by
  induction n <;> simp [chkLt]

instance {n : ℕ} {p : ℕ → Prop} [h : ∀ k, Decidable (p k)] : Decidable (∀ k ≤ n, p k) :=
  decidable_of_iff' (chkLe n p) (by simp)

instance {n : ℕ} {p : ℕ → Prop} [h : ∀ k, Decidable (p k)] : Decidable (∃ k ≤ n, p k) :=
  decidable_of_iff' (!chkLe n (!p ·)) (by simp)

instance {n : ℕ} {p : ℕ → Prop} [h : ∀ k, Decidable (p k)] : Decidable (∀ k < n, p k) :=
  decidable_of_iff' (chkLt n p) (by simp)

instance {n : ℕ} {p : ℕ → Prop} [h : ∀ k, Decidable (p k)] : Decidable (∃ k < n, p k) :=
  decidable_of_iff' (!chkLt n (!p ·)) (by simp)

@[simp]
theorem mul_two_lor_mul_two {n m : ℕ} : n * 2 ||| m * 2 = (n ||| m) * 2 := by
  change bitwise _ _ _ = (bitwise _ _ _) * 2; rw [bitwise]; simp; split_ifs with h₁ h₂
  change _ = (_ ||| _) * 2; simp [h₁]; change _ = (_ ||| _) * 2; simp [h₂]; omega

@[simp]
theorem mul_two_succ_lor_mul_two {n m : ℕ} : n * 2 + 1 ||| m * 2 = (n ||| m) * 2 + 1 := by
  change bitwise _ _ _ = (bitwise _ _ _) * 2 + 1; rw [bitwise]; simp; split_ifs with h₁
  change _ = (_ ||| _) * 2 + 1; simp [h₁]; omega

@[simp]
theorem mul_two_lor_mul_two_succ {n m : ℕ} : n * 2 ||| m * 2 + 1 = (n ||| m) * 2 + 1 := by
  rw [Nat.or_comm]; simp; rw [Nat.or_comm]

@[simp]
theorem mul_two_succ_lor_mul_two_succ {n m : ℕ} : n * 2 + 1 ||| m * 2 + 1 = (n ||| m) * 2 + 1 := by
  change bitwise _ _ _ = (bitwise _ _ _) * 2 + 1; rw [bitwise]; simp; omega

@[simp]
theorem odd_lor_iff {n m : ℕ} : Odd (n ||| m) ↔ Odd n ∨ Odd m := by
  induction n using Nat.mod_2_ind <;> nm n <;>
  induction m using Nat.mod_2_ind <;> nm m <;> simp

@[simp]
theorem even_lor_iff {n m : ℕ} : Even (n ||| m) ↔ Even n ∧ Even m := by
  rw [←not_odd_iff_even, odd_lor_iff]; simp

@[simp]
theorem even_shiftLeft_succ {n k : ℕ} : Even (n <<< (k + 1)) := by
  simp [shiftLeft_eq, pow_succ]

@[simp]
theorem not_odd_shiftLeft_succ {n k : ℕ} : ¬Odd (n <<< (k + 1)) := by
  simp

@[simp]
theorem forall_even_shiftRight_iff {n : ℕ} : (∀ k, Even (n >>> k)) ↔ n = 0 := by
  symm; constructor; rintro rfl; simp
  intro h
  induction n using Nat.strong_induction_on
  nm n ih
  by_cases h₁ : n >>> 1 = 0
  · cases n; rfl; nm n
    rw [Nat.shiftRight_eq_div_pow] at h₁
    simp at h₁
    subst h₁
    specialize h 0
    simp at h
  specialize ih (n >>> 1) (by omega)
  simp [h₁] at ih
  choose k ih using ih
  specialize h (k + 1)
  rw [add_comm] at h
  simp [Nat.shiftRight_add] at h
  grind

theorem shiftRight_add' {n m k : ℕ} : n >>> (m + k) = n >>> k >>> m := by
  rw [add_comm, shiftRight_add]

@[simp]
theorem mul_two_add_one_div_two {n : ℕ} : (n * 2 + 1) / 2 = n := by
  omega

theorem div_two_eq_shiftRight {n : ℕ} : n / 2 = n >>> 1 := by
  simp [shiftRight_eq_div_pow]

theorem eq_iff_odd_shiftRight {n m : ℕ} : n = m ↔ ∀ k, Odd (n >>> k) ↔ Odd (m >>> k) := by
  constructor; rintro rfl; simp; intro h
  induction n using Nat.strong_induction_on generalizing m
  nm n ih
  by_cases h₁ : n = 0
  · clear ih
    subst h₁
    simp at h
    rw [h]
  by_cases h₂ : m = 0
  · clear ih
    subst h₂
    simp at h
    rw [h]
  by_cases h₃ : n = 1
  · subst h₃; clear h₁
    have h₃ := h 0
    simp at h₃
    replace h := forall_spec (· + 1) h
    simp [shiftRight_add'] at h
    cases m; simp at h₂; nm m; cases m; rfl; nm m
    simp [add_assoc, shiftRight_eq_div_pow] at h
  have h₄ : m ≠ 1
  · rintro rfl
    clear h₂
    have h₂ := h 0
    simp at h₂
    replace h := forall_spec (· + 1) h
    simp [shiftRight_add'] at h
    cases n; simp at h₂; nm n; cases n; simp at h₃
    simp [add_assoc, shiftRight_eq_div_pow] at h
  simp at h₄
  specialize @ih (n >>> 1) (by omega) (m >>> 1)
  convert_to n / 2 * 2 + n % 2 = m / 2 * 2 + m % 2; iterate 2 simp
  have h₅ : m % 2 = n % 2
  · specialize h 0
    simp at h
    grind
  rw [h₅]; clear h₅
  congr 2
  simp [Nat.div_two_eq_shiftRight]
  apply ih
  intro k
  specialize h (k + 1)
  simpa [shiftRight_add'] using h

attribute [simp] Nat.lt_two_pow_self

@[simp]
theorem shiftRight_add_left {n m : ℕ} : n >>> (m + n) = 0 := by
  rw [shiftRight_eq_div_pow]; simp; apply lt_of_le_of_lt (b := m + n) <;> simp

@[simp]
theorem shiftRight_add_right {n m : ℕ} : n >>> (n + m) = 0 := by
  rw [add_comm]; simp

theorem div_mul_eq_div_div {n m k : ℕ} : n / (m * k) = n / m / k := by
  rw [Nat.div_div_eq_div_mul]

@[simp]
theorem mul_two_add_one_div_two_pow_succ {n m : ℕ} : (n * 2 + 1) / 2 ^ (m + 1) = n / 2 ^ m := by
  rw [pow_succ]; nth_rw 2 [mul_comm]; rw [div_mul_eq_div_div]; simp

@[simp]
theorem mul_two_add_one_shiftRight_succ {n m : ℕ} : (n * 2 + 1) >>> (m + 1) = n >>> m := by
  simp [shiftRight_eq_div_pow]

@[simp]
theorem lor_one_shiftRight_succ {n m : ℕ} : (n ||| 1) >>> (m + 1) = n >>> (m + 1) := by
  change bitwise _ _ _ >>> _ = _
  unfold bitwise
  simp
  split_ifs with h
  · simp [h]
  change ((_ ||| 0) + (_ ||| 0) + 1) >>> _ = _
  simp [←mul_two]
  simp [shiftRight_eq_div_pow, pow_succ', Nat.div_div_eq_div_mul]

@[simp]
theorem mul_two_shiftRight_succ {n m : ℕ} : (n * 2) >>> (m + 1) = n >>> m := by
  simp [shiftRight_eq_div_pow, pow_succ']

theorem lor_one_eq_ite {n : ℕ} : n ||| 1 = if Odd n then n else n + 1 := by
  change bitwise _ _ _ = _
  unfold bitwise
  simp
  split_ifs with h₁ h₂ h₂
  iterate 2 grind
  all_goals
    change (_ ||| 0) + (_ ||| 0) + _ = _
    simp [←mul_two]
  · rw [odd_iff_exi] at h₂
    omega
  · simp at h₂
    rw [even_iff_exi] at h₂
    omega

@[simp]
theorem mul_two_lor_one_eq {n : ℕ} : n * 2 ||| 1 = n * 2 + 1 := by
  rw [lor_one_eq_ite]; simp

@[simp]
theorem mul_two_add_one_lor_one_eq {n : ℕ} : (n * 2 + 1) ||| 1 = n * 2 + 1 := by
  rw [lor_one_eq_ite]; simp

theorem mod_self_pow_succ {n m : ℕ} (hn : n ≠ 1) (hm : m ≠ 0) : n % n ^ (m + 1) = n := by
  cases n; simp; nm n; simp at hn; apply Nat.mod_eq_of_lt
  apply lt_self_pow₀ <;> simp <;> omega

theorem beq_eq_eq {n m : ℕ} : (n == m) = decide (n = m) := rfl

theorem mod_two_eq_one_iff_odd {n : ℕ} : n % 2 = 1 ↔ Odd n := by
  rw [Nat.odd_iff]

theorem mod_two_eq_zero_iff_even {n : ℕ} : n % 2 = 0 ↔ Even n := by
  rw [Nat.even_iff]

theorem testBit_eq_odd {n i : ℕ} : n.testBit i = decide (Odd (n >>> i)) := by
  simp [-decide_shiftRight_mod_two_eq_one, testBit, beq_eq_eq, mod_two_eq_one_iff_odd]

theorem ne_zero_of_odd {n : ℕ} (h : Odd n) : n ≠ 0 := by
  rintro rfl; simp at h

theorem pos_of_odd {n : ℕ} (h : Odd n) : 0 < n :=
  pos_of_ne_zero # ne_zero_of_odd h

@[simp]
theorem sum_min_left {n m : ℕ} : n - min n m = n - m := by
  omega

@[simp]
theorem sum_min_right {n m : ℕ} : n - min m n = n - m := by
  omega

theorem eq_div_mod (n k : ℕ) : n = n / k * k + n % k := by
  simp

theorem eq_mod_div (n k : ℕ) : n = n % k + n / k * k := by
  simp

theorem eq_of_mod_eq_mod {n m : ℕ} (k : ℕ)
(hn : n < k) (hm : m < k) (h : n % k = m % k) : n = m := by
  rw [mod_eq_of_lt hn, mod_eq_of_lt hm] at h; exact h

theorem ind_step (k : ℕ) {p : ℕ → Prop} (h₁ : ∀ n, n < k → p n)
(h₂ : ∀ n, (∀ c < n + k, p c) → p (n + k)) : ∀ n, p n := by
  intro n
  induction n using Nat.strong_induction_on
  nm n ih
  by_cases h₃ : n < k
  · exact h₁ _ h₃
  simp at h₃
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₃; clear h₃
  rw [add_comm] at ih ⊢
  exact h₂ _ ih

theorem not_le_mod {n k : ℕ} (hk : k ≠ 0) : ¬(k ≤ n % k) := by
  simp; apply mod_lt; omega

@[simp]
theorem sub_succ_div_self_eq_zero {n m : ℕ} : (n - (m + 1)) / n = 0 := by
  rw [Nat.div_eq_zero_iff]; omega

theorem exi_mul_add (n b : ℕ) (h : b ≠ 0) : ∃ m r, r < b ∧ n = m * b + r := by
  use n / b, n % b; simp; apply Nat.mod_lt; omega

theorem lt_self_mul_add_iff {a b c : ℕ} : a < a * b + c ↔
(a ≠ 0 ∨ c ≠ 0) ∧ (a ≠ 0 → (b = 0 → a < c) ∧ (b ≠ 0 → c = 0 → b ≠ 1)) := by
  cases a <;> cases b <;> cases c <;> grind

@[simp]
theorem lt_self_mul_iff' {b n : ℕ} : n < n * b ↔ 2 ≤ b ∧ n ≠ 0 := by
  cases n <;> simp; omega

@[simp]
theorem lt_mul_self_iff' {b n : ℕ} : n < b * n ↔ 2 ≤ b ∧ n ≠ 0 := by
  rw [mul_comm]; simp

theorem eq_of_le_and_dvd {n b}
(hb : b ≠ 0) (hn : n ≠ 0) (h₁ : n ≤ b) (h₂ : b ∣ n) : n = b := by
  suffices : b ≤ n; omega
  by_contra! h₃
  clear h₁
  obtain ⟨n, rfl⟩ := h₂
  contrapose! h₃; clear h₃
  simp [hb]
  rintro rfl
  simp at hn

theorem eq_of_le_and_mod_eq_zero {n b}
(hb : b ≠ 0) (hn : n ≠ 0) (h₁ : n ≤ b) (h₂ : n % b = 0) : n = b :=
  eq_of_le_and_dvd hb hn h₁ # dvd_of_mod_eq_zero h₂

@[simp]
theorem not_prime_0 : ¬Nat.Prime 0 := by
  decide

@[simp]
theorem not_prime_1 : ¬Nat.Prime 1 := by
  decide

@[simp]
theorem prime_2 : Nat.Prime 2 := by
  decide

theorem prime_add_prime_iff {p : ℕ → ℕ → ℕ → Prop} (hp : ∀ a b c, p a b c ↔ p b a c) :
(∀ (a b c : ℕ), a.Prime → b.Prime → c.Prime → a + b = c → p a b c) ↔
(∀ (a c : ℕ), a.Prime → c.Prime → Odd a → a + 2 = c → p a 2 c) := by
  constructor
  · intro h a c ha hc ha₁
    apply h <;> simp [ha, hc]
  intro h a b c ha hb h₁ h₂
  have h₄ : Even a ↔ Odd b
  · by_contra h₅
    simp [not_iff'] at h₅
    by_cases h₄ : Even a <;> simp [h₄] at h₅
    · rw [Nat.Prime.even_iff (by assumption)] at h₄ h₅
      subst h₄ h₅ h₂
      norm_num at h₁
    simp at h₄
    have h₆ : Even c
    · subst h₂
      exact Odd.add_odd h₄ h₅
    rw [h₁.even_iff] at h₆
    subst h₆
    have := ha.two_le
    have := hb.two_le
    omega
  wlog h₅ : Odd a ∧ Even b with ih
  · rw [hp]
    apply @ih p hp h b a c hb ha h₁ (by omega) <;> clear ih h
    · contrapose!; simp [h₄]
    simp at h₅
    rw [←Nat.not_odd_iff_even] at h₄ ⊢
    tauto
  clear h₄
  choose h₄ h₅ using h₅
  rw [hb.even_iff] at h₅
  subst h₅; clear hb
  tauto

theorem three_dvd_add_two_four {n : ℕ} : 3 ∣ n ∨ 3 ∣ n + 2 ∨ 3 ∣ n + 4 := by
  rw [show 4 = 1 + 3 by rfl, ←Nat.add_assoc, Nat.dvd_add_self_right]
  induction n <;> simp [add_assoc]; tauto

theorem prime_iff' {n : ℕ} : n.Prime ↔ 2 ≤ n ∧ ∀ k, 2 ≤ k → k < n → ¬(k ∣ n) := by
  constructor
  · intro h
    use h.two_le
    intro k h₁ h₂ h₃
    obtain ⟨n, rfl⟩ := h₃
    rw [prime_mul_iff] at h
    grind
  rintro ⟨h₁, h₂⟩
  constructor <;> simp; omega
  rintro a b rfl
  cases a; simp at h₁; nm a
  cases b; simp at h₁; nm b
  simp
  rw[or_iff_not_imp_left]
  intro ha
  by_contra hb
  apply h₂ (a + 1) (by omega) (by grind); clear h₂
  simp

theorem eq_of_prime_and_dvd {n p : ℕ} (hp : p.Prime) (hn : n.Prime) (h : p ∣ n) : n = p := by
  rw [prime_iff'] at hn; have h₁ := hn.2 p hp.two_le; simp [h] at h₁
  exact eq_of_le_and_dvd hp.ne_zero (by grind) h₁ h

@[simp]
theorem one_shiftLeft_eq_one_iff {n : ℕ} : 1 <<< n = 1 ↔ n = 0 := by
  cases n <;> simp [shiftLeft_eq]

theorem ind_bit {p : ℕ → Prop} (h₁ : p 0) (h₂ : ∀ n, p n → p (n * 2))
(h₃ : ∀ n, p n → p (n * 2 + 1)) : ∀ n, p n := by
  intro n; induction n using Nat.strong_induction_on; nm n ih
  induction n using mod_2_ind <;> nm n
  · cases n
    · simpa
    nm n
    apply h₂
    apply ih
    omega
  · apply h₃
    apply ih
    omega

theorem or_mul_two_pow {n m k : ℕ} : (n ||| m) * 2 ^ k = n * 2 ^ k ||| m * 2 ^ k := by
  iterate 3 rw [←shiftLeft_eq];; rw [shiftLeft_or_distrib]

theorem or_two_pow_eq_add_of {n k : ℕ} (h : n < 2 ^ k) : n ||| 2 ^ k = n + 2 ^ k := by
  induction n using ind_bit generalizing k
  · simp
  · nm n ih
    cases k
    · simp
    nm k
    simp [pow_add, ←add_mul] at h ⊢
    exact ih h
  · nm n ih
    cases k
    · simp at h
    nm k
    simp [pow_add] at h ⊢
    rw [show n * 2 + 1 + 2 ^ k * 2 = (n + 2 ^ k) * 2 + 1 by omega]
    simp
    apply ih
    omega

theorem two_pow_or_eq_add_of {n k : ℕ} (h : n < 2 ^ k) : 2 ^ k ||| n = 2 ^ k + n := by
  rw [Nat.or_comm, add_comm, or_two_pow_eq_add_of h]

theorem eq_div_add_mod (n b : ℕ) : n = n / b * b + n % b := by
  simp

theorem or_mul_two_pow_eq_add_of {n k c : ℕ}
(h : n < 2 ^ k) : n ||| c * 2 ^ k = n + c * 2 ^ k := by
  induction n using ind_bit generalizing k c
  · simp
  · nm n ih
    cases k
    ·
      simp at h
      simp [h]
    nm k
    simp [pow_add, ←mul_assoc, ←add_mul] at h ⊢
    exact ih h
  · nm n ih
    cases k
    · simp at h
    nm k
    simp [pow_add] at h ⊢
    rw [show n * 2 + 1 + c * (2 ^ k * 2) = (n + c * 2 ^ k) * 2 + 1 by nlinarith]
    simp [←mul_assoc]
    apply ih
    omega

theorem or_two_pow_mul_eq_add_of {n k c : ℕ}
(h : n < 2 ^ k) : n ||| 2 ^ k * c = n + 2 ^ k * c := by
  rw [mul_comm _ c, or_mul_two_pow_eq_add_of h]

@[simp]
theorem le_two_pow_self {n} : n ≤ 2 ^ n :=
  le_of_lt Nat.lt_two_pow_self

theorem mul_pow_mod_pow {b n k w : ℕ} : n * b ^ k % b ^ w = n % b ^ (w - k) * b ^ k := by
  induction k generalizing n w
  · simp
  nm k ih
  cases w
  · simp
  nm w
  simp [Nat.pow_add, ←mul_assoc]
  rw [Nat.mul_mod_mul_right]
  rw [ih]