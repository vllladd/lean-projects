import Projects.Util.Basic

section Id

variable {α β γ : Type}

@[simp]
theorem fmap_Id {f : α → β} {x : α} : @Functor.map Id _ α β f x = f x := by rfl

-- #check 0 #exit

end Id

namespace Nat

attribute [simp] mod_one

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

-- #check 0 #exit

end Nat

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

theorem range_add' {n m : Nat} : range (n + m) = range m ++ (range n).map (m + ·) := by
  rw [add_comm, range_add]

theorem range_succ' {n : ℕ} : range (n + 1) = 0 :: (range n).map (· + 1) := by
  rw [range_add']; simp; omega

attribute [-simp] List.getElem!_eq_getElem?_getD

@[simp]
theorem map_getElem!_range_length [ha : Inhabited α] :
(range xs.length).map (xs[·]!) = xs := by
  apply ext_getElem <;> simp

theorem map_getElem!_range_of_le_length [ha : Inhabited α] {n : ℕ}
(h : n ≤ xs.length) : (range n).map (xs[·]!) = xs.take n := by
  apply ext_getElem <;> simp; omega

theorem map_getElem!_range_of_length_le [ha : Inhabited α] {n : ℕ}
(h : xs.length ≤ n) : (range n).map (xs[·]!) = xs ++ replicate (n - xs.length) default := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h; simp [range_add]

theorem map_getElem!_range [ha : Inhabited α] {n : ℕ} :
(range n).map (xs[·]!) = xs.take n ++ replicate (n - xs.length) default := by
  by_cases h : n ≤ xs.length
  · simp [Nat.sub_eq_zero_of_le h, map_getElem!_range_of_le_length h]
  · rw [map_getElem!_range_of_length_le # by omega]; simp; omega

theorem foldr_apply {f : α → β → β} {z : β}
(g₁ : β → γ) (g₂ : γ → β) (h : ∀ ⦃x⦄, g₂ (g₁ x) = x) :
xs.foldr f z = g₂ (xs.foldr (λ x acc => g₁ # f x # g₂ acc) (g₁ z)) := by
  induction xs <;> grind

theorem foldl_apply {f : β → α → β} {z : β}
(g₁ : β → γ) (g₂ : γ → β) (h : ∀ ⦃x⦄, g₂ (g₁ x) = x) :
xs.foldl f z = g₂ (xs.foldl (λ acc x => g₁ # f (g₂ acc) x) (g₁ z)) := by
  simp_rw [foldl_eq_foldr_reverse, foldr_apply _ _ h]

@[simp]
theorem take_take_same {n : ℕ} : (xs.take n).take n = xs.take n := by
  rw [take_take]; simp

-- #check 0 #exit

end List

namespace Bit

@[simp]
theorem ofBool_eq_iff {b₁ b₂} : ofBool b₁ = ofBool b₂ ↔ b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> simp

@[simp] theorem ofBool_false : ofBool false = 0 := rfl
@[simp] theorem ofBool_true : ofBool true = 1 := rfl
@[simp] theorem toBool_0 : toBool 0 = false := rfl
@[simp] theorem toBool_1 : toBool 1 = true := rfl

@[simp]
theorem ofBool_eq_zero_iff {b : Bool} : ofBool b = 0 ↔ b = false := by
  cases b <;> simp

@[simp]
theorem ofBool_eq_one_iff {b : Bool} : ofBool b = 1 ↔ b = true := by
  cases b <;> simp

@[simp]
theorem toBool_eq_false_iff {b : Bit} : b.toBool = false ↔ b = 0 := by
  cases b <;> simp

@[simp]
theorem toBool_eq_true_iff {b : Bit} : b.toBool = true ↔ b = 1 := by
  cases b <;> simp

@[simp]
theorem toBool_ofBool {b : Bool} : (ofBool b).toBool = b := by
  cases b <;> rfl

@[simp]
theorem ofBool_toBool {b : Bit} : ofBool b.toBool = b := by
  cases b <;> rfl

-- #check 0 #exit

end Bit

namespace BitVec

variable {w : ℕ}
variable {x y z : BitVec w}

def ofBit (w : ℕ) (b : Bit) : BitVec w :=
  match b with
  | 0 => 0
  | 1 => 1

def lowestBit (x : BitVec w) : Bit :=
  .ofBool # Odd x.toNat

def ofBits (w : ℕ) (bs : List Bit) : BitVec w :=
  bs.foldr (λ bit x => (x <<< 1) ||| ofBit w bit) 0

def toBits (x : BitVec w) : List Bit :=
  List.range w |>.map # λ n => (x >>> n).lowestBit

-----

@[simp]
theorem ofNatLT_eq_ofNatLT_iff {n m hn hm} :
(.ofNatLT n hn : BitVec w) = .ofNatLT m hm ↔ n = m := by
  simp [BitVec.ofNatLT]

@[simp]
theorem lowestBit_ofNat {n} : (BitVec.ofNat w n).lowestBit = .ofBool (Odd (n % 2 ^ w)) := rfl

@[simp]
theorem toBits_zero : (BitVec.ofNat w 0).toBits = .replicate w 0 := by
  simp [toBits]

@[simp]
theorem toBits_nil {n} : (BitVec.ofNat 0 n).toBits = [] := rfl

@[simp]
theorem ofBits_nil : ofBits w [] = BitVec.ofNat w 0 := rfl

attribute [-simp] Bit.ofBool

@[simp] theorem ofBit_zero : ofBit w 0 = 0 := rfl
@[simp] theorem ofBit_one : ofBit w 1 = 1 := rfl

@[simp]
theorem toBits_cons {b} : (cons b x).toBits = x.toBits ++ [.ofBool b] := by
  rcases x with ⟨⟨x, h⟩⟩
  simp [toBits, cons, BitVec.cast, BitVec.ofNatLT, List.range_succ, lowestBit]
  simp [Nat.shiftRight_or_distrib]
  split_ands
  · intro n hn h₁
    obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_lt hn; clear hn
    rw [show n + w + 1 = w + 1 + n by omega] at h₁
    simp [Nat.shiftLeft_add] at h₁
  cases b <;> simp
  simp [Nat.shiftRight_eq_zero _ _ h]

theorem shiftLeft_one_eq_mul_two : x <<< 1 = x * 2 := by
  rw [shiftLeft_eq_mul_twoPow]; congr; simp [twoPow]; clear! w x
  rw [←BitVec.toFin_inj]; simp; ext; simp; rw [Nat.shiftLeft_eq]; simp

theorem mul_two_or_one_eq : x * 2 ||| 1 = x * 2 + 1 := by
  rcases x with ⟨⟨x, h⟩⟩
  rw [←BitVec.toFin_inj]
  simp
  ext
  simp [Fin.val_mul, Fin.val_add]
  cases w <;> simp
  nm w
  nth_rw 1 [Nat.pow_succ]
  rw [Nat.mul_mod_mul_right]
  simp
  by_cases h₁ : x < 2 ^ w
  · rw [Nat.mod_eq_of_lt h₁]
    rw [Nat.mod_eq_of_lt # by omega]
  simp at h₁
  replace h₁ : ∃ y, x = 2 ^ w + y
  · use x % 2 ^ w
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le h₁; clear h₁
    simp; simp [pow_succ, Nat.mul_two] at h
    rw [Nat.mod_eq_of_lt h]
  obtain ⟨x, rfl⟩ := h₁
  simp; simp [pow_succ, Nat.mul_two] at h
  rw [Nat.mod_eq_of_lt h]
  rw [Nat.add_mod, Nat.one_mod_two_pow # by omega]
  by_cases h₁ : w = 0; simp_all
  rw [Nat.add_mul, ←pow_succ]
  simp
  rw [Nat.mod_eq_of_lt]
  omega

theorem foldr_eq_add_ofBits {bs : List Bit} {z : BitVec w} :
bs.foldr (λ bit (x : BitVec w) => (x <<< 1) ||| ofBit w bit) z =
(z <<< bs.length) + ofBits w bs := by
  unfold ofBits
  induction bs generalizing z <;> simp
  nm b bs ih
  rw [ih]; clear ih
  cases b <;> simp [shiftLeft_add]
  generalize z <<< bs.length = n
  generalize bs.foldr _ _ = x
  simp only [shiftLeft_one_eq_mul_two]
  rw [←add_mul]
  rw [show (1#w) = 1 by rfl]
  simp_rw [mul_two_or_one_eq]
  grind

theorem ofBits_snoc_eq_add_ofBits {bs : List Bit} {b : Bit} :
ofBits w (bs ++ [b]) = ofBit _ b <<< bs.length + ofBits _ bs := by
  rw [ofBits]; simp [foldr_eq_add_ofBits]

attribute [-simp] List.getElem!_eq_getElem?_getD

@[simp]
theorem getElem_zero_ofBit {b h} : (ofBit w b)[0]'h = b.toBool := by
  cases b <;> simp [ofBit]

@[simp]
theorem getElem_succ_ofBit {i : ℕ} {b h} : (ofBit w b)[i + 1]'h = false := by
  cases b <;> simp [ofBit]

@[simp]
theorem getElem_ofBits {bs} {i : ℕ} {h} : (ofBits w bs)[i]'h = bs[i]! := by
  rw [ofBits]
  generalize hz : (0 : BitVec w) = z; symm at hz
  trans (z <<< bs.length)[i] || bs[i]!.toBool
  on_goal 2 => simp [hz]
  clear hz
  rw [Bool.eq_iff_iff]
  simp
  induction bs generalizing i z <;> simp
  nm b bs ih
  cases i <;> simp
  nm i
  rw [ih]; clear ih
  grind

theorem foldr_eq_or_ofBits {bs : List Bit} {z : BitVec w} :
bs.foldr (λ bit (x : BitVec w) => (x <<< 1) ||| ofBit w bit) z =
(z <<< bs.length) ||| ofBits w bs := by
  rw [foldr_eq_add_ofBits]
  apply add_eq_or_of_and_eq_zero
  ext i h
  simp
  intro h₁
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h₁
  simp

theorem ofBits_snoc_eq_or_ofBits {bs : List Bit} {b : Bit} :
ofBits w (bs ++ [b]) = ofBit _ b <<< bs.length ||| ofBits _ bs := by
  rw [ofBits]; simp [foldr_eq_or_ofBits]

@[simp]
theorem length_toBits : x.toBits.length = w := by
  simp [toBits]

theorem odd_shiftRight_toNat_iff {i : ℕ} : Odd (x.toNat >>> i) ↔ ∃ (h : i < w), x[i] := by
  rcases x with ⟨⟨x, h⟩⟩
  simp [Nat.shiftRight_eq_div_pow, Nat.testBit_eq_odd]
  intro h₁
  replace h₁ := Nat.pos_of_odd h₁
  simp [Nat.div_pos_iff] at h₁
  replace h₁ := lt_of_le_of_lt h₁ h
  rwa [Nat.pow_lt_pow_iff_right (by simp)] at h₁

theorem lowestBit_shiftRight {i : ℕ} :
(x >>> i).lowestBit = if h : i < w then .ofBool x[i] else 0 := by
  simp [lowestBit, odd_shiftRight_toNat_iff]; split_ifs with h <;> simp [h]

theorem toBits_eq_map_getElem : x.toBits = (List.range w).attach.map
λ ⟨i, h⟩ => .ofBool # x[i]'(by grind) := by
  simp [toBits]
  rw [List.map_eq_map_attach]
  congr
  ext y
  rcases y with ⟨i, h⟩
  simp at h
  simp [lowestBit_shiftRight, h]

@[simp]
theorem getElem_cons_last {b h} : (cons b x)[w] = b := by
  simp [getElem_cons]

@[simp]
theorem ofBits_toBits : ofBits _ x.toBits = x := by
  induction x
  · simp
  clear! w x
  nm w b x ih
  simp
  ext i h
  rw [ofBits_snoc_eq_or_ofBits]
  rw [Bool.eq_iff_iff]
  simp
  by_cases h₁ : i = w
  · subst h₁
    simp
  replace h₁ : i < w; omega
  simp [show ¬(w ≤ i) by omega]
  rw [getElem_cons, dif_neg (by omega)]
  rw [toBits_eq_map_getElem]
  simp
  rw [List.getElem!_eq_getElem (by simpa)]
  simp

@[simp]
theorem toBits_eq_iff : x.toBits = y.toBits ↔ x = y := by
  symm; constructor; tauto; intro h
  replace h := congrArg (ofBits w) h
  simp at h; exact h

@[simp]
theorem list_subset_zero_one {bs : List Bit} : bs ⊆ [0, 1] := by
  intro; simp

@[simp]
theorem w_zero_eq {x : BitVec 0} : x = (BitVec.ofNat 0 0) := by
  ext; omega

theorem toBits_ofBits {bs : List Bit} : (ofBits w bs).toBits =
bs.take w ++ .replicate (w - bs.length) 0 := by
  simp [toBits_eq_map_getElem, List.map_getElem!_range]

theorem toBits_ofBits_of_length_eq {bs : List Bit} (h : bs.length = w) :
(ofBits w bs).toBits = bs := by
  simp [toBits_ofBits, h]

theorem toBits_ofBits_of_length_le {bs : List Bit} (h : bs.length ≤ w) :
(ofBits w bs).toBits = bs ++ .replicate (w - bs.length) 0 := by
  simp [toBits_ofBits, h]

theorem toBits_ofBits_of_le_length {bs : List Bit} (h : w ≤ bs.length) :
(ofBits w bs).toBits = bs.take w := by
  simp [toBits_ofBits, h]

@[simp]
theorem toBits_eq_nil_iff : x.toBits = [] ↔ w = 0 := by
  rw [List.eq_nil_iff_length_eq_zero, length_toBits]

-- #check 0 #exit

end BitVec

namespace UInt8

def ofBit (b : Bit) : UInt8 :=
  match b with
  | 0 => 0
  | 1 => 1

def lowestBit (x : UInt8) : Bit :=
  .ofBool # Odd x.toNat

def ofBits (bs : List Bit) : UInt8 :=
  bs.foldr (λ bit x => (x <<< 1) ||| ofBit bit) 0

def toBits (x : UInt8) : List Bit :=
  List.range 8 |>.map # λ n => (x >>> ofNat n).lowestBit

-----

variable {x y z : UInt8}
variable {bs : List Bit}

attribute [simp] UInt8.toNat_lt_size

@[simp]
theorem mk_eq_mk_iff {x y : BitVec 8} : (⟨x⟩ : UInt8) = ⟨y⟩ ↔ x = y := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; rfl

theorem eq_iff_mk : x = y ↔ x.toBitVec = y.toBitVec := by
  cases x; cases y; simp

@[simp]
theorem ofNatLT_eq_ofNatLT_iff {n m hn hm} : ofNatLT n hn = ofNatLT m hm ↔ n = m := by
  simp_rw [ofNatLT, mk_eq_mk_iff]; simp

attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [-simp] Bit.ofBool

@[simp]
theorem ofBit_eq_mk {b} : ofBit b = ⟨.ofBit _ b⟩ := by
  cases b <;> rfl

@[simp]
theorem lowestBit_mk {x : BitVec 8} : lowestBit ⟨x⟩ = x.lowestBit := rfl

theorem or_eq_mk : x ||| y = ⟨x.toBitVec ||| y.toBitVec⟩ := rfl

@[simp]
theorem ofBits_eq_mk {bs : List Bit} : ofBits bs = ⟨.ofBits _ bs⟩ := by
  simp [eq_iff_mk, ofBits, BitVec.ofBits]
  rw [List.foldr_apply toBitVec ofBitVec]; simp
  rintro ⟨x⟩; simp

@[simp]
theorem toBitVec_eq_iff : x.toBitVec = y.toBitVec ↔ x = y := by
  cases x; cases y; simp

@[simp]
theorem toBits_eq_mk : x.toBits = x.toBitVec.toBits := rfl

end UInt8

namespace ByteArray

def ofBits' (acc : List UInt8) (bs : List Bit) : List UInt8 :=
  if bs = [] then acc else
  match _h : bs.splitAt 8 with
  | (xs, bs') => ofBits' (.ofBits xs :: acc) bs'
termination_by bs.length
decreasing_by have : bs.length ≠ 0; simpa; grind

def ofBits (bs : List Bit) : ByteArray :=
  ⟨⟨ofBits' [] bs |>.reverse⟩⟩

def toBits (bs : ByteArray) : List Bit :=
  bs.1.1.flatMap UInt8.toBits

-----

theorem empty_def : (∅ : ByteArray) = ⟨⟨[]⟩⟩ := rfl

@[simp]
theorem ofBits_nil : ofBits [] = ∅ := by
  ext <;> simp [ofBits, ofBits']

@[simp]
theorem ofBits'_nil {acc} : ofBits' acc [] = acc := by
  simp [ofBits']

@[simp]
theorem ofBits_toBits {bs : ByteArray} : ofBits bs.toBits = bs := by
  rcases bs with ⟨⟨bs⟩⟩
  simp [ofBits, toBits]
  suffices h : ∀ acc, ofBits' acc (bs.flatMap UInt8.toBits) = bs.reverse ++ acc
  · specialize h []
    simp at h
    simp [h]
  intro acc
  induction bs generalizing acc
  · simp
  nm x bs ih
  simp
  unfold ofBits'
  simp [ih]

@[simp] theorem toBits_empty : empty.toBits = [] := rfl

theorem ofBits'_of_length_le_8 {bs₁ : List UInt8} {bs₂ : List Bit}
(h₁ : bs₂ ≠ []) (h₂ : bs₂.length ≤ 8) : ofBits' bs₁ bs₂ = .ofBits bs₂ :: bs₁ := by
  unfold ofBits'; simp [h₁]; rw [List.take_eq_self_of_le h₂, List.drop_eq_nil_of_le h₂]; simp

theorem ofBits'_eq_append {bs₁ bs₂} : ofBits' bs₁ bs₂ = ofBits' [] bs₂ ++ bs₁ := by
  generalize hn : bs₂.length = n
  induction n using Nat.strong_induction_on generalizing bs₁ bs₂
  nm n ih
  cases n
  · simp at hn
    simp [hn]
  nm n
  have h₁ : bs₂ ≠ []; grind
  nth_rw 2 [ofBits']
  rw [ofBits']
  simp [h₁]
  nth_rw 2 [@ih (bs₂.drop 8).length (by grind) _ (bs₂.drop 8) rfl]
  rw [@ih (bs₂.drop 8).length (by grind) _ (bs₂.drop 8) rfl]
  simp

@[simp]
theorem toBits_ofBits {bs : List Bit} :
(ofBits bs).toBits = bs ++ .replicate ((8 - bs.length % 8) % 8) 0 := by
  generalize hn : bs.length = n
  induction n using Nat.strong_induction_on generalizing bs
  nm n ih; subst hn
  by_cases h₁ : bs = []
  · simp [h₁]
  by_cases h₂ : bs.length = 8
  · simp [h₂]
    simp [ofBits, toBits, ofBits'_of_length_le_8 h₁ # by omega]
    rw [BitVec.toBits_ofBits_of_length_eq h₂]
  by_cases h₃ : bs.length < 8
  · clear ih
    rw [Nat.mod_eq_of_lt h₃]
    simp [ofBits, toBits, ofBits'_of_length_le_8 h₁ # le_of_lt h₃]
    rw [BitVec.toBits_ofBits_of_length_le # by omega]
    simp
    rw [Nat.mod_eq_of_lt]
    have h₄ : bs.length ≠ 0; grind
    omega
  replace h₂ : 8 < bs.length; omega
  clear h₃
  simp [ofBits, toBits]
  unfold ofBits'
  simp [h₁]
  generalize h₃ : bs.drop 8 = bs'
  have h₄ : bs'.length < bs.length
  · subst h₃; simp; grind
  specialize @ih _ h₄ bs' rfl
  have h₅ : bs'.length % 8 = bs.length % 8
  · subst h₃
    simp
    omega
  rw [h₅] at ih
  have h₆ := bs.take_append_drop 8
  rw [h₃] at h₆
  nth_rw 2 [←h₆]
  rw [List.append_assoc]
  rw [←ih]; clear ih
  rw [ofBits'_eq_append]
  simp
  congr 1
  rw [BitVec.toBits_ofBits]
  simp; omega

-- #check 0 #exit

end ByteArray

structure Serializer where
  bytes : ByteArray
  curByte : UInt8
  bitMask : UInt8
deriving DecidableEq

namespace Serializer

abbrev Ser := StateM Serializer

def empty : Serializer where
  bytes := ∅
  curByte := 0
  bitMask := 1

instance : EmptyCollection Serializer := ⟨empty⟩
theorem empty_def : (∅ : Serializer) = empty := rfl

def flush' : Ser Unit := modify # λ s =>
  { bytes := s.bytes.push s.curByte
    curByte := 0
    bitMask := 1
  }

def flush : Ser Unit := do
  bif (←get).bitMask != 0 then pure () else flush'

def writeBit' (b : Bit) : Ser Unit := modify # λ s =>
  { bytes := s.bytes
    curByte := match b with
      | .B₀ => s.curByte
      | .B₁ => s.curByte ||| s.bitMask
    bitMask := s.bitMask <<< 1
  }

def writeBit (b : Bit) : Ser Unit := do
  writeBit' b; flush

def writeBits (bs : List Bit) : Ser Unit :=
  bs.forM writeBit

def getOutput : Ser ByteArray := do
  flush; gets (·.bytes)

def ofBits (bs : List Bit) : Serializer :=
  StateT.run (m := Id) (writeBits bs) ∅ |>.2

-- #check 0 #exit

-----

variable {α β γ : Type}
variable {s : Serializer}

@[simp]
theorem writeBits_nil : writeBits [] = pure () := rfl

@[simp]
theorem getOutput_empty : getOutput.run ∅ = (∅, ∅) := rfl

@[simp low]
theorem writeBits_empty {bs} : (writeBits bs).run ∅ = ((), ofBits bs) := rfl

@[simp]
theorem ofBits_nil : ofBits [] = ∅ := rfl

@[simp]
theorem flush_empty : flush.run ∅ = ((), ∅) := rfl

@[simp]
theorem writeBits_cons {b bs} : writeBits (b :: bs) = (do writeBit b; writeBits bs) := rfl

@[simp]
theorem writeBits_append {bs₁ bs₂} :
writeBits (bs₁ ++ bs₂) = (do writeBits bs₁; writeBits bs₂) := by
  simp [writeBits]

@[simp]
theorem flush_flush' : flush.run (flush'.run s).2 = flush'.run s := rfl

@[simp]
theorem flush_flush : flush.run (flush.run s).2 = flush.run s := by
  nth_rw 2 [flush]; simp
  split_ifs with h <;> simp
  simp [flush, h]

@[simp]
theorem flush_ofBits {bs} : flush.run (ofBits bs) = ((), ofBits bs) := by
  induction bs using List.reverseRecOn; simp
  unfold ofBits; simp [writeBit, writeBit']; rfl

@[simp]
theorem getOutput_ofBits {bs} : getOutput.run (ofBits bs) = (ofBits bs |>.bytes, ofBits bs) := by
  simp [getOutput]

@[simp]
theorem bytes_empty : (∅ : Serializer).bytes = ∅ := rfl

@[simp]
theorem ofBits_append {bs₁ bs₂} :
ofBits (bs₁ ++ bs₂) = (writeBits bs₂ |>.run (ofBits bs₁) |>.2) := by
  unfold ofBits; simp

-- @[simp]
-- theorem bytes_ofBits {bs : List Bit} : (ofBits bs).bytes = .ofBits bs := by
--   generalize hn : bs.length = n
--   induction n using Nat.strong_induction_on generalizing bs
--   nm n ih
--   subst hn
--   by_cases h : bs.length < 8
--   ·
--     sorry
--   sorry