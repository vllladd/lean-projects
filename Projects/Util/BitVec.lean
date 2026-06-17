import Projects.Util.Bit
import Projects.Util.Array

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

@[simp]
theorem ofBits_singleton {b} : ofBits w [b] = ofBit w b := by
  simp [ofBits]