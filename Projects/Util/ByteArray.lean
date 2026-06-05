import Projects.Util.UInt8

namespace ByteArray

def getD (bs : ByteArray) (z : UInt8) (i : ℕ) : UInt8 :=
  if h : i < bs.size then bs[i] else z

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

attribute [-simp] List.getElem!_eq_getElem?_getD

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

theorem ofBits'_of_length_le {bs₁ : List UInt8} {bs₂ : List Bit}
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
    simp [ofBits, toBits, ofBits'_of_length_le h₁ # by omega]
    rw [BitVec.toBits_ofBits_of_length_eq h₂]
  by_cases h₃ : bs.length < 8
  · clear ih
    rw [Nat.mod_eq_of_lt h₃]
    simp [ofBits, toBits, ofBits'_of_length_le h₁ # le_of_lt h₃]
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

theorem ofBits_of_length_le {bs : List Bit}
(h₁ : bs ≠ []) (h₂ : bs.length ≤ 8) : ofBits bs = ⟨⟨[.ofBits bs]⟩⟩ := by
  rw [ofBits, ofBits'_of_length_le h₁ h₂]; rfl

@[simp]
theorem size_mk {bs} : (⟨bs⟩ : ByteArray).size = bs.size := rfl

@[simp]
theorem get!_mk {bs i} : (⟨bs⟩ : ByteArray).get! i = bs[i]! := rfl