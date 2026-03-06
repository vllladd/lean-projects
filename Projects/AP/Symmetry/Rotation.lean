import Projects.AP.Symmetry.Translation

namespace AP

def rotRight : sys.Symmetry := mkSym
  { toFun := λ p => ⟨-p.y, p.x⟩
  , invFun := λ p => ⟨p.y, -p.x⟩
  , left_inv := λ _ => by simp
  , right_inv := λ _ => by simp
  }

theorem rotRight.cnd_initial_fs_iff {s} :
sys.Initial (rotRight.fs s) ↔ sys.Initial s := by
  simp [rotRight, aPos₀_mkSymFsAux_eq_ite]
  split_ifs with h
  · simp [State.aPos₀, h]
    have h₁ : initState s.pw none.getd ≠ s
    · intro h₁
      rw [←h₁] at h
      simp at h
    rw [Option.getd] at h₁
    simp [h₁]
    apply ne_of_congr (·.hist.length)
    simp [h]
  simp [State.ext_iff]
  constructor
  · rintro ⟨h₁, ⟨h₂, h₅⟩, h₃, h₄⟩
    symm at h₄
    simp at h₄
    simp [h₁, h₃]
    obtain ⟨p, h₄, h₆, h₇⟩ := h₄
    rw [Point.ext_iff]
    simp [h₂, h₅, h₄]
    rw [Point.ext_iff]
    simp [h₆, h₇]
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    simp [h₁, h₂, h₃]
    symm; simp
    use s.aPos₀
    simp [←h₂, h₄]

theorem rotRight.cnd_tr_eq {s p} : sys.tr s p =
(sys.tr (rotRight.fs s) (rotRight.ft p)).map rotRight.fs' := by
  ext s'
  simp [rotRight, sys, State.move]
  split_ifs with ht
  · simp [State.aMove]; simp [State.ext_iff]
    intro h₁ h₂ h₃ h₄ h₅
    constructor
    · rintro ⟨H₁, H₂, H₃⟩
      refine' ⟨_, _, _⟩
      · intro H₄
        contrapose! H₁
        ext <;> assumption
      · intro p₁ hp₁ hp₂
        contrapose! H₂
        convert hp₁
        ext <;> simp_all
      · simp [Point.dist] at H₃ ⊢
        rw [add_comm]
        rw [Int.add_neg_eq_sub]
        rw [abs_sub_comm]
        exact H₃.symm
    · rintro ⟨H₁, H₂, H₃⟩
      refine' ⟨_, _, _⟩
      · rintro rfl
        simp at H₁
      · intro H₄
        specialize H₂ _ H₄
        simp at H₂
      · simp [Point.dist] at H₃ ⊢
        rw [add_comm] at H₃
        rw [Int.add_neg_eq_sub] at H₃
        rw [abs_sub_comm] at H₃
        exact H₃.symm
  · simp [State.dMove]; simp [State.ext_iff]
    intro h₁ h₂ h₃ h₄ h₅
    constructor
    · rintro ⟨H₁, H₂⟩
      constructor
      · intro H₃ H₄
        apply H₁; ext <;> assumption
      · intro p₁ hp₁ hp₂ hp₃
        apply H₂
        convert hp₁
        ext <;> simp_all
    · rintro ⟨H₁, H₂⟩
      constructor
      · rintro rfl
        simp at H₁
      · intro H₃
        specialize H₂ _ H₃
        simp at H₂

@[simp]
instance : rotRight.WF where
  initial_fs_iff := rotRight.cnd_initial_fs_iff
  tr_eq := rotRight.cnd_tr_eq

def rotLeft : sys.Symmetry :=
  rotRight⁻¹

@[simp] instance : rotLeft.WF := by unfold rotLeft; infer_instance

def rot180 : sys.Symmetry :=
  rotRight ^ 2

@[simp] instance : rot180.WF := by unfold rot180; infer_instance

@[simp] theorem rotRight_mul_rotRight : rotRight * rotRight = rot180 := rfl
@[simp] theorem rotRight_mul_rotLeft : rotRight * rotLeft = 1 := by simp [rotLeft]
@[simp] theorem rotLeft_mul_rotRight : rotLeft * rotRight = 1 := by simp [rotLeft]

theorem inv_rot180 : rot180⁻¹ = rot180 := by
  rw [rot180, pow_two, mul_inv_rev, rotRight]
  ext:2 <;> simp; ext:1 <;> simp

instance : rot180.SelfInverse where
  inv_eq_self := inv_rot180

@[simp]
theorem rotLeft_mul_rotLeft : rotLeft * rotLeft = rot180 := by
  rw [rotLeft, ←mul_inv_rev, ←pow_two, ←rot180]; simp

@[simp] theorem rotRight_pow_two : rotRight ^ 2 = rot180 := rotRight_mul_rotRight
@[simp] theorem rotLeft_pow_two : rotLeft ^ 2 = rot180 := rotLeft_mul_rotLeft

@[simp]
theorem rotRight_pow_three : rotRight ^ 3 = rotLeft := by
  rw [pow_succ, rotRight_pow_two, ←rotLeft_mul_rotLeft, mul_assoc]; simp

@[simp]
theorem rotLeft_pow_three : rotLeft ^ 3 = rotRight := by
  rw [pow_succ, rotLeft_pow_two, ←rotRight_mul_rotRight, mul_assoc]; simp

@[simp]
theorem rot180_mul_rot180 : rot180 * rot180 = 1 := by
  nth_rw 1 [←inv_rot180, inv_mul_cancel]

@[simp]
theorem rot180_pow_two : rot180 ^ 2 = 1 :=
  rot180_mul_rot180

@[simp]
theorem rotRight_pow_four : rotRight ^ 4 = 1 := by
  rw [show 4 = 2 + 2 by rfl, pow_add]; simp

@[simp]
theorem rotLeft_pow_four : rotLeft ^ 4 = 1 := by
  rw [show 4 = 2 + 2 by rfl, pow_add]; simp

@[simp] theorem inv_rotRight : rotRight⁻¹ = rotLeft := rfl
@[simp] theorem inv_rotLeft : rotLeft⁻¹ = rotRight := rfl

@[simp] instance : BasicSym rotRight where
  exi_mkSym := by simp [rotRight]

@[simp] instance : BasicSym rotLeft := by unfold rotLeft; infer_instance
@[simp] instance : BasicSym rot180 := by unfold rot180; infer_instance

@[simp] theorem rotRight_ft_x {p} : (rotRight.ft p).x = -p.y := rfl
@[simp] theorem rotRight_ft_y {p} : (rotRight.ft p).y = p.x := rfl
@[simp] theorem rotRight_ft'_x {p} : (rotRight.ft' p).x = p.y := rfl
@[simp] theorem rotRight_ft'_y {p} : (rotRight.ft' p).y = -p.x := rfl

@[simp] theorem rotLeft_ft_x {p} : (rotLeft.ft p).x = p.y := rfl
@[simp] theorem rotLeft_ft_y {p} : (rotLeft.ft p).y = -p.x := rfl
@[simp] theorem rotLeft_ft'_x {p} : (rotLeft.ft' p).x = -p.y := rfl
@[simp] theorem rotLeft_ft'_y {p} : (rotLeft.ft' p).y = p.x := rfl

@[simp] theorem rot180_ft_x {p} : (rot180.ft p).x = -p.x := rfl
@[simp] theorem rot180_ft_y {p} : (rot180.ft p).y = -p.y := rfl
@[simp] theorem rot180_ft'_x {p} : (rot180.ft' p).x = -p.x := rfl
@[simp] theorem rot180_ft'_y {p} : (rot180.ft' p).y = -p.y := rfl

@[simp]
theorem rotRight_dist_rotRight {p₁ p₂} :
(rotRight.ft p₁).dist (rotRight.ft p₂) = p₁.dist p₂ := by
  simp [rotRight, Point.dist, neg_add_eq_sub, abs_sub_comm, max_comm]

@[simp]
theorem rotRight_dist_rotRight' {p₁ p₂} :
(rotRight.ft' p₁).dist (rotRight.ft' p₂) = p₁.dist p₂ := by
  simp [rotRight, Point.dist, neg_add_eq_sub, abs_sub_comm, max_comm]

@[simp]
theorem rotLeft_dist_rotLeft {p₁ p₂} :
(rotLeft.ft p₁).dist (rotLeft.ft p₂) = p₁.dist p₂ :=
  rotRight_dist_rotRight'

@[simp]
theorem rotLeft_dist_rotLeft' {p₁ p₂} :
(rotLeft.ft' p₁).dist (rotLeft.ft' p₂) = p₁.dist p₂ :=
  rotRight_dist_rotRight

@[simp]
theorem rot180_dist_rot180 {p₁ p₂} :
(rot180.ft p₁).dist (rot180.ft p₂) = p₁.dist p₂ :=
  rotRight_dist_rotRight.trans rotRight_dist_rotRight

@[simp]
theorem rot180_dist_rot180' {p₁ p₂} :
(rot180.ft' p₁).dist (rot180.ft' p₂) = p₁.dist p₂ :=
  rotRight_dist_rotRight'.trans rotRight_dist_rotRight'

@[simp] theorem rotRight_ft_mk {x y} : rotRight.ft ⟨x, y⟩ = ⟨-y, x⟩ := rfl
@[simp] theorem rotRight_ft'_mk {x y} : rotRight.ft' ⟨x, y⟩ = ⟨y, -x⟩ := rfl
@[simp] theorem rotLeft_ft_mk {x y} : rotLeft.ft ⟨x, y⟩ = ⟨y, -x⟩ := rfl
@[simp] theorem rotLeft_ft'_mk {x y} : rotLeft.ft' ⟨x, y⟩ = ⟨-y, x⟩ := rfl
@[simp] theorem rot180_ft_mk {x y} : rot180.ft ⟨x, y⟩ = ⟨-x, -y⟩ := rfl

@[simp]
theorem rotRight_mul_rot180 : rotRight * rot180 = rotLeft := by
  rw [←rotLeft_mul_rotLeft, ←mul_assoc]; simp

@[simp]
theorem rot180_mul_rotRight : rot180 * rotRight = rotLeft := by
  rw [←rotLeft_mul_rotLeft, mul_assoc]; simp

@[simp]
theorem rotLeft_mul_rot180 : rotLeft * rot180 = rotRight := by
  rw [←rotRight_mul_rotRight, ←mul_assoc]; simp

@[simp]
theorem rot180_mul_rotLeft : rot180 * rotLeft = rotRight := by
  rw [←rotRight_mul_rotRight, mul_assoc]; simp