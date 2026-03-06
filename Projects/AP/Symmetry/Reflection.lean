import Projects.AP.Symmetry.Rotation

namespace AP

def flipH : sys.Symmetry := mkSym
  { toFun := λ p => ⟨-p.x, p.y⟩
  , invFun := λ p => ⟨-p.x, p.y⟩
  , left_inv := λ _ => by simp
  , right_inv := λ _ => by simp
  }

def flipV : sys.Symmetry := mkSym
  { toFun := λ p => ⟨p.x, -p.y⟩
  , invFun := λ p => ⟨p.x, -p.y⟩
  , left_inv := λ _ => by simp
  , right_inv := λ _ => by simp
  }

theorem flipH.cnd_initial_fs_iff {s} :
sys.Initial (flipH.fs s) ↔ sys.Initial s := by
  simp [flipH, aPos₀_mkSymFsAux_eq_ite]
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

theorem flipV.cnd_initial_fs_iff {s} :
sys.Initial (flipV.fs s) ↔ sys.Initial s := by
  simp [flipV, aPos₀_mkSymFsAux_eq_ite]
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

theorem flipH.cnd_tr_eq {s p} : sys.tr s p =
(sys.tr (flipH.fs s) (flipH.ft p)).map flipH.fs' := by
  ext s'
  simp [flipH, sys, State.move]
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
        rwa [abs_sub_comm]
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
        rwa [abs_sub_comm] at H₃
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

theorem flipV.cnd_tr_eq {s p} : sys.tr s p =
(sys.tr (flipV.fs s) (flipV.ft p)).map flipV.fs' := by
  ext s'
  simp [flipV, sys, State.move]
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
        nth_rw 2 [abs_sub_comm]
        exact H₃
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
        nth_rw 2 [abs_sub_comm]
        exact H₃
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
instance : flipH.WF where
  initial_fs_iff := flipH.cnd_initial_fs_iff
  tr_eq := flipH.cnd_tr_eq

@[simp]
instance : flipV.WF where
  initial_fs_iff := flipV.cnd_initial_fs_iff
  tr_eq := flipV.cnd_tr_eq

@[simp] theorem flipH_ft_x {p} : (flipH.ft p).x = -p.x := rfl
@[simp] theorem flipH_ft_y {p} : (flipH.ft p).y = p.y := rfl
@[simp] theorem flipH_ft'_x {p} : (flipH.ft' p).x = -p.x := rfl
@[simp] theorem flipH_ft'_y {p} : (flipH.ft' p).y = p.y := rfl

@[simp] theorem flipV_ft_x {p} : (flipV.ft p).x = p.x := rfl
@[simp] theorem flipV_ft_y {p} : (flipV.ft p).y = -p.y := rfl
@[simp] theorem flipV_ft'_x {p} : (flipV.ft' p).x = p.x := rfl
@[simp] theorem flipV_ft'_y {p} : (flipV.ft' p).y = -p.y := rfl

@[simp]
theorem flipH_dist_flipH {p₁ p₂} :
(flipH.ft p₁).dist (flipH.ft p₂) = p₁.dist p₂ := by
  simp [Point.dist, neg_add_eq_sub, abs_sub_comm]

@[simp]
theorem flipH_dist_flipH' {p₁ p₂} :
(flipH.ft' p₁).dist (flipH.ft' p₂) = p₁.dist p₂ := by
  simp [Point.dist, neg_add_eq_sub, abs_sub_comm]

@[simp]
theorem flipV_dist_flipV {p₁ p₂} :
(flipV.ft p₁).dist (flipV.ft p₂) = p₁.dist p₂ := by
  simp [Point.dist, neg_add_eq_sub, abs_sub_comm]

@[simp]
theorem flipV_dist_flipV' {p₁ p₂} :
(flipV.ft' p₁).dist (flipV.ft' p₂) = p₁.dist p₂ := by
  simp [Point.dist, neg_add_eq_sub, abs_sub_comm]

@[simp] instance : BasicSym flipH where
  exi_mkSym := by simp [flipH]

@[simp] instance : BasicSym flipV where
  exi_mkSym := by simp [flipV]

theorem inv_flipH : flipH⁻¹ = flipH := rfl
theorem inv_flipV : flipV⁻¹ = flipV := rfl

instance : flipH.SelfInverse where
  inv_eq_self := inv_flipH

instance : flipV.SelfInverse where
  inv_eq_self := inv_flipV

@[simp] theorem flipH_ft_mk {x y} : flipH.ft ⟨x, y⟩ = ⟨-x, y⟩ := rfl
@[simp] theorem flipV_ft_mk {x y} : flipV.ft ⟨x, y⟩ = ⟨x, -y⟩ := rfl

@[simp]
theorem flipH_mul_flipV : flipH * flipV = rot180 := by
  rw [ext_iff_of_basicSym]; intro p; rfl

@[simp]
theorem flipV_mul_flipH : flipV * flipH = rot180 := by
  rw [ext_iff_of_basicSym]; intro p; rfl

@[simp]
theorem flipH_mul_rot180 : flipH * rot180 = flipV := by
  rw [ext_iff_of_basicSym]; intro p; ext <;> simp

@[simp]
theorem rot180_mul_flipH : rot180 * flipH = flipV := by
  rw [ext_iff_of_basicSym]; intro p; ext <;> simp

@[simp]
theorem flipV_mul_rot180 : flipV * rot180 = flipH := by
  rw [ext_iff_of_basicSym]; intro p; ext <;> simp

@[simp]
theorem rot180_mul_flipV : rot180 * flipV = flipH := by
  rw [ext_iff_of_basicSym]; intro p; ext <;> simp

@[simp] theorem flipH_ft_flipV_ft {p} : flipH.ft (flipV.ft p) = rot180.ft p := by cases p; simp
@[simp] theorem flipV_ft_flipH_ft {p} : flipV.ft (flipH.ft p) = rot180.ft p := by cases p; simp
@[simp] theorem flipH_ft_rot180_ft {p} : flipH.ft (rot180.ft p) = flipV.ft p := by cases p; simp
@[simp] theorem rot180_ft_flipH_ft {p} : rot180.ft (flipH.ft p) = flipV.ft p := by cases p; simp
@[simp] theorem flipV_ft_rot180_ft {p} : flipV.ft (rot180.ft p) = flipH.ft p := by cases p; simp
@[simp] theorem rot180_ft_flipV_ft {p} : rot180.ft (flipV.ft p) = flipH.ft p := by cases p; simp