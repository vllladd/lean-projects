import AP.AP.Symmetry.Basic

namespace AP

def translate (offset : PointZ) : sys.Symmetry := mkSym
  { toFun := (· + offset)
  , invFun := (· - offset)
  , left_inv := λ _ => by simp
  , right_inv := λ _ => by simp
  }

theorem translate.cnd_initial_fs_iff {offset s} :
sys.Initial ((translate offset).fs s) ↔ sys.Initial s := by
  simp [translate, aPos₀_mkSymFsAux_eq_ite]
  split_ifs with h
  · simp [State.aPos₀, h]
    have h₁ : initState s.pw none.iget ≠ s
    · intro h₁
      rw [←h₁] at h
      simp at h
    simp [h₁]
    apply ne_of_congr (·.hist.length)
    simp [h]
  simp [State.ext_iff]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    simp [h₁, h₂, h₃]
    symm at h₄; simp at h₄
    simp [h₂, h₄]
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    simp [h₁, h₂, h₃]
    symm; simp
    rw [←h₂, h₄]

theorem translate.cnd_tr_eq {offset s p} : sys.tr s p =
(sys.tr ((translate offset).fs s) ((translate offset).ft p)).map (translate offset).fs' := by
  ext s'
  simp [translate, sys, State.move]
  split_ifs with ht
  · simp [State.aMove]; simp [State.ext_iff]
  · simp [State.dMove]; simp [State.ext_iff]

@[simp]
instance {offset} : (translate offset).WF where
  initial_fs_iff := translate.cnd_initial_fs_iff
  tr_eq := translate.cnd_tr_eq

@[simp]
instance {offset} : BasicSym # translate offset where
  exi_mkSym := by simp [translate]

@[simp] theorem translate_ft_x {p offset} : (translate offset |>.ft p).x = p.x + offset.x := rfl
@[simp] theorem translate_ft_y {p offset} : (translate offset |>.ft p).y = p.y + offset.y := rfl
@[simp] theorem translate_ft'_x {p offset} : (translate offset |>.ft' p).x = p.x - offset.x := rfl
@[simp] theorem translate_ft'_y {p offset} : (translate offset |>.ft' p).y = p.y - offset.y := rfl

@[simp] theorem translate_ft_mk {offset x y} :
(translate offset).ft ⟨x, y⟩ = ⟨x + offset.x, y + offset.y⟩ := rfl

@[simp] theorem translate_ft_mk' {offset x y} :
(translate offset).ft' ⟨x, y⟩ = ⟨x - offset.x, y - offset.y⟩ := rfl

@[simp]
theorem translate_dist_translate {offset p₁ p₂} :
(translate offset |>.ft p₁).dist (translate offset |>.ft p₂) = p₁.dist p₂ := by
  simp [translate]

@[simp]
theorem translate_dist_translate' {offset p₁ p₂} :
(translate offset |>.ft' p₁).dist (translate offset |>.ft' p₂) = p₁.dist p₂ := by
  simp [translate]