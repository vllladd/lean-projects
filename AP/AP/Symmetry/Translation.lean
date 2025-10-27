import AP.AP.Symmetry.Basic

namespace AP

def translate (dif : PointZ) : sys.Symmetry := mkSym
  { toFun := (· + dif)
  , invFun := (· - dif)
  , left_inv := λ _ => by simp
  , right_inv := λ _ => by simp
  }

theorem translate.cnd_initial_fs_iff {dif s} :
sys.Initial ((translate dif).fs s) ↔ sys.Initial s := by
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

theorem translate.cnd_tr_eq {dif s p} : sys.tr s p =
(sys.tr ((translate dif).fs s) ((translate dif).ft p)).map (translate dif).fs' := by
  ext s'
  simp [translate, sys, State.move]
  split_ifs with ht
  · simp [State.aMove]; simp [State.ext_iff]
  · simp [State.dMove]; simp [State.ext_iff]

@[simp]
instance {dif} : (translate dif).WF where
  initial_fs_iff := translate.cnd_initial_fs_iff
  tr_eq := translate.cnd_tr_eq

@[simp] instance {dif} : BasicSym # translate dif where
  exi_mkSym := by simp [translate]