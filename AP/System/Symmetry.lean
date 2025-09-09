import AP.System.Invariant

namespace Equiv

variable {α β γ : Type*}
variable {e : α ≃ β} {e₁ : β ≃ γ} {e₂ : α ≃ β}

def comp (e₁ : β ≃ γ) (e₂ : α ≃ β) : α ≃ γ where
  toFun := e₁ ∘ e₂
  invFun := e₂.symm ∘ e₁.symm
  left_inv := by intros x; simp
  right_inv := by intros x; simp

@[simp]
theorem coe_toFun_comp : (e₁.comp e₂ : _ → _) = e₁ ∘ e₂ := rfl

@[simp]
theorem symm_comp : (e₁.comp e₂).symm = e₂.symm.comp e₁.symm := rfl

-- #check 0 #exit

end Equiv

namespace System

universe u
variable {S T : Type u} {sys : System S T}

@[ext]
structure Symmetry (sys : System S T) : Type u where
  fs : S → S
  fs' : S → S
  ft : T → T
  ft' : T → T

namespace Symmetry

variable {sym sym₁ sym₂ : sys.Symmetry}

class WF (sym : sys.Symmetry) : Prop where
  h_fs : BijectiveOn sys.WF sys.WF sym.fs sym.fs'
  h_ft : BijectiveOn sys.WFTrans sys.WFTrans sym.ft sym.ft'
  tr_eq : ∀ {s t} [sys.WF s], sys.tr s t = (sys.tr (sym.fs s) (sym.ft t)).map sym.fs'
  tr_eq' : ∀ {s t} [sys.WF s], sys.tr s t = (sys.tr (sym.fs' s) (sym.ft' t)).map sym.fs

def one : sys.Symmetry := ⟨id, id, id, id⟩

instance : One sys.Symmetry := ⟨one⟩
theorem one_def : (1 : sys.Symmetry) = one := rfl

instance : Inhabited sys.Symmetry := ⟨one⟩
theorem default_eq : (default : sys.Symmetry) = 1 := rfl

@[simp]
instance : (1 : sys.Symmetry).WF := by
  rw [one_def, one]; constructor <;> simp

@[simp]
instance : (default : sys.Symmetry).WF := by
  rw [default_eq]; infer_instance

instance {s} [H : sym.WF] [hs : sys.WF s] : sys.WF (sym.fs s) :=
  H.h_fs.cnd_right hs

instance {s} [H : sym.WF] [hs : sys.WF s] : sys.WF (sym.fs' s) :=
  H.h_fs.cnd_left hs

instance {t} [H : sym.WF] [ht : sys.WFTrans t] : sys.WFTrans (sym.ft t) :=
  H.h_ft.cnd_right ht

instance {t} [H : sym.WF] [ht : sys.WFTrans t] : sys.WFTrans (sym.ft' t) :=
  H.h_ft.cnd_left ht

@[simp]
theorem fs'_fs {s} [H : sym.WF] [hs : sys.WF s] : sym.fs' (sym.fs s) = s :=
  H.h_fs.cancel_left hs

@[simp]
theorem fs_fs' {s} [H : sym.WF] [hs : sys.WF s] : sym.fs (sym.fs' s) = s :=
  H.h_fs.cancel_right hs

@[simp]
theorem ft'_ft {t} [H : sym.WF] [ht : sys.WFTrans t] : sym.ft' (sym.ft t) = t :=
  H.h_ft.cancel_left ht

@[simp]
theorem ft_ft' {t} [H : sym.WF] [ht : sys.WFTrans t] : sym.ft (sym.ft' t) = t :=
  H.h_ft.cancel_right ht

def tr_fs {s t} [H : sym.WF] [hs : sys.WF s] :
sys.tr (sym.fs s) t = (sys.tr s (sym.ft' t)).map sym.fs := by
  nth_rw 1 [H.tr_eq']; ext s'; simp

def tr_fs' {s t} [H : sym.WF] [hs : sys.WF s] :
sys.tr (sym.fs' s) t = (sys.tr s (sym.ft t)).map sym.fs' := by
  nth_rw 1 [H.tr_eq]; ext s'; simp

def tr_ft {s t} [H : sym.WF] [hs : sys.WF s] :
sys.tr s (sym.ft t) = (sys.tr (sym.fs' s) t).map sym.fs := by
  nth_rw 2 [H.tr_eq]; ext s'; simp; constructor
  · intro h; use s'; have hs' := wf_of_tr h; simpa
  · rintro ⟨s₁, h₁, h₂⟩; have hs₁ := wf_of_tr h₁; simp at h₂; simpa [←h₂]

def tr_ft' {s t} [H : sym.WF] [hs : sys.WF s] :
sys.tr s (sym.ft' t) = (sys.tr (sym.fs s) t).map sym.fs' := by
  nth_rw 2 [H.tr_eq']; ext s'; simp; constructor
  · intro h; use s', h; have h₁ := wf_of_tr h; simp
  · rintro ⟨s₁, h₁, h₂⟩; have h₃ := wf_of_tr h₁; simp at h₂; simpa [←h₂]

theorem validTr_fs_of {s t} [H : sym.WF] [hs : sys.WF s]
(h : sys.validTr s (sym.ft' t)) : sys.validTr (sym.fs s) t := by
  obtain ⟨s', h⟩ := h; simp [tr_ft'] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_fs'_of {s t} [H : sym.WF] [hs : sys.WF s]
(h : sys.validTr s (sym.ft t)) : sys.validTr (sym.fs' s) t := by
  obtain ⟨s', h⟩ := h; simp [tr_ft] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_ft_of {s t} [H : sym.WF] [hs : sys.WF s]
(h : sys.validTr (sym.fs' s) t) : sys.validTr s (sym.ft t) := by
  obtain ⟨s', h⟩ := h; simp [tr_fs'] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_ft'_of {s t} [H : sym.WF] [hs : sys.WF s]
(h : sys.validTr (sym.fs s) t) : sys.validTr s (sym.ft' t) := by
  obtain ⟨s', h⟩ := h; simp [tr_fs] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_fs {s t} [H : sym.WF] [hs : sys.WF s] :
sys.validTr (sym.fs s) t ↔ sys.validTr s (sym.ft' t) :=
  ⟨validTr_ft'_of, validTr_fs_of⟩

theorem validTr_fs' {s t} [H : sym.WF] [hs : sys.WF s] :
sys.validTr (sym.fs' s) t ↔ sys.validTr s (sym.ft t) :=
  ⟨validTr_ft_of, validTr_fs'_of⟩

theorem validTr_ft {s t} [H : sym.WF] [hs : sys.WF s] :
sys.validTr s (sym.ft t) ↔ sys.validTr (sym.fs' s) t :=
  ⟨validTr_fs'_of, validTr_ft_of⟩

theorem validTr_ft' {s t} [H : sym.WF] [hs : sys.WF s] :
sys.validTr s (sym.ft' t) ↔ sys.validTr (sym.fs s) t :=
  ⟨validTr_fs_of, validTr_ft'_of⟩

@[simp]
theorem hasTr_fs {s} [H : sym.WF] [hs : sys.WF s] :
sys.hasTr (sym.fs s) ↔ sys.hasTr s := by
  constructor <;> rintro ⟨t, h⟩
  · use sym.ft' t; simpa [validTr_ft']
  · use sym.ft t; simpa [validTr_ft]

@[simp]
theorem hasTr_fs' {s} [H : sym.WF] [hs : sys.WF s] :
sys.hasTr (sym.fs' s) ↔ sys.hasTr s := by
  constructor <;> rintro ⟨t, h⟩
  · use sym.ft t; simpa [validTr_ft]
  · use sym.ft' t; simpa [validTr_ft']

example {s t} [H : sym.WF] [hs : sys.WF s] :
sys.validTr (sym.fs s) t ↔ sys.validTr s (sym.ft' t) := by
  symm; constructor
  · exact fun a ↦ validTr_fs_of a
  · exact fun a ↦ validTr_ft'_of a

@[simp]
def simFn (sym : sys.Symmetry) (f : S → T) (s : S) : T :=
  sym.ft # f # sym.fs' s

instance {f} [H : sym.WF] [hf : sys.SimFn f] : sys.SimFn (sym.simFn f) := by
  rw [sys.simFn_def]; intro s hs h; simp; apply hf.1 at h; apply validTr_ft_of
  have h₁ : sys.hasTr (sym.fs' s); simp; exact ⟨_, h⟩; exact hf.1 h₁

def inv (sym : sys.Symmetry) : sys.Symmetry where
  fs := sym.fs'
  fs' := sym.fs
  ft' := sym.ft
  ft := sym.ft'

instance : Inv sys.Symmetry := ⟨.inv⟩
theorem inv_def : sym⁻¹ = sym.inv := rfl

@[simp]
protected theorem inv_inv : sym⁻¹⁻¹ = sym := by ext <;> rfl

instance [H : sym.WF] : sym⁻¹.WF where
  h_fs := H.h_fs.symm
  h_ft := H.h_ft.symm
  tr_eq := WF.tr_eq'
  tr_eq' := WF.tr_eq

@[simp]
theorem wf_inv_iff : sym⁻¹.WF ↔ sym.WF := by
  symm; constructor <;> intro h; infer_instance
  rw [←sym.inv_inv]; infer_instance

def mul (sym₁ sym₂ : sys.Symmetry) : sys.Symmetry where
  fs := sym₁.fs ∘ sym₂.fs
  fs' := sym₂.fs' ∘ sym₁.fs'
  ft := sym₁.ft ∘ sym₂.ft
  ft' := sym₂.ft' ∘ sym₁.ft'

instance : Mul sys.Symmetry := ⟨mul⟩
theorem mul_def : sym₁ * sym₂ = sym₁.mul sym₂ := rfl

@[simp]
instance [H₁ : sym₁.WF] [H₂ : sym₂.WF] : (sym₁ * sym₂).WF := by
  rw [mul_def, mul]; constructor <;> dsimp
  · constructor; have ⟨e₁, h₁, h₂⟩ := H₁.h_fs; have ⟨e₂, h₃, h₄⟩ := H₂.h_fs
    use e₁.comp e₂; constructor <;> intro s hs <;> simp
    rw [h₃ hs]; apply h₁; rw [h₂ hs]; apply h₄
  · constructor; have ⟨e₁, h₁, h₂⟩ := H₁.h_ft; have ⟨e₂, h₃, h₄⟩ := H₂.h_ft
    use e₁.comp e₂; constructor <;> intro s hs <;> simp
    rw [h₃ hs]; apply h₁; rw [h₂ hs]; apply h₄
  · intro s t hs; ext s'; simp; constructor
    · intro h₁; have hs' := wf_of_tr h₁; use sym₁.fs # sym₂.fs s'
      have ht := wfTrans_of_tr h₁; simp [tr_fs]; use s'
    · rintro ⟨s', h₁, rfl⟩; have hs₁ := wf_of_tr h₁; simp [tr_ft] at h₁
      obtain ⟨s', h₁, rfl⟩ := h₁; have hs' := wf_of_tr h₁; simpa
  · intro s t hs; ext s'; simp; constructor
    · intro h₁; have hs' := wf_of_tr h₁; use sym₂.fs' # sym₁.fs' s'
      have ht := wfTrans_of_tr h₁; simp [tr_fs']; use s'
    · rintro ⟨s', h₁, rfl⟩; have hs₁ := wf_of_tr h₁; simp [tr_ft'] at h₁
      obtain ⟨s', h₁, rfl⟩ := h₁; have hs' := wf_of_tr h₁; simpa

def npow (n : ℕ) (sym : sys.Symmetry) : sys.Symmetry :=
  (· * sym)^[n] 1

protected theorem one_mul : 1 * sym = sym := rfl
protected theorem mul_one : sym * 1 = sym := rfl
protected theorem mul_assoc {s₁ s₂ s₃ : sys.Symmetry} : s₁ * s₂ * s₃ = s₁ * (s₂ * s₃) := rfl

instance : Monoid sys.Symmetry where
  one_mul := λ _ => Symmetry.one_mul
  mul_one := λ _ => Symmetry.mul_one
  mul_assoc := λ _ _ _ => Symmetry.mul_assoc
  npow := npow
  npow_succ := by intros; simp_rw [npow, Function.iterate_succ']; simp

def zpow (z : ℤ) (sym : sys.Symmetry) : sys.Symmetry :=
  match z with
  | .ofNat n => sym ^ n
  | .negSucc n => sym⁻¹ ^ (n + 1)

protected theorem inv_one : (1 : sys.Symmetry)⁻¹ = 1 := rfl
protected theorem mul_inv_rev : (sym₁ * sym₂)⁻¹ = sym₂⁻¹ * sym₁⁻¹ := rfl

#check 0 #exit

protected theorem inv_mul_cancel : sym * sym⁻¹ = 1 := by
  ext
  · nm s
    simp [inv_def, mul_def, one_def, inv, mul, one]

#check 0 #exit

instance : Group sys.Symmetry where
  inv_mul_cancel := by

#check 0 #exit

protected theorem inv_eq_of_mul (h : sym₁ * sym₂ = 1) : sym₁⁻¹ = sym₂ := by
  apply congrArg (· * sym₂⁻¹) at h
  simp [mul_assoc] at h

#check 0 #exit

theorem inv_npow {n} : sym⁻¹ ^ n = (sym ^ n)⁻¹ := by
  induction n; rfl; nm n ih; simp [pow_succ]
  rw [ih]; clear ih; induction n; rfl; nm n ih
  simp [pow_succ, Symmetry.mul_inv_rev]; rw [mul_assoc, ih]

instance : DivInvMonoid sys.Symmetry where
  zpow := zpow
  zpow_succ' := Monoid.npow_succ
  zpow_neg' := λ _ _ => inv_npow

instance : DivisionMonoid sys.Symmetry where
  inv_inv := λ _ => Symmetry.inv_inv
  mul_inv_rev := λ _ _ => Symmetry.mul_inv_rev
  inv_eq_of_mul := by
  -- inv_mul := by
  --   sorry

#check 0 #exit

-- instance : InvOneClass sys.Symmetry where
--   inv_one := Symmetry.inv_one

example : sym ^ (-1 : ℤ) = sym⁻¹ := by
  rw [zpow_neg]