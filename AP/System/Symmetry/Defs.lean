import AP.System.Symmetry.Raw

namespace System

universe u
variable {S T : Type u} {sys : System S T}

def Symmetry (sys : System S T) : Type u :=
  Quotient # Symmetry.Raw.setoid (sys := sys)

namespace Symmetry

variable {sym sym₁ sym₂ sym₃ : Symmetry sys}

def one : Symmetry sys :=
  Quotient.mk' Raw.one

instance : One (Symmetry sys) := ⟨one⟩
theorem one_def : (1 : Symmetry sys) = one := rfl

instance : Inhabited (Symmetry sys) := ⟨1⟩
theorem default_eq : (default : Symmetry sys) = 1 := rfl

#check 0 #exit

@[simp] theorem fs'_fs {s} [hs : sys.WF s] : sym.fs' (sym.fs s) = s := Raw₀.fs'_fs
@[simp] theorem fs_fs' {s} [hs : sys.WF s] : sym.fs (sym.fs' s) = s := Raw₀.fs_fs'
@[simp] theorem ft'_ft {t} [ht : sys.WFTrans t] : sym.ft' (sym.ft t) = t := Raw₀.ft'_ft
@[simp] theorem ft_ft' {t} [ht : sys.WFTrans t] : sym.ft (sym.ft' t) = t := Raw₀.ft_ft'

theorem tr_fs {s t} [hs : sys.WF s] :
sys.tr (sym.fs s) t = (sys.tr s (sym.ft' t)).map sym.fs := Raw₀.tr_fs

theorem tr_fs' {s t} [hs : sys.WF s] :
sys.tr (sym.fs' s) t = (sys.tr s (sym.ft t)).map sym.fs' := Raw₀.tr_fs'

theorem tr_ft {s t} [hs : sys.WF s] :
sys.tr s (sym.ft t) = (sys.tr (sym.fs' s) t).map sym.fs := Raw₀.tr_ft

theorem tr_ft' {s t} [hs : sys.WF s] :
sys.tr s (sym.ft' t) = (sys.tr (sym.fs s) t).map sym.fs' := Raw₀.tr_ft'

theorem validTr_fs_of {s t} [hs : sys.WF s]
(h : sys.validTr s (sym.ft' t)) : sys.validTr (sym.fs s) t := Raw₀.validTr_fs_of h

theorem validTr_fs'_of {s t} [hs : sys.WF s]
(h : sys.validTr s (sym.ft t)) : sys.validTr (sym.fs' s) t := Raw₀.validTr_fs'_of h

theorem validTr_ft_of {s t} [hs : sys.WF s]
(h : sys.validTr (sym.fs' s) t) : sys.validTr s (sym.ft t) := Raw₀.validTr_ft_of h

theorem validTr_ft'_of {s t} [hs : sys.WF s]
(h : sys.validTr (sym.fs s) t) : sys.validTr s (sym.ft' t) := Raw₀.validTr_ft'_of h

theorem validTr_fs {s t} [hs : sys.WF s] :
sys.validTr (sym.fs s) t ↔ sys.validTr s (sym.ft' t) := Raw₀.validTr_fs

theorem validTr_fs' {s t} [hs : sys.WF s] :
sys.validTr (sym.fs' s) t ↔ sys.validTr s (sym.ft t) := Raw₀.validTr_fs'

theorem validTr_ft {s t} [hs : sys.WF s] :
sys.validTr s (sym.ft t) ↔ sys.validTr (sym.fs' s) t := Raw₀.validTr_ft

theorem validTr_ft' {s t} [hs : sys.WF s] :
sys.validTr s (sym.ft' t) ↔ sys.validTr (sym.fs s) t :=
  ⟨validTr_fs_of, validTr_ft'_of⟩

@[simp] theorem hasTr_fs {s} [hs : sys.WF s] :
sys.hasTr (sym.fs s) ↔ sys.hasTr s := Raw₀.hasTr_fs

@[simp]
theorem hasTr_fs' {s} [hs : sys.WF s] :
sys.hasTr (sym.fs' s) ↔ sys.hasTr s := Raw₀.hasTr_fs'

@[simp]
def simFn (sym : Raw sys) (f : S → T) (s : S) : T :=
  sym.toRaw₀.simFn f s

instance {f} [hf : sys.SimFn f] : sys.SimFn (sym.simFn f) := by
  unfold simFn; infer_instance

def inv (sym : Raw sys) : Raw sys :=
  ⟨sym.toRaw₀.inv, inferInstance⟩

@[simp]
theorem inv_inv : sym.inv.inv = sym := ext Raw₀.inv_inv

def mul (sym₁ sym₂ : Raw sys) : Raw sys :=
  ⟨sym₁.toRaw₀.mul sym₂.toRaw₀, inferInstance⟩

def npow (n : ℕ) (sym : Raw sys) : Raw sys :=
  ⟨sym.toRaw₀.npow n, inferInstance⟩

def zpow (z : ℤ) (sym : Raw sys) : Raw sys :=
  ⟨sym.toRaw₀.zpow z, inferInstance⟩

#check 0 #exit

instance : Monoid sys.Symmetry where
  one_mul := λ _ => rfl
  mul_one := λ _ => rfl
  mul_assoc := λ _ _ _ => rfl
  npow := npow
  npow_succ := by intros; simp_rw [npow, Function.iterate_succ']; simp

protected theorem inv_one : (1 : sys.Symmetry)⁻¹ = 1 := rfl
protected theorem mul_inv_rev : (sym₁ * sym₂)⁻¹ = sym₂⁻¹ * sym₁⁻¹ := rfl

#check 0 #exit

protected theorem inv_mul_cancel : sym * sym⁻¹ = 1 := by
  ext
  · nm s
    simp [inv_def, mul_def, one_def, inv, mul, one]
    simp

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