import AP.System.Symmetry.Raw

namespace System

universe u
variable {S T : Type u} {sys : System S T}

structure Symmetry (sys : System S T) : Type u extends Raw sys where
  wf : toRaw.WF

namespace Symmetry

variable {sym sym₁ sym₂ sym₃ : Symmetry sys}

@[ext]
theorem ext (h : sym₁.toRaw = sym₂.toRaw) : sym₁ = sym₂ := by
  cases sym₁; cases sym₂; simp_all

def one : Symmetry sys :=
  ⟨Raw.one, inferInstance⟩

instance : Inhabited (Symmetry sys) := ⟨one⟩
theorem default_eq : (default : Symmetry sys) = one := rfl

instance : sym.toRaw.WF := sym.wf

theorem tr_fs {s t} [hs : sys.WF s] :
sys.tr (sym.fs s) t = (sys.tr s (sym.ft' t)).map sym.fs := Raw.tr_fs

theorem tr_fs' {s t} [hs : sys.WF s] :
sys.tr (sym.fs' s) t = (sys.tr s (sym.ft t)).map sym.fs' := Raw.tr_fs'

theorem tr_ft {s t} [hs : sys.WF s] :
sys.tr s (sym.ft t) = (sys.tr (sym.fs' s) t).map sym.fs := Raw.tr_ft

theorem tr_ft' {s t} [hs : sys.WF s] :
sys.tr s (sym.ft' t) = (sys.tr (sym.fs s) t).map sym.fs' := Raw.tr_ft'

theorem validTr_fs_of {s t} [hs : sys.WF s]
(h : sys.validTr s (sym.ft' t)) : sys.validTr (sym.fs s) t := Raw.validTr_fs_of h

theorem validTr_fs'_of {s t} [hs : sys.WF s]
(h : sys.validTr s (sym.ft t)) : sys.validTr (sym.fs' s) t := Raw.validTr_fs'_of h

theorem validTr_ft_of {s t} [hs : sys.WF s]
(h : sys.validTr (sym.fs' s) t) : sys.validTr s (sym.ft t) := Raw.validTr_ft_of h

theorem validTr_ft'_of {s t} [hs : sys.WF s]
(h : sys.validTr (sym.fs s) t) : sys.validTr s (sym.ft' t) := Raw.validTr_ft'_of h

theorem validTr_fs {s t} [hs : sys.WF s] :
sys.validTr (sym.fs s) t ↔ sys.validTr s (sym.ft' t) := Raw.validTr_fs

theorem validTr_fs' {s t} [hs : sys.WF s] :
sys.validTr (sym.fs' s) t ↔ sys.validTr s (sym.ft t) := Raw.validTr_fs'

theorem validTr_ft {s t} [hs : sys.WF s] :
sys.validTr s (sym.ft t) ↔ sys.validTr (sym.fs' s) t := Raw.validTr_ft

theorem validTr_ft' {s t} [hs : sys.WF s] :
sys.validTr s (sym.ft' t) ↔ sys.validTr (sym.fs s) t :=
  ⟨validTr_fs_of, validTr_ft'_of⟩

def simFn (sym : Symmetry sys) (f : S → T) (s : S) : T :=
  sym.toRaw.simFn f s

instance {f} [hf : sys.SimFn f] : sys.SimFn (sym.simFn f) := by
  unfold simFn; infer_instance

def inv (sym : Symmetry sys) : Symmetry sys :=
  ⟨sym.toRaw.inv, inferInstance⟩

@[simp]
theorem inv_inv : sym.inv.inv = sym := ext Raw.inv_inv

def mul (sym₁ sym₂ : Symmetry sys) : Symmetry sys :=
  ⟨sym₁.toRaw.mul sym₂.toRaw, inferInstance⟩

def npow (n : ℕ) (sym : Symmetry sys) : Symmetry sys :=
  ⟨sym.toRaw.npow n, inferInstance⟩

def zpow (z : ℤ) (sym : Symmetry sys) : Symmetry sys :=
  ⟨sym.toRaw.zpow z, inferInstance⟩

def Equiv (sym₁ sym₂ : Symmetry sys) : Prop :=
  sym₁.toRaw.Equiv sym₂.toRaw

@[simp, refl]
theorem Equiv.refl : sym.Equiv sym := Raw.Equiv.refl

@[symm]
theorem Equiv.symm (h : sym₁.Equiv sym₂) : sym₂.Equiv sym₁ :=
  Raw.Equiv.symm h

@[trans]
theorem Equiv.trans (h₁ : sym₁.Equiv sym₂) (h₂ : sym₂.Equiv sym₃) : sym₁.Equiv sym₃ :=
  Raw.Equiv.trans h₁ h₂

theorem Equiv.iseqv : Equivalence # Equiv (sys := sys) where
  refl := λ _ => refl
  symm := symm
  trans := trans

instance setoid : Setoid (Symmetry sys) where
  r := Equiv
  iseqv := Equiv.iseqv

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