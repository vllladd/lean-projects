import AP.System.Symmetry.Raw0

namespace System.Symmetry

universe u
variable {S T : Type u} {sys : System S T}

structure Raw (sys : System S T) : Type u extends Raw₀ sys where
  wf : toRaw₀.WF

namespace Raw

variable {sym sym₁ sym₂ sym₃ : Raw sys}

@[ext]
theorem ext (h : sym₁.toRaw₀ = sym₂.toRaw₀) : sym₁ = sym₂ := by
  cases sym₁; cases sym₂; simp_all

def one : Raw sys :=
  ⟨Raw₀.one, inferInstance⟩

instance : Inhabited (Raw sys) := ⟨one⟩
theorem default_eq : (default : Raw sys) = one := rfl

instance : sym.toRaw₀.WF := sym.wf

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

def Equiv (sym₁ sym₂ : Raw sys) : Prop :=
  sym₁.toRaw₀.Equiv sym₂.toRaw₀

@[simp, refl]
theorem Equiv.refl : sym.Equiv sym := Raw₀.Equiv.refl

@[symm]
theorem Equiv.symm (h : sym₁.Equiv sym₂) : sym₂.Equiv sym₁ :=
  Raw₀.Equiv.symm h

@[trans]
theorem Equiv.trans (h₁ : sym₁.Equiv sym₂) (h₂ : sym₂.Equiv sym₃) : sym₁.Equiv sym₃ :=
  Raw₀.Equiv.trans h₁ h₂

theorem Equiv.iseqv : Equivalence # Equiv (sys := sys) where
  refl := λ _ => refl
  symm := symm
  trans := trans

instance setoid : Setoid (Raw sys) where
  r := Equiv
  iseqv := Equiv.iseqv