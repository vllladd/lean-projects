import AP.System.Invariant

namespace System.Symmetry

universe u
variable {S T : Type u} {sys : System S T}

@[ext]
structure Raw (sys : System S T) : Type u where
  fs : S → S
  fs' : S → S
  ft : T → T
  ft' : T → T

namespace Raw

class WF (sym : Raw sys) : Prop where
  h_fs : ∀ {s}, sys.WF (sym.fs s) ↔ sys.WF s -- derivable?
  h_fs' : ∀ {s}, sys.WF (sym.fs' s) ↔ sys.WF s -- derivable?
  h_ft : ∀ {t}, sys.WFTrans (sym.ft t) ↔ sys.WFTrans t -- derivable?
  h_ft' : ∀ {t}, sys.WFTrans (sym.ft' t) ↔ sys.WFTrans t -- derivable?
  fs_fs' : Inverse sym.fs sym.fs'
  ft_ft' : Inverse sym.ft sym.ft'
  tr_eq : ∀ {s t}, sys.tr s t = (sys.tr (sym.fs s) (sym.ft t)).map sym.fs'
  tr_eq' : ∀ {s t}, sys.tr s t = (sys.tr (sym.fs' s) (sym.ft' t)).map sym.fs -- derivable?

def one : Raw sys where
  fs := id
  fs' := id
  ft := id
  ft' := id

instance : Inhabited (Raw sys) := ⟨one⟩
theorem default_eq : (default : Raw sys) = one := rfl

@[simp]
def simFn (sym : Raw sys) (f : S → T) (s : S) : T :=
  sym.ft # f # sym.fs' s

def inv (sym : Raw sys) : Raw sys where
  fs := sym.fs'
  fs' := sym.fs
  ft' := sym.ft
  ft := sym.ft'

def mul (sym₁ sym₂ : Raw sys) : Raw sys where
  fs := sym₁.fs ∘ sym₂.fs
  fs' := sym₂.fs' ∘ sym₁.fs'
  ft := sym₁.ft ∘ sym₂.ft
  ft' := sym₂.ft' ∘ sym₁.ft'

def div (sym₁ sym₂ : Raw sys) : Raw sys :=
  sym₁.mul sym₂.inv

def npow (n : ℕ) (sym : Raw sys) : Raw sys :=
  (·.mul sym)^[n] one

def zpow (z : ℤ) (sym : Raw sys) : Raw sys :=
  match z with
  | .ofNat n => sym.npow n
  | .negSucc n => sym.inv.npow (n + 1)

-----

variable {sym sym₁ sym₂ sym₃ : Raw sys}
variable [wf : sym.WF] [wf₁ : sym₁.WF] [wf₂ : sym₂.WF] [wf₃ : sym₃.WF]

@[simp] theorem wf_fs_iff {s} : sys.WF (sym.fs s) ↔ sys.WF s := by rw [wf.h_fs]
@[simp] theorem wf_fs'_iff {s} : sys.WF (sym.fs' s) ↔ sys.WF s := by rw [wf.h_fs']
@[simp] theorem wf_ft_iff {t} : sys.WFTrans (sym.ft t) ↔ sys.WFTrans t := by rw [wf.h_ft]
@[simp] theorem wf_ft'_iff {t} : sys.WFTrans (sym.ft' t) ↔ sys.WFTrans t := by rw [wf.h_ft']

instance {s} [hs : sys.WF s] : sys.WF (sym.fs s) := by simpa
instance {s} [hs : sys.WF s] : sys.WF (sym.fs' s) := by simpa
instance {t} [ht : sys.WFTrans t] : sys.WFTrans (sym.ft t) := by simpa
instance {t} [ht : sys.WFTrans t] : sys.WFTrans (sym.ft' t) := by simpa

@[simp] theorem fs_fs' {s} : sym.fs (sym.fs' s) = s := wf.fs_fs'.fg
@[simp] theorem fs'_fs {s} : sym.fs' (sym.fs s) = s := wf.fs_fs'.gf
@[simp] theorem ft_ft' {s} : sym.ft (sym.ft' s) = s := wf.ft_ft'.fg
@[simp] theorem ft'_ft {s} : sym.ft' (sym.ft s) = s := wf.ft_ft'.gf

theorem tr_fs {s t} : sys.tr (sym.fs s) t = (sys.tr s (sym.ft' t)).map sym.fs := by
  nth_rw 1 [wf.tr_eq']; ext s'; simp

theorem tr_fs' {s t} : sys.tr (sym.fs' s) t = (sys.tr s (sym.ft t)).map sym.fs' := by
  nth_rw 1 [wf.tr_eq]; ext s'; simp

theorem tr_ft {s t} : sys.tr s (sym.ft t) = (sys.tr (sym.fs' s) t).map sym.fs := by
  nth_rw 2 [wf.tr_eq]; ext s'; simp

theorem tr_ft' {s t} : sys.tr s (sym.ft' t) = (sys.tr (sym.fs s) t).map sym.fs' := by
  nth_rw 2 [wf.tr_eq']; ext s'; simp

theorem validTr_fs_of {s t}
(h : sys.validTr s (sym.ft' t)) : sys.validTr (sym.fs s) t := by
  obtain ⟨s', h⟩ := h; simp [tr_ft'] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_fs'_of {s t}
(h : sys.validTr s (sym.ft t)) : sys.validTr (sym.fs' s) t := by
  obtain ⟨s', h⟩ := h; simp [tr_ft] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_ft_of {s t}
(h : sys.validTr (sym.fs' s) t) : sys.validTr s (sym.ft t) := by
  obtain ⟨s', h⟩ := h; simp [tr_fs'] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_ft'_of {s t}
(h : sys.validTr (sym.fs s) t) : sys.validTr s (sym.ft' t) := by
  obtain ⟨s', h⟩ := h; simp [tr_fs] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_fs {s t} : sys.validTr (sym.fs s) t ↔ sys.validTr s (sym.ft' t) :=
  ⟨validTr_ft'_of, validTr_fs_of⟩

theorem validTr_fs' {s t} : sys.validTr (sym.fs' s) t ↔ sys.validTr s (sym.ft t) :=
  ⟨validTr_ft_of, validTr_fs'_of⟩

theorem validTr_ft {s t} : sys.validTr s (sym.ft t) ↔ sys.validTr (sym.fs' s) t :=
  ⟨validTr_fs'_of, validTr_ft_of⟩

theorem validTr_ft' {s t} : sys.validTr s (sym.ft' t) ↔ sys.validTr (sym.fs s) t :=
  ⟨validTr_fs_of, validTr_ft'_of⟩

@[simp]
theorem hasTr_fs {s} : sys.hasTr (sym.fs s) ↔ sys.hasTr s := by
  constructor <;> rintro ⟨t, h⟩
  · use sym.ft' t; simpa [validTr_ft']
  · use sym.ft t; simpa [validTr_ft]

@[simp]
theorem hasTr_fs' {s} : sys.hasTr (sym.fs' s) ↔ sys.hasTr s := by
  constructor <;> rintro ⟨t, h⟩
  · use sym.ft t; simpa [validTr_ft]
  · use sym.ft' t; simpa [validTr_ft']

instance : (Raw.one : Raw sys).WF := by
  unfold Raw.one; constructor <;> simp

instance {f} [hf : sys.SimFn f] : sys.SimFn (sym.simFn f) := by
  rw [sys.simFn_def]; intro s hs h; simp; apply hf.1 at h; apply validTr_ft_of
  have h₁ : sys.hasTr (sym.fs' s); simp; exact ⟨_, h⟩; exact hf.1 h₁

instance : sym.inv.WF where
  h_fs := wf.h_fs'
  h_fs' := wf.h_fs
  h_ft := wf.h_ft'
  h_ft' := wf.h_ft
  fs_fs' := wf.fs_fs'.symm
  ft_ft' := wf.ft_ft'.symm
  tr_eq := wf.tr_eq'
  tr_eq' := wf.tr_eq

omit wf in @[simp]
theorem inv_inv : sym.inv.inv = sym := by ext <;> rfl

instance : (sym₁.mul sym₂).WF where
  h_fs := by simp [mul]
  h_fs' := by simp [mul]
  h_ft := by simp [mul]
  h_ft' := by simp [mul]
  fs_fs' := by constructor <;> simp [mul]
  ft_ft' := by constructor <;> simp [mul]
  tr_eq := by
    intro s t; ext s'; simp [mul]; constructor
    · intro h₁; use sym₁.fs # sym₂.fs s'; simp [tr_fs]; use s'
    · rintro ⟨s', h₁, rfl⟩; simp [tr_ft] at h₁; obtain ⟨s', h₁, rfl⟩ := h₁; simpa
  tr_eq' := by
    intro s t; ext s'; simp [mul]; constructor
    · intro h₁; use sym₂.fs' # sym₁.fs' s'; simp [tr_fs']; use s'
    · rintro ⟨s', h₁, rfl⟩; simp [tr_ft'] at h₁; obtain ⟨s', h₁, rfl⟩ := h₁; simpa

instance : (sym₁.div sym₂).WF := by
  unfold div; infer_instance

instance {n} : (sym.npow n).WF := by
  simp [npow]; induction n; simp; infer_instance; nm n ih
  rw [Function.iterate_succ']; simp; infer_instance

instance {z} : (sym.zpow z).WF := by
  simp [zpow]; split <;> infer_instance

@[simp]
protected theorem inv_mul_cancel : sym.inv.mul sym = one := by
  simp [inv, mul, one]; constructor <;> ext <;> simp

omit wf₁ @[simp]
protected theorem inv_eq_of_mul (h : sym₁.mul sym₂ = one) : sym₁.inv = sym₂ := by
  simp [inv, mul, one] at h ⊢; rcases h with ⟨h₁, h₂, h₃, h₄⟩; ext <;> dsimp
  · nm s; apply congrArg sym₂.fs ∘ congrArg (· s) at h₂; simp at h₂; exact h₂
  · nm s; apply congrArg (· # sym₂.fs' s) at h₁; simp at h₁; exact h₁
  · nm t; apply congrArg sym₂.ft ∘ congrArg (· t) at h₄; simp at h₄; exact h₄
  · nm t; apply congrArg (· # sym₂.ft' t) at h₃; simp at h₃; exact h₃