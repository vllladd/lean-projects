import AP.System.Invariant

namespace System.Symmetry

universe u
variable {S T : Type u} {sys : System S T}

@[ext]
structure Raw₀ (sys : System S T) : Type u where
  fs : S → S
  fs' : S → S
  ft : T → T
  ft' : T → T

namespace Raw₀

class WF (sym : Raw₀ sys) : Prop where
  h_fs : StrictBijectiveOn sys.WF sys.WF sym.fs sym.fs'
  h_ft : StrictBijectiveOn sys.WFTrans sys.WFTrans sym.ft sym.ft'
  tr_eq : ∀ {s t} [sys.WF s], sys.tr s t = (sys.tr (sym.fs s) (sym.ft t)).map sym.fs'
  tr_eq' : ∀ {s t} [sys.WF s], sys.tr s t = (sys.tr (sym.fs' s) (sym.ft' t)).map sym.fs

def one : Raw₀ sys where
  fs := id
  fs' := id
  ft := id
  ft' := id

instance : Inhabited (Raw₀ sys) := ⟨one⟩
theorem default_eq : (default : Raw₀ sys) = one := rfl

@[simp]
def simFn (sym : Raw₀ sys) (f : S → T) (s : S) : T :=
  sym.ft # f # sym.fs' s

def inv (sym : Raw₀ sys) : Raw₀ sys where
  fs := sym.fs'
  fs' := sym.fs
  ft' := sym.ft
  ft := sym.ft'

def mul (sym₁ sym₂ : Raw₀ sys) : Raw₀ sys where
  fs := sym₁.fs ∘ sym₂.fs
  fs' := sym₂.fs' ∘ sym₁.fs'
  ft := sym₁.ft ∘ sym₂.ft
  ft' := sym₂.ft' ∘ sym₁.ft'

def npow (n : ℕ) (sym : Raw₀ sys) : Raw₀ sys :=
  (·.mul sym)^[n] one

def zpow (z : ℤ) (sym : Raw₀ sys) : Raw₀ sys :=
  match z with
  | .ofNat n => sym.npow n
  | .negSucc n => sym.inv.npow (n + 1)

-----

variable {sym sym₁ sym₂ sym₃ : Raw₀ sys}
variable [wf : sym.WF] [wf₁ : sym₁.WF] [wf₂ : sym₂.WF] [wf₃ : sym₃.WF]

instance {s} [hs : sys.WF s] : sys.WF (sym.fs s) :=
  wf.h_fs.cnd_right hs

instance {s} [hs : sys.WF s] : sys.WF (sym.fs' s) :=
  wf.h_fs.cnd_left hs

instance {t} [ht : sys.WFTrans t] : sys.WFTrans (sym.ft t) :=
  wf.h_ft.cnd_right ht

instance {t} [ht : sys.WFTrans t] : sys.WFTrans (sym.ft' t) :=
  wf.h_ft.cnd_left ht

include wf

@[simp]
theorem fs'_fs {s} [hs : sys.WF s] : sym.fs' (sym.fs s) = s :=
  wf.h_fs.cancel_left hs

@[simp]
theorem fs_fs' {s} [hs : sys.WF s] : sym.fs (sym.fs' s) = s :=
  wf.h_fs.cancel_right hs

@[simp]
theorem ft'_ft {t} [ht : sys.WFTrans t] : sym.ft' (sym.ft t) = t :=
  wf.h_ft.cancel_left ht

@[simp]
theorem ft_ft' {t} [ht : sys.WFTrans t] : sym.ft (sym.ft' t) = t :=
  wf.h_ft.cancel_right ht

theorem tr_fs {s t} [hs : sys.WF s] :
sys.tr (sym.fs s) t = (sys.tr s (sym.ft' t)).map sym.fs := by
  nth_rw 1 [wf.tr_eq']; ext s'; simp

theorem tr_fs' {s t} [hs : sys.WF s] :
sys.tr (sym.fs' s) t = (sys.tr s (sym.ft t)).map sym.fs' := by
  nth_rw 1 [wf.tr_eq]; ext s'; simp

theorem tr_ft {s t} [hs : sys.WF s] :
sys.tr s (sym.ft t) = (sys.tr (sym.fs' s) t).map sym.fs := by
  nth_rw 2 [wf.tr_eq]; ext s'; simp; constructor
  · intro h; use s'; have hs' := wf_of_tr h; simpa
  · rintro ⟨s₁, h₁, h₂⟩; have hs₁ := wf_of_tr h₁; simp at h₂; simpa [←h₂]

theorem tr_ft' {s t} [hs : sys.WF s] :
sys.tr s (sym.ft' t) = (sys.tr (sym.fs s) t).map sym.fs' := by
  nth_rw 2 [wf.tr_eq']; ext s'; simp; constructor
  · intro h; use s', h; have h₁ := wf_of_tr h; simp
  · rintro ⟨s₁, h₁, h₂⟩; have h₃ := wf_of_tr h₁; simp at h₂; simpa [←h₂]

theorem validTr_fs_of {s t} [hs : sys.WF s]
(h : sys.validTr s (sym.ft' t)) : sys.validTr (sym.fs s) t := by
  obtain ⟨s', h⟩ := h; simp [tr_ft'] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_fs'_of {s t} [hs : sys.WF s]
(h : sys.validTr s (sym.ft t)) : sys.validTr (sym.fs' s) t := by
  obtain ⟨s', h⟩ := h; simp [tr_ft] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_ft_of {s t} [hs : sys.WF s]
(h : sys.validTr (sym.fs' s) t) : sys.validTr s (sym.ft t) := by
  obtain ⟨s', h⟩ := h; simp [tr_fs'] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_ft'_of {s t} [hs : sys.WF s]
(h : sys.validTr (sym.fs s) t) : sys.validTr s (sym.ft' t) := by
  obtain ⟨s', h⟩ := h; simp [tr_fs] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_fs {s t} [hs : sys.WF s] :
sys.validTr (sym.fs s) t ↔ sys.validTr s (sym.ft' t) :=
  ⟨validTr_ft'_of, validTr_fs_of⟩

theorem validTr_fs' {s t} [hs : sys.WF s] :
sys.validTr (sym.fs' s) t ↔ sys.validTr s (sym.ft t) :=
  ⟨validTr_ft_of, validTr_fs'_of⟩

theorem validTr_ft {s t} [hs : sys.WF s] :
sys.validTr s (sym.ft t) ↔ sys.validTr (sym.fs' s) t :=
  ⟨validTr_fs'_of, validTr_ft_of⟩

theorem validTr_ft' {s t} [hs : sys.WF s] :
sys.validTr s (sym.ft' t) ↔ sys.validTr (sym.fs s) t :=
  ⟨validTr_fs_of, validTr_ft'_of⟩

@[simp]
theorem hasTr_fs {s} [hs : sys.WF s] :
sys.hasTr (sym.fs s) ↔ sys.hasTr s := by
  constructor <;> rintro ⟨t, h⟩
  · use sym.ft' t; simpa [validTr_ft']
  · use sym.ft t; simpa [validTr_ft]

@[simp]
theorem hasTr_fs' {s} [hs : sys.WF s] :
sys.hasTr (sym.fs' s) ↔ sys.hasTr s := by
  constructor <;> rintro ⟨t, h⟩
  · use sym.ft t; simpa [validTr_ft]
  · use sym.ft' t; simpa [validTr_ft']

omit wf

instance : (Raw₀.one : Raw₀ sys).WF := by
  unfold Raw₀.one; constructor <;> simp

instance {f} [hf : sys.SimFn f] : sys.SimFn (sym.simFn f) := by
  rw [sys.simFn_def]; intro s hs h; simp; apply hf.1 at h; apply validTr_ft_of
  have h₁ : sys.hasTr (sym.fs' s); simp; exact ⟨_, h⟩; exact hf.1 h₁

include wf₁ in
instance [wf : sym.WF] : sym.inv.WF where
  h_fs := wf.h_fs.symm
  h_ft := wf.h_ft.symm
  tr_eq := wf.tr_eq'
  tr_eq' := wf.tr_eq

@[simp]
theorem inv_inv : sym.inv.inv = sym := by ext <;> rfl

include wf₁ wf₂ in
instance : (sym₁.mul sym₂).WF where
  h_fs := by
    simp [Raw₀.mul]; constructor
    · have ⟨e₁, h₁, h₂⟩ := wf₁.h_fs.toBijectiveOn
      have ⟨e₂, h₃, h₄⟩ := wf₂.h_fs.toBijectiveOn
      use e₁.comp e₂; constructor <;> intro s hs <;> simp
      rw [h₃ hs]; apply h₁; rw [h₂ hs]; apply h₄
    · intro x h; apply wf₂.h_fs.cnd_of_right
      exact wf₁.h_fs.cnd_of_right h
    · intro x h; apply wf₁.h_fs.cnd_of_left
      exact wf₂.h_fs.cnd_of_left h
  h_ft := by
    simp [Raw₀.mul]; constructor
    · have ⟨e₁, h₁, h₂⟩ := wf₁.h_ft.toBijectiveOn
      have ⟨e₂, h₃, h₄⟩ := wf₂.h_ft.toBijectiveOn
      use e₁.comp e₂; constructor <;> intro s hs <;> simp
      rw [h₃ hs]; apply h₁; rw [h₂ hs]; apply h₄
    · intro x h; apply wf₂.h_ft.cnd_of_right
      exact wf₁.h_ft.cnd_of_right h
    · intro x h; apply wf₁.h_ft.cnd_of_left
      exact wf₂.h_ft.cnd_of_left h
  tr_eq := by
    intro s t hs; ext s'; simp [Raw₀.mul]; constructor
    · intro h₁; have hs' := wf_of_tr h₁; use sym₁.fs # sym₂.fs s'
      have ht := wfTrans_of_tr h₁; simp [tr_fs]; use s'
    · rintro ⟨s', h₁, rfl⟩; have hs₁ := wf_of_tr h₁; simp [tr_ft] at h₁
      obtain ⟨s', h₁, rfl⟩ := h₁; have hs' := wf_of_tr h₁; simpa
  tr_eq' := by
    intro s t hs; ext s'; simp [Raw₀.mul]; constructor
    · intro h₁; have hs' := wf_of_tr h₁; use sym₂.fs' # sym₁.fs' s'
      have ht := wfTrans_of_tr h₁; simp [tr_fs']; use s'
    · rintro ⟨s', h₁, rfl⟩; have hs₁ := wf_of_tr h₁; simp [tr_ft'] at h₁
      obtain ⟨s', h₁, rfl⟩ := h₁; have hs' := wf_of_tr h₁; simpa

include wf in
instance {n} : (sym.npow n).WF := by
  simp [Raw₀.npow]; induction n; simp; infer_instance; nm n ih
  rw [Function.iterate_succ']; simp; infer_instance

include wf in
instance {z} : (sym.zpow z).WF := by
  simp [Raw₀.zpow]; split <;> infer_instance

structure Equiv (sym₁ sym₂ : Raw₀ sys) : Prop where
  hs : ∀ {s} [sys.WF s], sym₁.fs s = sym₂.fs s
  hs' : ∀ {s} [sys.WF s], sym₁.fs' s = sym₂.fs' s
  ht : ∀ {t} [sys.WFTrans t], sym₁.ft t = sym₂.ft t
  ht' : ∀ {t} [sys.WFTrans t], sym₁.ft' t = sym₂.ft' t

@[simp, refl]
theorem Equiv.refl : sym.Equiv sym := by constructor <;> simp

omit wf₁ wf₂ in @[symm]
theorem Equiv.symm (h : sym₁.Equiv sym₂) : sym₂.Equiv sym₁ where
  hs := h.hs.symm
  hs' := h.hs'.symm
  ht := h.ht.symm
  ht' := h.ht'.symm

omit wf₁ wf₂ wf₃ in @[trans]
theorem Equiv.trans (h₁ : sym₁.Equiv sym₂) (h₂ : sym₂.Equiv sym₃) : sym₁.Equiv sym₃ where
  hs := h₁.hs.trans # h₂.hs.trans # by rfl
  hs' := h₁.hs'.trans # h₂.hs'.trans # by rfl
  ht := h₁.ht.trans # h₂.ht.trans # by rfl
  ht' := h₁.ht'.trans # h₂.ht'.trans # by rfl

theorem Equiv.iseqv : Equivalence # Equiv (sys := sys) where
  refl := λ _ => refl
  symm := symm
  trans := trans

instance setoid : Setoid (Raw₀ sys) where
  r := Equiv
  iseqv := Equiv.iseqv