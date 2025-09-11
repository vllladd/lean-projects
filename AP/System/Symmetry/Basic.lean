import AP.System.Symmetry.Defs

namespace System.Symmetry

universe u
variable {S T : Type u} {sys : System S T}
variable {sym sym₁ sym₂ sym₃ : sys.Symmetry}
variable [wf : sym.WF] [wf₁ : sym₁.WF] [wf₂ : sym₂.WF] [wf₃ : sym₃.WF]
omit wf wf₁ wf₂ wf₃

@[simp] theorem ft_mk {ft fs} : (⟨ft, fs⟩ : sys.Symmetry).ft = ft := rfl
@[simp] theorem ft'_mk {ft fs} : (⟨ft, fs⟩ : sys.Symmetry).ft' = ft.symm := rfl
@[simp] theorem fs_mk {ft fs} : (⟨ft, fs⟩ : sys.Symmetry).fs = fs := rfl
@[simp] theorem fs'_mk {ft fs} : (⟨ft, fs⟩ : sys.Symmetry).fs' = fs.symm := rfl

@[simp] theorem ft'_ft {t} : sym.ft' (sym.ft t) = t := by simp [ft']
@[simp] theorem ft_ft' {t} : sym.ft (sym.ft' t) = t := by simp [ft']
@[simp] theorem fs'_fs {s} : sym.fs' (sym.fs s) = s := by simp [fs']
@[simp] theorem fs_fs' {s} : sym.fs (sym.fs' s) = s := by simp [fs']

@[simp] theorem ft_symm : sym.ft.symm = sym.ft' := rfl
@[simp] theorem ft'_symm : sym.ft'.symm = sym.ft := rfl
@[simp] theorem fs_symm : sym.fs.symm = sym.fs' := rfl
@[simp] theorem fs'_symm : sym.fs'.symm = sym.fs := rfl

include wf

@[simp]
theorem initial_fs_iff {s} : sys.Initial (sym.fs s) ↔ sys.Initial s :=
  WF.initial_fs_iff

@[simp]
theorem initial_fs'_iff {s} : sys.Initial (sym.fs' s) ↔ sys.Initial s := by
  rw [←sym.fs_fs' (s := s), WF.initial_fs_iff]; simp

theorem tr_eq {s t} : sys.tr s t = (sys.tr (sym.fs s) (sym.ft t)).map sym.fs' :=
  WF.tr_eq

theorem tr_eq' {s t} : sys.tr s t = (sys.tr (sym.fs' s) (sym.ft' t)).map sym.fs := by
  ext s'; nth_rw 2 [sym.tr_eq]; simp

theorem reachable_of {s s'} (h : sys.Reachable s s') :
sys.Reachable (sym.fs s) (sym.fs s') := by
  induction h; rfl; nm a b c t h₁ h₂ ih; rw [sym.tr_eq] at h₁
  simp at h₁; obtain ⟨s', h₁, rfl⟩ := h₁; simp at ih
  exact reachable_of_tr h₁ |>.trans ih

theorem reachable'_of {s s'} (h : sys.Reachable s s') :
sys.Reachable (sym.fs' s) (sym.fs' s') := by
  induction h; rfl; nm a b c t h₁ h₂ ih; rw [sym.tr_eq'] at h₁
  simp at h₁; obtain ⟨s', h₁, rfl⟩ := h₁; simp at ih
  exact reachable_of_tr h₁ |>.trans ih

theorem reachable_iff {s s'} :
sys.Reachable s s' ↔ sys.Reachable (sym.fs s) (sym.fs s') := by
  use sym.reachable_of; intro h; apply sym.reachable'_of at h; simp at h; exact h

theorem reachable_iff' {s s'} :
sys.Reachable s s' ↔ sys.Reachable (sym.fs' s) (sym.fs' s') := by
  nth_rw 2 [sym.reachable_iff]; simp

@[simp]
theorem wf_fs_iff {s} : sys.WF (sym.fs s) ↔ sys.WF s := by
  constructor <;> rintro ⟨s₀, h₁, h₂⟩
  · use sym.fs' s₀; simp [h₁]; rw [sym.reachable_iff]; simpa
  · use sym.fs s₀; simp [h₁]; rw [sym.reachable_iff']; simpa

@[simp]
theorem wf_fs'_iff {s} : sys.WF (sym.fs' s) ↔ sys.WF s := by
  rw [←sym.wf_fs_iff]; simp

instance {s} [hs : sys.WF s] : sys.WF (sym.fs s) := by simpa
instance {s} [hs : sys.WF s] : sys.WF (sym.fs' s) := by simpa

theorem validTr_iff {s t} :
sys.validTr s t ↔ sys.validTr (sym.fs s) (sym.ft t) := by
  unfold validTr; nth_rw 2 [sym.tr_eq']; simp; rw [exists_comm]; simp

theorem validTr_iff' {s t} :
sys.validTr s t ↔ sys.validTr (sym.fs' s) (sym.ft' t) := by
  nth_rw 2 [sym.validTr_iff]; simp

theorem hasTr_iff {s} : sys.hasTr s ↔ sys.hasTr (sym.fs s) := by
  constructor <;> intro ⟨t, h⟩
  · use sym.ft t; rw [sym.validTr_iff']; simpa
  · use sym.ft' t; rw [sym.validTr_iff]; simpa

theorem hasTr_iff' {s} : sys.hasTr s ↔ sys.hasTr (sym.fs' s) := by
  nth_rw 2 [sym.hasTr_iff]; simp

@[simp]
theorem hasTr_fs_iff {s} : sys.hasTr (sym.fs s) ↔ sys.hasTr s :=
  sym.hasTr_iff.symm

@[simp]
theorem hasTr_fs'_iff {s} : sys.hasTr (sym.fs' s) ↔ sys.hasTr s :=
  sym.hasTr_iff'.symm

omit wf

@[simp] theorem ft_one {t} : (1 : sys.Symmetry).ft t = t := rfl
@[simp] theorem ft'_one {t} : (1 : sys.Symmetry).ft' t = t := rfl
@[simp] theorem fs_one {s} : (1 : sys.Symmetry).fs s = s := rfl
@[simp] theorem fs'_one {s} : (1 : sys.Symmetry).fs' s = s := rfl

@[simp]
instance : (1 : sys.Symmetry).WF where
  initial_fs_iff := by simp
  tr_eq := by simp [one_def, one]

instance {f} [hf : sys.SimFn f] : sys.SimFn # sym.simFn f := by
  constructor; intro s hs; rw [sym.validTr_iff']; simp

@[simp] theorem ft_inv : sym⁻¹.ft = sym.ft' := rfl
@[simp] theorem ft'_inv : sym⁻¹.ft' = sym.ft := rfl
@[simp] theorem fs_inv : sym⁻¹.fs = sym.fs' := rfl
@[simp] theorem fs'_inv : sym⁻¹.fs' = sym.fs := rfl

instance : sym⁻¹.WF where
  initial_fs_iff := by simp
  tr_eq := by simp [←sym.tr_eq']

@[simp]
theorem inv_inv : sym⁻¹⁻¹ = sym := by ext <;> rfl

@[simp] theorem ft_mul {t} : (sym₁ * sym₂).ft t = sym₁.ft (sym₂.ft t) := rfl
@[simp] theorem ft'_mul {t} : (sym₁ * sym₂).ft' t = sym₂.ft' (sym₁.ft' t) := rfl
@[simp] theorem fs_mul {s} : (sym₁ * sym₂).fs s = sym₁.fs (sym₂.fs s) := rfl
@[simp] theorem fs'_mul {s} : (sym₁ * sym₂).fs' s = sym₂.fs' (sym₁.fs' s) := rfl

instance : (sym₁ * sym₂).WF where
  initial_fs_iff := by simp
  tr_eq := by intro s t; simp [mul_def, mul]; rw [sym₂.tr_eq, sym₁.tr_eq]; simp

instance : (sym₁ / sym₂).WF := by
  rw [div_def]; infer_instance

@[simp]
protected theorem inv_mul_cancel : sym⁻¹ * sym = 1 := by
  ext <;> simp

@[simp]
protected theorem inv_eq_of_mul (h : sym₁ * sym₂ = 1) : sym₁⁻¹ = sym₂ := by
  symm at h; simp [mul_def, mul, Symmetry.ext_iff, Equiv.ext_iff] at h
  rcases h with ⟨h₁, h₂⟩; ext
  · nm t; simp; rw [h₁ t]; simp; apply h₁
  · nm s; simp; rw [h₂ s]; simp; apply h₂

instance : Group sys.Symmetry where
  mul_assoc := λ _ _ _ => rfl
  one_mul := λ _ => rfl
  mul_one := λ _ => rfl
  inv_mul_cancel := λ _ => Symmetry.inv_mul_cancel

instance : DivisionMonoid sys.Symmetry where
  mul_inv_rev := λ _ _ => rfl
  inv_eq_of_mul := λ _ _ => Symmetry.inv_eq_of_mul

theorem npow_def {n : ℕ} : sym ^ n = sym.npow n := by
  simp [npow]

instance {n : ℕ} : (sym ^ n).WF := by
  induction n; simp; nm n ih; rw [pow_succ]; infer_instance

theorem zpow_def {z : ℤ} : sym ^ z = sym.zpow z := by
  unfold zpow; split <;> simp [←npow_def]

instance {z : ℤ} : (sym ^ z).WF := by
  cases z <;> simp <;> infer_instance

@[simp] theorem simFn'_simFn {f} : sym.simFn' (sym.simFn f) = f := by ext s; simp
@[simp] theorem simFn_simFn' {f} : sym.simFn (sym.simFn' f) = f := by ext s; simp
@[simp] theorem simFn_inv : sym⁻¹.simFn = sym.simFn' := by rfl

include wf

theorem tr_fs_ft {s t} : sys.tr (sym.fs s) (sym.ft t) = (sys.tr s t).map sym.fs := by
  rw [sym.tr_eq']; simp

theorem tr_fs'_ft' {s t} : sys.tr (sym.fs' s) (sym.ft' t) = (sys.tr s t).map sym.fs' := by
  rw [sym.tr_eq]; simp

theorem trs_eq {s ts} : sys.trs s ts =
(sys.trs (sym.fs s) # ts.map sym.ft).map sym.fs' (·.map sym.ft') := by
  induction ts generalizing s; simp; nm t ts ih; simp [tr_fs_ft]
  split; nm x h₁; clear x; simp [h₁]; nm x s' h₁; clear x; simp [h₁, ih]

theorem trs_eq' {s ts} : sys.trs s ts =
(sys.trs (sym.fs' s) # ts.map sym.ft').map sym.fs (·.map sym.ft) :=
  sym⁻¹.trs_eq

theorem simulate_eq {f s n} : sys.simulate f s n =
(sys.simulate (sym.simFn f) (sym.fs s) n).map sym.fs' id := by
  induction n generalizing s; simp; nm n ih; simp [tr_fs_ft]
  split; nm x h₁; clear x; simp [h₁]; nm x s' h₁; clear x; simp [h₁, ih]

theorem simulate_eq' {f s n} : sys.simulate f s n =
(sys.simulate (sym.simFn' f) (sym.fs' s) n).map sym.fs id :=
  sym⁻¹.simulate_eq

@[simp]
theorem snd_simulate_eq {f s n} :
(sys.simulate (sym.simFn f) s n).2 = (sys.simulate f (sym.fs' s) n).2 := by
  rw [sym.simulate_eq']; simp

@[simp]
theorem snd_simulate_eq' {f s n} :
(sys.simulate (sym.simFn' f) s n).2 = (sys.simulate f (sym.fs s) n).2 := by
  rw [sym.simulate_eq]; simp