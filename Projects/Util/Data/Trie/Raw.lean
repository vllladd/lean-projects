import Projects.Util.Data.Trie.Raw0

namespace Trie

open Std

@[ext]
structure Raw (α β : Type*) [DecidableEq α] [Hashable α] where
  inner : Raw₀ α β
  wf : inner.WF

namespace Raw

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable {t t' t₁ t₂ t₃ : Raw α β}

@[simp] instance : t.inner.WF := t.wf

def val (t : Raw α β) : Option β :=
  t.inner.val

def mp (t : Raw α β) : DHashMap.Raw α (λ _ => Raw₀ α β) :=
  t.inner.mp

@[simp] theorem val_mk {inner wf} : (⟨inner, wf⟩ : Raw α β).val = inner.val := rfl
@[simp] theorem mp_mk {inner wf} : (⟨inner, wf⟩ : Raw α β).mp = inner.mp := rfl

set_option linter.unusedVariables false
def rec' {γ : Raw α β → Sort*}
(motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw₀ α β)) wf,
(∀ i (t : Raw α β), mp.get? i = some t.inner → γ t) → γ ⟨Raw₀.mk val mp, wf⟩) :
(t : Raw α β) → γ t
| .mk (Raw₀.mk val mp) wf => motive val mp wf # λ i t h₁ => mk t.inner t.wf |>.rec' motive
termination_by t => t.1.depth
decreasing_by apply Raw₀.depth_lt; exact h₁

abbrev ind := @rec'

@[simp]
theorem rec'_mk {γ : Raw α β → Sort*} {val : Option β}
{mp : DHashMap.Raw α (λ _ => Raw₀ α β)} {wf : (⟨val, mp⟩ : Raw₀ α β).WF}
{motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw₀ α β)) wf,
(∀ i (t : Raw α β), mp.get? i = some t.inner → γ t) → γ ⟨Raw₀.mk val mp, wf⟩} :
(⟨⟨val, mp⟩, wf⟩ : Raw α β).rec' motive =
motive val mp wf (λ _ t h => t.rec' motive) := by
  simp [rec']

def empty : Raw α β where
  inner := ∅
  wf := inferInstance

instance : EmptyCollection # Raw α β := ⟨empty⟩
theorem empty_def : (∅ : Raw α β) = ⟨∅, inferInstance⟩ := rfl

@[simp] theorem inner_empty : (∅ : Raw α β).inner = ∅ := rfl

def depth (t : Raw α β) : ℕ :=
  t.rec' (γ := λ _ => ℕ) # λ _ mp wf f => (mp.foldWith wf.mp · 0) # λ acc i x h₂ =>
  max acc # 1 + f i ⟨_, wf.get1? h₂⟩ h₂

@[simp]
theorem depth_empty : (∅ : Raw α β).depth = 0 := by
  simp [empty_def, Raw₀.empty_def, depth]

def get1? (t : Raw α β) (k : α) : Option (Raw α β) :=
  match h : t.mp.get? k with
  | none => none
  | some t' => some ⟨t', t.wf.get1? h⟩

theorem get1?_eq_some_iff {k t'} :
t.get1? k = some t' ↔ t.mp.get? k = t'.inner := by
  simp [get1?]
  apply Iff.intro
  · intro a
    split at a
    next heq => simp_all only [reduceCtorEq]
    next t'_1 heq =>
      simp_all only [Option.some.injEq]
      subst a
      simp_all only
  · intro a
    split
    next heq => simp_all only [reduceCtorEq]
    next t'_1 heq => simp_all only [Option.some.injEq]

theorem depth_eq_depth_inner : t.depth = t.inner.depth := by
  apply t.ind
  simp only [Raw₀.depth_mk]
  intro val mp wf ih
  simp only [depth, rec'_mk] at ih ⊢
  congr
  ext i k t' h
  specialize ih k ⟨_, wf.get1? h⟩
  rwa [ih]

theorem depth_lt {k t'} (h : t.get1? k = some t') : t'.depth < t.depth := by
  simp_rw [depth_eq_depth_inner]; simp [get1?_eq_some_iff] at h; exact Raw₀.depth_lt h

@[simp]
theorem depth_mk {raw : Raw₀ α β} [wf : raw.WF] : (Raw.mk raw wf).depth = raw.depth := by
  simp [depth_eq_depth_inner]

@[simp]
theorem get?_mp_inner_eq_some_inner_iff {k} :
t.inner.mp.get? k = some t'.inner ↔ t.get1? k = some t' := by
  simp [get1?, mp]
  split
  · nm h
    simp [h]
  nm t₁ h
  cases t'; simp [h]

@[simp]
theorem WF.mp : t.mp.WF := by
  simp [Raw.mp]

theorem get?_mp {k} : t.mp.get? k = (t.get1? k).map (·.1) := by
  ext x
  simp [get1?]
  constructor
  · intro h
    rw! [h]
    simp
  · rintro ⟨a, h, rfl⟩
    split at h <;> simp at h
    simpa [←h]

theorem mem_of_get?_eq_some {k x} (h : t.get1? k = some x) : k ∈ t.mp := by
  rw [get1?_eq_some_iff] at h; exact t.mp.mem_of_get?_eq_some (by simp) h

theorem mem_mp_iff_get?_eq_some {k} : k ∈ t.mp ↔ ∃ x, t.get1? k = some x := by
  rw [t.mp.mem_iff_isSome_get? # by simp]
  rw [Option.isSome_iff_exists]
  simp [get?_mp]

def isEmpty (t : Raw α β) : Prop :=
  t.1.isEmpty

instance : Decidable t.isEmpty :=
  show Decidable t.1.isEmpty from inferInstance

def setVal (t : Raw α β) (val : Option β) : Raw α β :=
  ⟨t.1.setVal val, inferInstance⟩

@[simp] theorem val_setVal {val} : (t.setVal val).val = val := rfl
@[simp] theorem mp_setVal {val} : (t.setVal val).mp = t.mp := rfl

def erase1 (t : Raw α β) (i : α) : Raw α β :=
  ⟨t.1.erase1 i, inferInstance⟩

@[simp] theorem val_erase1 {i} : (t.erase1 i).val = t.val := rfl
@[simp] theorem mp_erase1 {i} : (t.erase1 i).mp = t.mp.erase i := rfl

def insert1 (t : Raw α β) (i : α) (t₁ : Raw α β) : Raw α β :=
  ⟨t.1.insert1 i t₁.1, inferInstance⟩

@[simp]
theorem val_insert1 {i t₁} : (t.insert1 i t₁).val = t.val :=
  t.1.val_insert1

theorem mp_insert1 {i} : (t.insert1 i t₁).mp =
if t₁.isEmpty then t.mp.erase i else t.mp.insert i t₁.1 :=
  t.1.mp_insert1

theorem get1?_eq_get1?_inner {i} : t.get1? i = match h : t.1.get1? i with
| none => none
| some t₁ => some ⟨t₁, t.2.get1? h⟩ := rfl

theorem get1?_eq_some_iff_inner {i t₁} : t.get1? i = some t₁ ↔ t.1.get1? i = some t₁.1 := by
  rw [get1?_eq_get1?_inner]; split <;> simp_all [Raw.ext_iff]

theorem get1?_eq_none_iff_inner {i} : t.get1? i = none ↔ t.1.get1? i = none := by
  rw [get1?_eq_get1?_inner]; split <;> simp_all

theorem get1?_erase1 {i j} :
(t.erase1 i).get1? j = if i = j then none else t.get1? j := by
  ext; simp [get1?_eq_some_iff_inner, erase1, Raw₀.get1?_erase1]

theorem get1?_insert1 {i j} {t₁ : Raw α β} :
(t.insert1 i t₁).get1? j = if i = j then
if t₁.isEmpty then none else some t₁ else t.get1? j := by
  ext t'
  simp [get1?_eq_some_iff_inner]
  unfold insert1
  rw [Raw₀.get1?_insert1]
  by_cases h : t₁.isEmpty <;> simp [h] <;> rw [isEmpty] at h
  · simp [h, get1?_eq_some_iff_inner]
  · simp [h]; split_ifs with h₁
    · simp [Raw.ext_iff]
    · simp [get1?_eq_some_iff_inner]

@[simp]
theorem get1?_erase1_eq_some_iff {i j} :
(t.erase1 i).get1? j = some t₁ ↔ i ≠ j ∧ t.get1? j = t₁ := by
  simp [get1?_eq_some_iff_inner, erase1]