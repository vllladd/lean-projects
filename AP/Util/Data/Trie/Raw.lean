import AP.Util.Data.Trie.Raw0

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
  max acc # 1 + f i ⟨_, wf.get? h₂⟩ h₂

@[simp]
theorem depth_empty : (∅ : Raw α β).depth = 0 := by
  simp [empty_def, Raw₀.empty_def, depth]

def get? (t : Raw α β) (k : α) : Option (Raw α β) :=
  match h : t.mp.get? k with
  | none => none
  | some t' => some ⟨t', t.wf.get? h⟩

theorem get?_eq_some_iff {k t'} :
t.get? k = some t' ↔ t.mp.get? k = t'.inner := by
  simp [get?]
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
  specialize ih k ⟨_, wf.get? h⟩
  rwa [ih]

theorem depth_lt {k t'} (h : t.get? k = some t') : t'.depth < t.depth := by
  simp_rw [depth_eq_depth_inner]; simp [get?_eq_some_iff] at h; exact Raw₀.depth_lt h

@[simp]
theorem depth_mk {raw : Raw₀ α β} [wf : raw.WF] : (Raw.mk raw wf).depth = raw.depth := by
  simp [depth_eq_depth_inner]

@[simp]
theorem get?_mp_inner_eq_some_inner_iff {k} :
t.inner.mp.get? k = some t'.inner ↔ t.get? k = some t' := by
  simp [get?, mp]
  split
  · nm h
    simp [h]
  nm t₁ h
  cases t'; simp [h]

@[simp]
theorem WF.mp : t.mp.WF := by
  simp [Raw.mp]

theorem get?_mp {k} : t.mp.get? k = (t.get? k).map (·.1) := by
  ext x
  simp [get?]
  constructor
  · intro h
    rw! [h]
    simp
  · rintro ⟨a, h, rfl⟩
    split at h <;> simp at h
    simpa [←h]

theorem mem_of_get?_eq_some {k x} (h : t.get? k = some x) : k ∈ t.mp := by
  rw [get?_eq_some_iff] at h; exact t.mp.mem_of_get?_eq_some (by simp) h

theorem mem_mp_iff_get?_eq_some {k} : k ∈ t.mp ↔ ∃ x, t.get? k = some x := by
  rw [t.mp.mem_iff_isSome_get? # by simp]
  rw [Option.isSome_iff_exists]
  simp [get?_mp]