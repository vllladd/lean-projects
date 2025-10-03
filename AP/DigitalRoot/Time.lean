import AP.DigitalRoot.List

section logic

@[simp]
theorem choose?_eq_some_iff {α : Type*} {p : α → Prop} {x}
[hp : Decidable # ∃ x, p x] : choose? p = some x ↔ p x ∧
haveI : Inhabited α := ⟨x⟩; Classical.epsilon p = x := by
  have h₁ : Inhabited α := ⟨x⟩; simp [choose?]; constructor
  · rintro ⟨h₂, rfl⟩; use h₂.choose_spec, choose_eq_epsilon h₂ |>.symm
  · rintro ⟨h₂, h₃⟩; use ⟨_, h₂⟩; rwa [choose_eq_epsilon ⟨_, h₂⟩]

theorem epsilon_eq_of_exiu {α : Type*} [ha : Inhabited α] {p : α → Prop} {x}
(h₁ : p x) (h₂ : ∃! x, p x) : Classical.epsilon p = x := by
  have hp : p = λ y => x = y
  · ext y; obtain ⟨z, h₂, h₃⟩ := h₂
    constructor <;> intro h₄
    · rw [h₃ _ h₁, h₃ _ h₄]
    · rwa [←h₄]
  have h₃ := Classical.epsilon_spec h₂
  dsimp at h₃; subst hp; simp at h₃; exact h₃.symm

theorem epsilon_eq_of {α : Type*} [ha : Inhabited α] {p : α → Prop} {x}
(h₁ : p x) (h₂ : ∀ y, p y → y = x) : Classical.epsilon p = x := by
  apply epsilon_eq_of_exiu h₁; use x

-- #check 0 #exit

end logic

section order

variable {α : Type*} [ha₁ : DecidableEq α] [ha₂ : Fintype α]

noncomputable
def fintypeIdx (x : α) : ℕ :=
  Finset.univ.toList.idxOf x

@[simp]
theorem fintypeIdx_eq_iff {x y : α} : fintypeIdx x = fintypeIdx y ↔ x = y := by
  symm; constructor; rintro rfl; rfl; intro h; unfold fintypeIdx at h
  rwa [List.idxOf_inj] at h <;> simp

open Classical in noncomputable
def fintypeToLinearOrder : LinearOrder α where
  le a b := fintypeIdx a ≤ fintypeIdx b
  le_refl a := by rfl
  le_trans a b c h₁ h₂ := h₁.trans h₂
  le_antisymm a b h₁ h₂ := by
    have h₃ := le_antisymm h₁ h₂
    simp at h₃; exact h₃
  le_total a b := by apply le_total
  toDecidableLE := by infer_instance

-- #check 0 #exit

end order

namespace Map

variable {α : Type*} [ha₁ : LinearOrder α] [ha₂ : Hashable α]
variable {mp mp₁ mp₂ : Map α ℕ}

def push (mp : Map α ℕ) (i : α) : Map α ℕ :=
  mp.insert i # (mp.get? i).getD 0 + 1

theorem get?_insert {i j x} :
(mp.insert j x).get? i = if j = i then some x else mp.get? i := by
  convert mp.1.get?_insert; simp; rfl

theorem push_push_comm {i j} : (mp.push i).push j = (mp.push j).push i := by
  ext; simp [push, get?_insert]; aesop

-- #check 0 #exit

end Map

namespace DigitalRoot

structure Time : Type where
  hour : Fin 24
  minute : Fin 60
deriving Inhabited, DecidableEq, Fintype, Hashable

def Time.toList (t : Time) : List ℕ :=
  [t.hour, t.minute]

@[simp]
def timeSet : Set' Time := Set'.univ

def digRootTime (b : ℕ) (t : Time) : ℕ :=
  digRootList b t.toList

open Classical in noncomputable
def freqTimeDig (b : ℕ) : Option ℕ := choose? # λ d =>
  let f d₁ := timeSet.count (digRootTime b · = d₁)
  d ≤ b ∧ ∀ d', d' ≠ d → f d' < f d

def freqTimeDigFn (b : ℕ) (mp : Map ℕ ℕ) (t : Time) : Map ℕ ℕ :=
  mp.push # digRootTime b t

theorem freqTimeDigFn_freqTimeDigFn_comm {b} {mp : Map ℕ ℕ} {t₁ t₂ : Time} :
freqTimeDigFn b (freqTimeDigFn b mp t₁) t₂ = freqTimeDigFn b (freqTimeDigFn b mp t₂) t₁ :=
  Map.push_push_comm

def freqTimeDig' (b : ℕ) : Option ℕ := do
  let res : Map ℕ ℕ := timeSet.fold (freqTimeDigFn b) ∅
    freqTimeDigFn_freqTimeDigFn_comm
  let xs := res.toList.mergeSort # λ a b => b.2 ≤ a.2
  match xs with
  | (d₁, c₁) :: (_, c₂) :: _ => do
    guard # c₁ ≠ c₂
    pure d₁
  | _ => none

-- variable {b} [hb : Base b]

-- #check 0 #exit

theorem freqTimeDig_eq_freqTimeDig' {b} : freqTimeDig b = freqTimeDig' b := by
  have H := fintypeToLinearOrder (α := Time)
  ext d
  simp [freqTimeDig, freqTimeDig']
  constructor
  · rintro ⟨⟨h₁, h₂⟩, -⟩
    rw [Set'.fold_eq_foldl_toList]
    sorry
  · intro h
    split at h <;> simp at h
    nm xs d₁ c₁ d₂ c₂ ys h₁
    rcases h with ⟨h, rfl⟩
    apply and_of
    · constructor
      · sorry
      · intro d' h₂
        sorry
    rintro ⟨h₂, h₃⟩
    apply epsilon_eq_of ⟨h₂, h₃⟩
    rintro d₁' ⟨h₄, h₅⟩
    by_contra! h₆
    specialize h₃ _ h₆
    specialize h₅ _ # ne_symm' h₆
    linarith

-- #check 0 #exit

theorem freqTimeDig_10_eq_some_5 : freqTimeDig 10 = some 5 := by
  rw [freqTimeDig_eq_freqTimeDig']; native_decide