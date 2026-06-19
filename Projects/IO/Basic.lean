import Projects.IO.Defs

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

-- #check 0 #exit

end List

section monad

variable {α β γ : Type}
variable {M : Type → Type} [hM₁ : Monad M] [hM₂ : LawfulMonad M]

-- #check 0 #exit

end monad

section MonadState

variable {α β γ : Type}
variable {σ : Type} {M : Type → Type}
variable [hσ : MonadState σ M] [hM : Monad M]

-- #check 0 #exit

end MonadState

namespace VerifiedIO

variable {α β γ : Type}

@[instance, simp]
theorem ProgM.wf_pure {x : α} : (pure x : ProgM α).WF := by
  constructor <;> simp

@[instance]
theorem ProgM.wf_bind {m : ProgM α} {f : α → ProgM β}
[H₁ : m.WF] [H₂ : ∀ x, (f x).WF] : (m >>= f).WF := by
  constructor
  · intro xs zs r h₁;
    simp at h₁
    obtain ⟨x, bs, h₁, h₂⟩ := h₁
    replace H₁ := H₁.1 h₁
    replace H₂ := (H₂ x).1 h₂
    obtain ⟨h₃, h₄⟩ := H₁
    obtain ⟨h₅, h₆⟩ := H₂
    use h₅.trans h₃
    intro ys
    simp [h₄, h₆]
  · intro xs b h₁ ys zs r h₂
    simp at h₁ h₂
    obtain ⟨x, bs, h₂, h₃⟩ := h₂
    rcases h₁ with h₁ | ⟨y, bs', h₄, h₅⟩
    · obtain ⟨h₅, h₆⟩ := H₁.2 h₁ h₂
      obtain ⟨h₇, h₈⟩ := (H₂ x).1 h₃
      use h₇.trans h₅
      rintro rfl
      apply h₆; clear h₆
      exact List.suffix_antisymm h₅ h₇
    · obtain ⟨h₆, h₇⟩ := H₁.1 h₄
      simp [h₇] at h₂; clear h₇
      rcases h₂ with ⟨rfl, rfl⟩
      exact (H₂ y).2 h₅ h₃

@[instance]
theorem ProgM.monadCnd_wf : MonadCnd (M := ProgM) WF := by
  use wf_pure; apply wf_bind

@[instance]
theorem ProgM.wf_map {m : ProgM α} {f : α → β} [H₁ : m.WF] : (f <$> m).WF :=
  MonadCnd.map inferInstance

example : ¬(gets List.length : ProgM _).WF := by
  rintro ⟨h₁, -⟩; specialize @h₁ [] [] 0 (by rfl)
  replace h₁ := @h₁.2 [0]; revert h₁; simp

@[instance, simp]
theorem ProgM.wf_ioBit {b} : (ioBit b).WF := by
  constructor
  · intro xs zs r h₁
    simp [ioBit] at h₁
    split at h₁ <;> cases h₁
    nm bs b₁
    simp
    intro ys
    rfl
  · intro xs b₁ h₁ ys zs r h₂
    simp [ioBit] at h₁ h₂
    split at h₂; grind
    nm bs₀ b₂ bs h₃
    cases h₂
    split at h₁
    · nm bs'
      simp at h₃
      subst h₃
      cases h₁
      simp
    nm bs' b₃ bs₁
    simp at h₃
    rcases h₃ with ⟨rfl, rfl⟩
    simp at h₁

@[instance, simp]
theorem Prog.wf_toProgM {p : Prog} : p.toProgM.WF := by
  constructor <;> simp [toProgM]

@[simp]
theorem toProg_toProgM {p : Prog} : p.toProgM.toProg = p := by
  ext; simp [ProgM.toProg, Prog.toProgM]; simp [bind, Sum.bind]

theorem toProgM_toProg {m : ProgM Unit}
(h : ∀ bs, ∃ b, m.run bs = .inl b) : m.toProg.toProgM = m := by
  ext; simp [ProgM.toProg, Prog.toProgM]; simp [bind, Sum.bind]
  nm bs; choose b h₁ using h bs; simp [h₁]

@[simp] theorem run_ioBit_nil {b} : (ioBit b).run [] = .inl b := rfl
@[simp] theorem run_ioBit_cons {b b₁ bs} : (ioBit b).run (b₁ :: bs) = .inr (b₁, bs) := rfl
@[simp] theorem run_readBit_nil : readBit.run [] = .inl 0 := rfl
@[simp] theorem run_readBit_cons {b bs} : readBit.run (b :: bs) = .inr (b, bs) := rfl
@[simp] theorem run_writeBit_nil {b} : (writeBit b).run [] = .inl b := rfl
@[simp] theorem run_writeBit_cons {b b₁ bs} : (writeBit b).run (b₁ :: bs) = .inr ((), bs) := rfl

@[instance, simp]
theorem ProgM.wf_readBit : readBit.WF := by
  simp [readBit]

@[instance, simp]
theorem ProgM.wf_writeBit {b} : (writeBit b).WF := by
  unfold writeBit; infer_instance

@[instance, simp]
theorem ProgM.wf_readBitsUntil {p} : (readBitsUntil p).WF := by
  unfold readBitsUntil; simp; constructor
  · intro xs zs r h
    simp at h
    split at h <;> simp at h
    nm x bs₁ h₁; clear x
    rcases h with ⟨rfl, rfl⟩
    use by simp
    intro ys
    simp [h₁]
    rw [List.drop_append]
    simp [Nat.sub_eq_zero_iff_le]
    left
    replace h₁ := List.mem_of_find?_eq_some h₁
    simp at h₁
    grind
  · intro xs b h₁ ys zs r h₂
    simp at h₁ h₂
    split at h₁ <;> simp at h₁
    nm x h₁; clear x
    subst h₁
    simp [h₁] at h₂
    simp at h₁
    split at h₂ <;> simp at h₂
    nm x bs h₃; clear x
    rcases h₂ with ⟨rfl, rfl⟩
    rw [List.drop_append]
    simp
    have h₂ := h₃
    replace h₃ := List.mem_of_find?_eq_some h₃
    have h₄ := List.mem_of_mem_tail h₃
    simp at h₄
    obtain ⟨bs, ⟨zs, rfl⟩, rfl⟩ := h₄
    simp
    replace h₂ := List.find?_some h₂
    grind

@[instance, simp]
theorem ProgM.wf_readNat : readNat.WF := by
  unfold readNat; infer_instance

@[instance, simp]
theorem ProgM.writeNat {n} : (writeNat n).WF := by
  unfold VerifiedIO.writeNat; apply MonadCnd.bind
  · apply MonadCnd.replicateM'; infer_instance
  · infer_instance