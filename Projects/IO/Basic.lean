import Projects.IO.Defs

namespace VerifiedIO

variable {α β γ : Type}

attribute [simp, instance] ProgM.WF.toProgM ProgM.WF.pure ProgM.WF.bit

instance ProgM.WF.bind' {m : ProgM α} {f : α → ProgM β}
[H₁ : WF m] [H₂ : ∀ x, WF # f x] : WF (m >>= f) :=
  .bind H₁ H₂

@[simp]
theorem Prog.toProgM₂_zero {p : Prog} {bs} : p.toProgM₂ bs 0 = pure () := rfl

@[simp]
theorem Prog.toProgM₂_succ {p : Prog} {bs n} :
p.toProgM₂ bs (n + 1) = ioBit (p.run bs) >>= λ b => p.toProgM₂ (bs ++ [b]) n := rfl

theorem Prog.toProgM₁_eq {p : Prog} {bs : List Bit} :
p.toProgM₁ bs = ioBit (p.run bs) >>= λ b => p.toProgM₁ (bs ++ [b]) := by
  ext bs₀; unfold toProgM₁; simp [gets]; cases bs₀ <;> simp [ioBit]; rfl

@[simp]
theorem ProgM.run_toProg {m : ProgM Unit} :
m.toProg.run = λ bs => match m.run bs with | .inl b => b | .inr _ => 0 := rfl

@[simp]
theorem Prog.run_toProgM₁_nil {p : Prog} {bs₀} :
(p.toProgM₁ bs₀).run [] = .inl (p.run bs₀) := rfl

@[simp]
theorem Prog.run_toProgM_nil {p : Prog} :
p.toProgM.run [] = .inl (p.run []) := rfl

@[simp]
theorem Prog.run_toProgM₁_cons {p : Prog} {bs₁ bs₂ b} :
(p.toProgM₁ bs₁).run (b :: bs₂) = (p.toProgM₁ (bs₁ ++ [b])).run bs₂ := by
  rw [toProgM₁_eq]; nth_rw 1 [ioBit]; simp

@[simp]
theorem Prog.run_toProgM_cons {p : Prog} {b bs} :
p.toProgM.run (b :: bs) = (p.toProgM₁ [b]).run bs := by
  simp [toProgM]

@[simp]
theorem Prog.run_toProgM₁_append {p : Prog} {bs₁ bs₂ bs₃} :
(p.toProgM₁ bs₁).run (bs₂ ++ bs₃) = (p.toProgM₁ (bs₁ ++ bs₂)).run bs₃ := by
  induction bs₂ generalizing bs₁ bs₃ <;> simp
  nm b bs₂ ih; rw [ih]; simp

@[simp]
theorem Prog.toProg_toProgM {p : Prog} : p.toProgM.toProg = p := by
  ext bs; simp [toProgM]; generalize h : [] = bs₀
  nth_rw 2 [show bs = bs₀ ++ bs by grind]; clear h
  induction bs generalizing bs₀ <;> simp
  nm b bs ih; rw [ih]; simp

theorem ProgM.wf_iff {m : ProgM α} : m.WF ↔
(∃ (p : Prog), α = Unit ∧ p.toProgM ≍ m) ∨ (∃ x, pure x = m) ∨
(∃ (β : Type) (m' : ProgM β) (f : β → ProgM α), m'.WF ∧
(∀ x, f x |>.WF) ∧ (m' >>= f) = m) ∨ (∃ b, α = Bit ∧ ioBit b ≍ m) := by
  constructor; rintro ⟨⟩ <;> grind
  rintro (⟨p, rfl, rfl⟩ | ⟨x, rfl⟩ | ⟨β, m, f, h₁, h₂, rfl⟩ | ⟨b, rfl, rfl⟩) <;> infer_instance

theorem Prog.toProgM_eq_iff {p : Prog} {m : ProgM Unit} :
p.toProgM = m ↔ ∀ bs₁ bs₂, (p.toProgM₁ bs₁).run bs₂ = m.run (bs₁ ++ bs₂) := by
  unfold toProgM
  constructor
  · rintro rfl bs₁ bs₂
    generalize h : [] = bs₃
    nth_rw 1 [show bs₁ = bs₃ ++ bs₁ by grind]
    simp
  · intro h
    ext bs
    apply h

-- @[simp]
-- theorem ProgM.toProgM_toProg {m : ProgM Unit} [wf : m.WF] : m.toProg.toProgM = m := by
--   rw [wf_iff] at wf
--   rcases wf with (⟨p, ⟨⟩, rfl⟩ | ⟨x, rfl⟩ | ⟨β, m, f, h₁, h₂, rfl⟩ | ⟨b, h, -⟩)
--   ·
--     simp
--   ·
--     simp [toProg]
--     rw [Prog.toProgM_eq_iff]
--     intro bs₁ bs₂; simp
--     induction bs₂ <;> simp
--     
-- #check 0 #exit
-- 
-- @[instance]
-- theorem ProgM.wf_of_wf' {m : ProgM Unit} [H : m.WF'] : m.WF := by
--   rw [wf_iff]; use m.toProg
--   rw [wf'_iff] at H
--   rcases H with (⟨x, rfl⟩ | ⟨β, m, f, h₁, h₂, rfl⟩ | ⟨b, h, -⟩)
--   ·
--     rw [toProgM_toProg]