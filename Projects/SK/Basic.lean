import Projects.SK.Defs

namespace SK

open Expr

@[simp, instance]
theorem reduced_K : Reduced K := by
  constructor; intro a h; generalize hx : K = x at h; induction h <;> grind

@[simp, instance]
theorem reduced_S : Reduced S := by
  constructor; intro a h; generalize hx : S = x at h; induction h <;> grind

@[simp]
theorem reduces_reduced_iff {a b} [ha : Reduced a] : Reduces a b ↔ a = b := by
  use ha.h; rintro rfl; rfl

theorem reduced_iff {a} : Reduced a ↔ ∀ {b}, Reduces a b → a = b :=
  ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem reduces_comb1_iff {c a b} (hc : c = K ∨ c = S) :
Reduces (c %% a) b ↔ ∃ a', Reduces a a' ∧ c %% a' = b := by
  rcases hc with rfl | rfl; all_goals
  symm; constructor
  · rintro ⟨a', h₁, rfl⟩; exact Reduces.app .rfl h₁
  intro h; generalize hy : _ %% a = y at h
  induction h generalizing a
  any_goals simp at hy
  · subst hy; use a
  · nm b c d h₁ h₂ ih₁ ih₂; subst hy; simp at ih₁
    obtain ⟨a', ih₁, rfl⟩ := ih₁; simp at ih₂
    obtain ⟨a₁, ih₂, rfl⟩ := ih₂; simp; exact ih₁.trans ih₂
  · clear b; nm b c d e h₁ h₂ ih₁ ih₂
    obtain ⟨rfl, rfl⟩ := hy; simp at h₁; subst h₁; simpa

theorem K1_reduces_iff {a b} : Reduces (K %% a) b ↔ ∃ a', Reduces a a' ∧ K %% a' = b :=
  reduces_comb1_iff # by tauto

theorem S1_reduces_iff {a b} : Reduces (S %% a) b ↔ ∃ a', Reduces a a' ∧ S %% a' = b :=
  reduces_comb1_iff # by tauto

theorem S2_reduces_iff {a b c} : Reduces (S %% a %% b) c ↔
∃ a' b', Reduces a a' ∧ Reduces b b' ∧ S %% a' %% b' = c := by
  symm; constructor
  · rintro ⟨a', b', h₁, h₂, rfl⟩; exact Reduces.app (.app .rfl h₁) h₂
  intro h; generalize hy : S %% a %% b = y at h
  induction h generalizing a b
  any_goals simp at hy
  · subst hy; use a, b
  · nm b c d h₁ h₂ ih₁ ih₂; subst hy; simp at ih₁
    obtain ⟨a', b', ih₁, ih, rfl⟩ := ih₁; simp at ih₂
    obtain ⟨a₁, b₁, ih₂, ih', rfl⟩ := ih₂; simp; tauto
  nm b₁ c₁ d e h₁ h₂ ih₁ ih₂; clear ih₁
  obtain ⟨rfl, rfl⟩ := hy; rw [S1_reduces_iff] at h₁
  obtain ⟨a', h₁, rfl⟩ := h₁; tauto

@[simp, instance]
theorem reduced_K1 {a} [ha : Reduced a] : Reduced (K %% a) := by
  rw [reduced_iff] at ha ⊢; intro b h; rw [K1_reduces_iff] at h
  obtain ⟨a', h, rfl⟩ := h; simp; tauto

@[simp, instance]
theorem reduced_S1 {a} [ha : Reduced a] : Reduced (S %% a) := by
  rw [reduced_iff] at ha ⊢; intro b h; rw [S1_reduces_iff] at h
  obtain ⟨a', h, rfl⟩ := h; simp; tauto

@[simp, instance]
theorem reduced_S2 {a b} [ha : Reduced a] [hb : Reduced b] : Reduced (S %% a %% b) := by
  rw [reduced_iff] at ha hb ⊢; intro b h; rw [S2_reduces_iff] at h
  obtain ⟨a', b', h₁, h₂, rfl⟩ := h; simp; tauto

@[simp, instance]
theorem reduced_I : Reduced I :=
  inferInstanceAs # Reduced # _ %% _

@[simp]
theorem not_exprEq_iff {a b} : ¬ExprEq a b ↔ ExprNe a b := by
  unfold ExprEq; tauto

@[simp]
theorem not_exprNe_iff {a b} : ¬ExprNe a b ↔ ExprEq a b := by
  unfold ExprEq; tauto

@[simp]
theorem I_reduces {a} : Reduces (I %% a) a :=
  .trans .s # .trans .k .rfl

@[simp, instance]
theorem reduced_KI : Reduced KI :=
  inferInstanceAs # Reduced # _ %% _

@[simp]
theorem KI_reduces {a} : Reduces (KI %% a) I :=
  .trans .k .rfl

@[simp]
theorem KI_reduces' {a b} : Reduces (KI %% a %% b) b := by
  apply Reduces.trans (b := I %% b) # .app _ _ <;> simp

@[simp, instance]
theorem reduced_KK : Reduced KK :=
  inferInstanceAs # Reduced # _ %% _

@[simp]
theorem KK_reduces {a} : Reduces (KK %% a) K :=
  .trans .k .rfl

@[simp]
theorem exprNe_KK_I : ExprNe KK I := by
  apply @ExprNe.ext _ _ S K S <;> simp

@[simp]
theorem exprNe_I_KI : ExprNe I KI := by
  apply @ExprNe.ext _ _ KK KK I <;> simp

@[simp]
theorem exprNe_KI_SKIK : ExprNe KI (S %% KI %% K) := by
  apply @ExprNe.ext _ _ I I KI <;> try simp
  apply Reduces.trans .s
  apply Reduces.trans # .app (a' := I) (b' := KI) _ _
  all_goals simp [KI]

@[simp]
theorem exprNe_KKI_SKI : ExprNe (K %% KI) (S %% KI) := by
  apply @ExprNe.ext _ _ K KI (S %% KI %% K) .k .rfl; simp

@[simp]
theorem exprNe_K_KI : ExprNe K KI := by
  apply @ExprNe.ext _ _ K KK I <;> simp; rfl

@[simp]
theorem exprNe_KI_K : ExprNe KI K := by
  apply @ExprNe.ext _ _ S I _ .k .rfl
  apply @ExprNe.ext _ _ K K S <;> simp

theorem exprEq_of_ext {f g} (h : ∀ ⦃x⦄, ExprEq (f %% x) (g %% x)) : ExprEq f g := by
  contrapose! h; simp at h ⊢; induction h; use KI; simp
  · clear f g; nm f g f' g' h₁ h₂ h₃ ih; choose x ih using ih
    use x; exact ExprNe.reduce (.app h₁ .rfl) (.app h₂ .rfl) ih
  · clear f g; nm a b c d e h₁ h₂ h₃ ih; choose x ih using ih
    use c; exact ExprNe.reduce h₁ h₂ h₃

@[simp]
theorem exprNe_S_K : ExprNe S K := by
  apply @ExprNe.ext _ _ KI _ _ .rfl .rfl
  apply @ExprNe.ext _ _ K _ KI .rfl (by simp)
  apply @ExprNe.ext _ _ I KI I _ (by simp) _
  · apply Reduces.trans .s
    apply Reduces.trans # .app (a' := I) (b' := KI) _ .rfl
    all_goals simp
  apply @ExprNe.ext _ _ (K %% S) I (K %% S) .k <;> try simp
  apply @ExprNe.ext _ _ K K S <;> simp

@[symm]
theorem ExprNe.symm {a b} (h : ExprNe a b) : ExprNe b a := by
  induction h; simp
  · clear a b; nm a b a' b' h₁ h₂ h₃ ih
    exact ExprNe.reduce h₂ h₁ ih
  · clear a b; nm a b c x y h₁ h₂ h₃ ih
    exact ExprNe.ext h₂ h₁ ih

@[symm]
theorem ExprEq.symm {a b} (h : ExprEq a b) : ExprEq b a := by
  contrapose h; simp at h ⊢; symm; exact h

theorem ExprNe.comm {a b} : ExprNe a b ↔ ExprNe b a :=
  comm_of_symm ExprNe.symm

theorem ExprEq.comm {a b} : ExprEq a b ↔ ExprEq b a :=
  comm_of_symm ExprEq.symm

theorem exprEq_of_reduces' {a b a' b'} (h₁ : Reduces a a') (h₂ : Reduces b b')
(h₃ : ExprEq a b) : ExprEq a' b' := by
  contrapose h₃; simp at h₃ ⊢; exact ExprNe.reduce h₁ h₂ h₃

-- theorem exprEq_of_reduces {a b a' b'} (h₁ : Reduces a a') (h₂ : Reduces b b')
-- (h₃ : ExprEq a' b') : ExprEq a b := by
--   contrapose h₃; simp at h₃ ⊢
--   induction h₃ generalizing a' b'
--   ·
--     simp at h₁ h₂
--     simp [←h₁, ←h₂]
--   ·
--     clear a b
--     nm a b a₁ b₁ h₃ h₄ h₅ ih

-- #check 0 #exit

-- theorem confluence {a b c} (h₁ : Reduces a b) (h₂ : Reduces a c) :
-- ∃ d, Reduces b d ∧ Reduces c d := by
--   induction h₁ generalizing c; use c
--   ·
--     clear a b
--     nm a b c' h₁ h₃ ih₁ ih₂

-- #check 0 #exit

-- theorem exprEq_of_reduces {a b a' b'} (h₁ : Reduces a a') (h₂ : Reduces b b')
-- (h₃ : ExprEq a' b') : ExprEq a b := by
--   contrapose h₃; simp at h₃ ⊢
--   induction h₃ generalizing a' b'
--   ·
--     simp at h₁ h₂
--     simp [←h₁, ←h₂]
--   ·
--     clear a b
--     nm a b a₁ b₁ h₃ h₄ h₅ ih

-- #check 0 #exit

-- example {a} : ExprEq (S %% K %% a) I := by
--   apply exprEq_of_ext
--   intro x