import Projects.Util.Logic

theorem Quot.lift_mk_of {α : Type*} {P : α → α → Prop} {f : α → Prop} {a} (h₁)
(h₂ : (∀ (a₁ a₂ : α), P a₁ a₂ → f a₁ = f a₂) → f a) :
Quot.lift f h₁ (Quot.mk P a) := h₂ h₁

theorem Setoid.comm {α : Type*} (s : Setoid α) {x y : α} : s x y ↔ s y x := by
  rcases s with ⟨r, h₁, h₂, h₃⟩
  exact ⟨h₂, h₂⟩

theorem Setoid.commFn {α : Type*} (s : Setoid α) : s = λ x y => s y x := by
  ext x y; exact s.comm

theorem liftWith_aux₁ {α β : Type*} {s : Setoid α} {f : α → β} {x y : α}
(h : x ≈ y) : HEq (λ (_ : ∀ (a b : α), s (Quotient.mk s x).out a →
s (Quotient.mk s x).out b → f a = f b) => f x) (λ (_ : ∀ (a b : α),
s (Quotient.mk s y).out a → s (Quotient.mk s y).out b → f a = f b) => f y)
:= by
  apply Function.hfunext <;> simp_rw [s.comm]
  · simp
    rw [forall_congr]; intro a
    rw [forall_congr]; intro b
    ext
    constructor
    all_goals
      intro h₁ h₂ h₃
      apply h₁
      all_goals
        first | apply s.trans h₂ | apply s.trans h₃
        apply Quotient.out_equiv_out.mpr
        apply Quotient.sound
        first | exact s.symm h | exact h
  intro h₁ h₂ h₃
  clear h₂ h₃
  simp
  have h₂ : s (Quotient.mk s x).out (Quotient.mk s y).out :=
    by
      apply Quotient.out_equiv_out.mpr
      exact Quotient.sound h
  apply h₁ x y
  · apply s.symm
    exact Quotient.eq_mk_iff_out.mp rfl
  · apply s.symm
    apply Quotient.eq_mk_iff_out.mp
    exact Quotient.sound h

def Quotient.liftWith {α β : Type*} {s : Setoid α} (q : Quotient s) (f : α → β)
(h : ∀ (x y : α), s q.out x → s q.out y → f x = f y) : β := by
  induction q using Quotient.hrecOn
  · nm x; use f x
  nm x y h; exact liftWith_aux₁ h

theorem Quotient.apply_of {α : Type*} [s : Setoid α]
{p : α → Prop} {q : Quotient s} {h} :
p q.out ↔ q.lift p h := by
  unfold Quotient.out Quot.out
  generalize_proofs h₁
  have h₂ := h₁.choose_spec
  nth_rw 2 [←h₂]

@[simp]
theorem Quotient.mk_out_eq {α : Type*} {s : Setoid α} {q : Quotient s} :
Quot.mk s q.out = q := by
  have h := @Quotient.out_equiv_out α s (Quot.mk s q.out) q
  unfold Quotient at h; rw [←h, ←Quotient.eq_mk_iff_out]; rfl

theorem Quotient.eq_mk_out {α : Type*} {s : Setoid α} {q : Quotient s} :
q = Quot.mk s q.out := by simp

theorem Quotient.mk_eq_mk {α : Type*} {s : Setoid α} {x y} :
Quotient.mk s x = Quotient.mk s y ↔ s x y := by rw [Quotient.eq'']

theorem Quot.mk_eq_mk {α : Type*} {s : Setoid α} {x y} :
Quot.mk s x = Quot.mk s y ↔ s x y := Quotient.mk_eq_mk

@[simp]
theorem Quot.mk_out_equiv {α : Type*} {s : Setoid α} {x} : s (mk s x).out x := by
  apply Quotient.mk_out

@[simp]
theorem Quot.equiv_mk_out {α : Type*} {s : Setoid α} {x} : s x (mk s x).out := by
  symm; exact mk_out_equiv

def quot_aux₁ {α : Type*} {β : α → Type*} {s : Setoid α}
{f : (i : α) → β i} (h : ∀ (x y : α), s x y → HEq (f x) (f y)) (x) :
β x = β (Quot.mk s x).out :=
  type_eq_of_heq # h x (Quot.mk s x).out Quot.equiv_mk_out

def quot_aux₂ {α : Type*} {β : α → Type*} {s : Setoid α}
{f : (i : α) → β i} (h : ∀ (x y : α), s x y → HEq (f x) (f y)) :
∀ (a b : α) (p : s a b), Quot.sound p ▸
  (λ x => cast (quot_aux₁ h x) (f x)) a =
  (λ x => cast (quot_aux₁ h x) (f x)) b
:= by
  intro x y h₁
  specialize h x y h₁
  rw [eq_cast_iff_heq]
  simpa

theorem Quot.rec_eq_apply_out {α : Type*} {β : α → Type*}
{s : Setoid α} {q : Quot s} {f : (i : α) → β i}
(h : ∀ (x y : α), s x y → HEq (f x) (f y)) :
Quot.rec (λ x => cast (quot_aux₁ h x) (f x)) (quot_aux₂ h) q = f q.out := by
  unfold Quot.rec Eq.ndrecOn Quot.indep
  revert h
  simp
  intro h
  unfold Quot.out
  generalize_proofs h₁ h₂ h₃ h₄ h₅ h₆
  have h₇ := h₁.choose_spec
  obtain ⟨w, rfl⟩ := h₁
  dsimp
  generalize_proofs h₈ h₉ at h₄ ⊢
  rw [mk_eq_mk] at h₇
  generalize_proofs at h₇
  specialize h _ _ h₇
  symm at h
  clear! h₂ h₃ h₇ h₉
  apply eq_of_heq
  trans f w; simp; exact h

theorem Quot.ndrec_eq_apply_out {α β : Type*} {s : Setoid α} {q : Quot s}
{f : α → β} {h} : q.rec f h = f q.out := by
  apply @rec_eq_apply_out α (λ _ => β)
  simp at h ⊢; exact h

theorem Quotient.rec_eq_apply_out {α : Type*} {β : α → Type*}
{s : Setoid α} {q : Quotient s} {f : (i : α) → β i}
(h : ∀ (x y : α), s x y → HEq (f x) (f y)) :
Quotient.rec (λ x => cast (quot_aux₁ h x) (f x)) (quot_aux₂ h) q = f q.out :=
  Quot.rec_eq_apply_out h

theorem Quotient.ndrec_eq_apply_out {α β : Type*} {s : Setoid α} {q : Quotient s}
{f : α → β} {h} : q.rec f h = f q.out := by
  apply Quot.ndrec_eq_apply_out; exact h

@[simp]
theorem Quot.mk_out_equiv_iff {α : Type*} {s : Setoid α} {x y} :
s (mk s x).out y ↔ s x y := by
  constructor <;> intro h
  · exact s.trans' equiv_mk_out h
  · apply s.trans' mk_out_equiv h

@[simp]
theorem Quot.equiv_mk_out_iff {α : Type*} {s : Setoid α} {x y} :
s x (mk s y).out ↔ s x y := by
  constructor <;> intro h
  · exact s.trans' h mk_out_equiv
  · apply s.trans' h equiv_mk_out

def liftWith_aux₂ {α β : Type*} {s : Setoid α} (q : Quotient s) (f : α → β)
(h : ∀ (x y : α), s x q.out → s y q.out → f x = f y) : β := by
  induction q using Quotient.hrecOn
  · nm x
    use f x
  nm x y h
  have h₁ := liftWith_aux₁ (f := f) h
  rwa [s.commFn]

@[simp]
theorem liftWith_aux₃ {α β : Type*} {s : Setoid α} {q : Quotient s}
{f : α → β} {h : ∀ (x y : α), s x q.out → s y q.out → f x = f y} :
liftWith_aux₂ q f h = f q.out := by
  classical
  unfold liftWith_aux₂ Quotient.hrecOn Quot.hrecOn Quot.recOn
  generalize_proofs h₁ h₂ h₃
  apply congrFun
  have h₄ := @Quot.rec_eq_apply_out
  specialize @h₄
    α (β := λ a => (∀ (x y : α), s x a →
    s y a → f x = f y) → β) s q
    (λ a h => f a) _
  · clear h₄
    intro x y hx
    apply Function.hfunext
    · ext
      rw [forall_congr]; intro a
      rw [forall_congr]; intro b
      ext
      constructor <;> intro h₄ h₅ h₆ <;> apply h₄ <;>
        (apply s.trans' # by assumption) <;>
        first | exact hx | exact s.symm' hx
    · intro h₄ h₅ h₆
      clear h₆
      rw [heq_eq_eq]
      specialize h₄ x y
      exact h₄ (s.refl' _) # s.symm' hx
  unfold Quotient.out
  dsimp at h₄ ⊢
  convert h₄
  nm x h₅
  generalize_proofs h₆
  symm
  apply congrFun
  apply cast_eq_iff_heq.mpr
  apply @heq_fn α β α f # λ z =>
    ∀ (x y : α), s x z → s y z → f x = f y
  simp [Quotient.mk]

@[simp]
theorem Quotient.liftWith_eq {α β : Type*} {s : Setoid α} {q : Quotient s}
{f : α → β} {h : ∀ (x y : α), s q.out x → s q.out y → f x = f y} :
q.liftWith f h = f q.out := by
  classical
  unfold liftWith
  have h₁ := h
  simp_rw [s.comm] at h₁
  have h₂ := liftWith_aux₃ (f := f) (q := q) (h := h₁)
  unfold liftWith_aux₂ at h₂
  generalize_proofs h₃
  revert h h₃
  rw [s.commFn]
  dsimp
  intro h h₃
  exact h₂

theorem Quotient.lift_eq {α β : Type*} {s : Setoid α} {q : Quotient s}
{f : α → β} {h : ∀ (x y : α), s x y → f x = f y} : q.lift f h = f q.out := by
  classical
  apply q.ind
  clear q
  intro x
  simp
  apply h
  exact s.symm # mk_out x

@[simp]
theorem Quotient.out_equiv {α : Type*} {s : Setoid α} {x : α} :
(⟦x⟧ : Quotient s).out ≈ x := by rw [←eq_mk_iff_out]

@[simp]
theorem Quotient.equiv_out {α : Type*} {s : Setoid α} {x : α} :
x ≈ (⟦x⟧ : Quotient s).out := s.symm' out_equiv

theorem Quotient.apply_lift {α β γ : Type*} {s : Setoid α} {q : Quotient s}
{f : β → γ} {g : α → β} {h₁} (h₂ : ∀ a b, a ≈ b → f (g a) = f (g b)) :
f (q.lift g h₁) = q.lift (f ∘ g) h₂ := by
  apply q.ind; intros; rfl

attribute [simp] Quotient.eq_iff_equiv