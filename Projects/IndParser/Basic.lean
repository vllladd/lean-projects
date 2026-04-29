import Projects.IndParser.Defs

namespace IndParser

instance : ParType Parser := .par

instance {α : Type*} {β : α → Type} [h : IsEmpty α] (x : α) : ParType (β x) :=
  IsEmpty.false x |>.elim

def botSpec : IndSpec where
  tn := 0
  cn := 1
  ts := nofun
  ctns := λ _ => 0
  cts := nofun
  cs := λ bot _ => (.up [bot.down], nofun)

def bot : Parser :=
  botSpec.toParser.down

def εSpec : IndSpec where
  tn := 0
  cn := 1
  ts := nofun
  ctns := λ _ => 1
  cts := λ _ _ => Parser
  cs := λ _ _ => (λ x => .up [x, x.concat x], nofun)

def ε : Parser :=
  εSpec.toParser.down

-- #check 0 #exit

-----

@[simp]
theorem mkFinFn_zero.{u, v} {α : Fin 0 → Type u} {β : Type v}
{f : (∀ n, α n) → β} : mkFinFn f = .up (f nofun) := rfl

@[simp]
theorem mkFinFn_succ.{u, v} {n} {α : Fin (n + 1) → Type u} {β : Type v}
{f : (∀ n, α n) → β} : mkFinFn f = λ (x : α 0) => @mkFinFn n
(λ ⟨k, h⟩ => α ⟨k + 1, by omega⟩) β (λ ps₁ => f # λ ⟨k, hk⟩ =>
match k with | 0 => x | k + 1 => ps₁ ⟨k, by omega⟩) := by
  funext x; congr; ext ps; dsimp; congr; ext k
  rcases k with ⟨⟨⟩ | _, hk⟩ <;> rfl

@[simp]
theorem callFinFn_mkFinFn.{u, v} {n : ℕ} {α : Fin n → Type u} {β : Type v}
{f : (∀ n, α n) → β} {ps : ∀ n, α n} : callFinFn (mkFinFn f) ps = f ps := by
  induction n
  · dsimp [callFinFn, mkFinFn]
    congr; ext n; rcases n with ⟨n, h⟩; simp at h
  nm n ih; simp [callFinFn]
  specialize @ih (λ ⟨k, h⟩ => α ⟨k + 1, by omega⟩) _ _
  · exact λ ps₁ => f λ ⟨k, hk⟩ => match k with
    | 0 => ps 0
    | k + 1 => ps₁ ⟨k, by omega⟩
  · exact λ ⟨k, hk⟩ => ps ⟨k + 1, by omega⟩
  convert ih using 2; ext k; rcases k with ⟨⟨⟩ | _, h⟩ <;> rfl

@[simp]
theorem callFinFn_zero.{u, v} {α : Fin 0 → Type u} {β : Type v} {ps} {r : β} :
callFinFn (α := α) ⟨r⟩ ps = r := rfl

@[simp]
theorem finFn_zero.{u, v} {α : Fin 0 → Type u} {β : Type v} :
FinFn α β = ULift.{max u v + 1} β := rfl

@[simp] theorem Word.xs_eps : eps.xs = [] := rfl
@[simp] theorem Word.xs_concat {a b : Word} : (a.concat b).xs = a.xs ++ b.xs := rfl
@[simp] theorem Parser.words_bot : Parser.bot.words = ∅ := rfl
@[simp] theorem Parser.words_eps : Parser.eps.words = {.eps} := rfl
@[simp] theorem Parser.words_univ : Parser.univ.words = .univ := rfl
@[simp] theorem Parser.words_inter {a b : Parser} : (a.inter b).words = a.words ∩ b.words := rfl

@[simp]
theorem Parser.words_concat {a b : Parser} : (a.concat b).words =
{w | ∃ w₁ ∈ a.words, ∃ w₂ ∈ b.words, w₁.concat w₂ = w} := rfl

@[simp]
theorem Word.eps_concat {a : Word} : eps.concat a = a := by
  ext; simp

@[simp]
theorem Word.concat_eps {a : Word} : a.concat eps = a := by
  ext; simp

@[simp]
theorem Parser.eps_concat {a : Parser} : eps.concat a = a := by
  ext; simp

@[simp]
theorem Parser.concat_eps {a : Parser} : a.concat eps = a := by
  ext; simp

-- #check 0 #exit

-----

@[simp]
theorem bot_eq : bot = .bot := by
  ext x : 2
  simp [bot, IndSpec.toParser]
  intro h
  apply @IndSpec.Ind.rec botSpec (motive := λ _ _ _ => False)
  on_goal 2 => exact h
  rintro n ps xs ys part ind w h₁ h₂ rfl rfl h₃ ih
  simp [botSpec] at ind
  rcases ind with ⟨⟨ind⟩⟩
  simp [botSpec] at h₃
  simp at h₂
  subst h₂
  simp at h₃
  exact ih _ w h₃

-- @[simp]
-- theorem ε_eq : ε = .eps := by
--   ext x : 2
--   simp [ε, IndSpec.toParser]
--   symm; constructor
--   ·
--     rintro rfl
--     have h := @IndSpec.Ind.mk εSpec
--     simp only [εSpec, finFn_zero, Fin.forall_fin_zero_pi, mkFinFn_zero, ULift.forall,
--       ULift.up.injEq, forall_const] at h
--     specialize h (λ _ => .eps) [.eps, .eps] (λ _ _ => False) .bot .eps
--     simp only [IsEmpty.forall_iff, implies_true, Set.setOf_false, List.foldr_cons,
--       List.foldr_nil, Parser.words_inter, Parser.words_eps, Parser.words_univ,
--       Set.inter_univ, Set.inter_self, Set.mem_singleton_iff, forall_const] at h
--     specialize h rfl
--     simp only [callFinFn, Parser.concat_eps, forall_const] at h
--     specialize h (funext # by simp)
--     convert h
--   sorry