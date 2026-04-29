import Projects.IndParser.Defs

namespace IndParser

instance : ParType Parser := .par

instance {α : Type*} {β : α → Type} [h : IsEmpty α] (x : α) : ParType (β x) :=
  IsEmpty.false x |>.elim

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

def botSpec : IndSpec where
  tn := 0
  cn := 1
  ts := nofun
  ctns := λ _ => 0
  cts := nofun
  cs := λ bot _ => (.up [bot.down], nofun)

def bot : Parser :=
  botSpec.toParser.down

-- @[simp]
-- theorem words_bot : bot.words = ∅ := by
--   ext x : 1
--   simp [bot, IndSpec.toParser]
--   intro h
--   apply @IndSpec.Ind.rec botSpec (motive := λ _ _ _ => False)
--   ·
--     grind
--   · sorry
--   · sorry

-- #check 0 #exit

def εSpec : IndSpec where
  tn := 0
  cn := 1
  ts := nofun
  ctns := λ _ => 1
  cts := λ _ _ => Parser
  cs := λ _ _ => (λ x => .up [x, x.concat x], nofun)

def ε : Parser :=
  εSpec.toParser.down

-- @[simp]
-- theorem words_ε : ε.words = {.nil} := by
--   ext x : 1
--   simp [ε, εSpec, IndSpec.toParser]