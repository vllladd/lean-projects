import Projects.Util

namespace Misc.Seq1

open Classical in noncomputable
def seq₁ : ℕ → ℕ :=
  τ a, a 0 = 1 ∧ ∀ n, n ≠ 0 →
  a n = (List.range n |>.map a |>.filter (¬n ∣ ·) |>.sum)

open Classical in noncomputable
def N₁ : ℕ :=
  seq₁ # Nat.find! λ i => let n := seq₁ i; 0 < n ∧ ∀ k, 2 ^ k ≠ n

-----

def seq₁Comp (n : ℕ) : ℕ :=
  if n = 0 then 1 else
  List.range n |>.attach |>.map (λ x => seq₁Comp x.1) |>.filter (¬n ∣ ·) |>.sum
decreasing_by grind

def N₁Comp : ℕ := 72

-----

@[simp]
theorem seq₁Comp_zero : seq₁Comp 0 = 1 := by
  simp [seq₁Comp]

@[simp]
theorem seq₁Comp_eq_seq₁ : seq₁Comp = seq₁ := by
  unfold seq₁; symm
  apply τ_eq_of
  · simp
    intro n hn
    unfold seq₁Comp
    simp [hn]
  rintro a ⟨h₁, h₂⟩
  funext n
  symm
  induction n using Nat.strong_induction_on
  nm n ih
  cases n
  · simp [h₁]
  nm n
  unfold seq₁Comp
  simp [h₂]
  congr 2
  rw [List.map_eq_map_iff]
  simp
  grind

@[csimp]
theorem seq₁_eq_seq₁Comp : seq₁ = seq₁Comp := by
  simp

theorem map_seq₁_range_10 : (List.range 10).map seq₁ = [1, 0, 1, 2, 4, 8, 16, 32, 8, 72] := by
  rw [seq₁_eq_seq₁Comp]; cbv

@[simp]
theorem seq₁_9 : seq₁ 9 = 72 := by
  rw [seq₁_eq_seq₁Comp]; cbv

@[simp]
theorem N₁Comp_eq : N₁Comp = 72 := rfl

@[simp]
theorem N₁_eq : N₁ = 72 := by
  rw [N₁, Nat.find!_eq_of (n := 9)] <;> simp; decide_cbv
  suffices h : ∀ n ∈ (List.range 9).map seq₁, 0 < n → n.powTwo
  · simpa using h
  have h : List.range 9 = (List.range 10).init
  · nth_rw 2 [List.range_succ]; simp
  rw [h]; clear h
  rw [List.map_init, map_seq₁_range_10]
  decide_cbv

@[csimp]
theorem N₁_eq_N₁Comp : N₁ = N₁Comp := by
  simp