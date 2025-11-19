import AP.RealAnalysis.Coherence

section logic

@[simp]
theorem epsilon_eq_left {α : Type*} {x : α} [ha : Nonempty α] :
Classical.epsilon (λ y => y = x) = x := by
  have := ha.inhabited; apply epsilon_eq_of <;> simp

@[simp]
theorem epsilon_eq_right {α : Type*} {x : α} [ha : Nonempty α] :
Classical.epsilon (λ y => x = y) = x := by
  have := ha.inhabited; apply epsilon_eq_of <;> simp

-- #check 0 #exit

end logic

namespace Finset

variable {α : Type*} [ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : AddLeftMono α]
variable {β : Type*} [hb₁ : LinearOrder β] [hb₂ : Semiring β]
  [hb₃ : AddLeftMono β] [hb₄ : AddLeftReflectLE β]
variable {s : Finset α}

omit ha₂ ha₃ in
theorem le_sum_of_mem {f : α → β} {x : α}
(h₁ : ∀ x ∈ s, 0 ≤ f x) (h₂ : x ∈ s) : f x ≤ ∑ i ∈ s, f i := by
  induction s using Finset.induction
  · simp at h₂
  clear! s
  nm y s h₃ ih
  simp at h₁ h₂
  rcases h₁ with ⟨h₁, h₄⟩
  specialize ih h₄
  rw [sum_insert h₃]
  rcases h₂ with rfl | h₂
  · rw [le_add_iff_nonneg_right]
    exact sum_nonneg h₄
  specialize ih h₂
  apply ih.trans
  rwa [le_add_iff_nonneg_left]

-- #check 0 #exit

end Finset

namespace RealAnalysis

def Rment (σ : ℕ → ℕ) : Prop :=
  σ.Bijective

noncomputable
def rinv (σ : ℕ → ℕ) (n : ℕ) : ℕ :=
  Classical.epsilon # λ k => σ k = n

theorem rment_eq_iff {σ n m} (h : Rment σ) : σ n = σ m ↔ n = m := by
  symm; constructor; rintro rfl; rfl
  intro h₁; exact h.1 h₁

theorem rinv_cancel_left {σ n} (h : Rment σ) : rinv σ (σ n) = n := by
  simp [rinv, rment_eq_iff h]

theorem rinv_cancel_right {σ n} (h : Rment σ) : σ (rinv σ n) = n := by
  unfold rinv
  apply Classical.epsilon_spec (p := λ k => σ k = n)
  apply h.2

theorem rment_rinv {σ} (h : Rment σ) : Rment (rinv σ) := by
  constructor
  · intro n m h₁
    replace h₁ := congrArg σ h₁
    simp_rw [rinv_cancel_right h] at h₁
    exact h₁
  · intro n
    use σ n
    rw [rinv_cancel_left h]

theorem tendsTo_rment_of {a σ L} (h₁ : Rment σ)
(h₂ : tendsTo a L) : tendsTo (a # σ ·) L := by
  intro e he
  dsimp
  specialize h₂ e he
  choose N h₂ using h₂
  dsimp at h₂
  use ∑ i ∈ Finset.range N, rinv σ i + 1
  intro n hn
  apply h₂; clear h₂
  by_contra! h₃
  have h₄ : rinv σ (σ n) ≤ ∑ i ∈ Finset.range N, rinv σ i
  · apply Finset.le_sum_of_mem <;> simp [h₃]
  rw [rinv_cancel_left h₁] at h₄
  omega

theorem tendsTo_rment_iff {a σ L} (h₁ : Rment σ) :
tendsTo (a # σ ·) L ↔ tendsTo a L := by
  symm; use tendsTo_rment_of h₁
  intro h₂
  replace h₂ := tendsTo_rment_of (rment_rinv h₁) h₂
  simp_rw [rinv_cancel_right h₁] at h₂
  exact h₂

theorem converges_rment_of {a σ} (h₁ : Rment σ)
(h₂ : converges a) : converges (a # σ ·) := by
  choose L h₂ using h₂; use L, tendsTo_rment_of h₁ h₂

theorem converges_rment_iff {a σ} (h₁ : Rment σ) :
converges (a # σ ·) ↔ converges a := by
  apply exists_congr; simp [tendsTo_rment_iff h₁]

-- #check 0 #exit

-- series of `a` diverges and it is monotone
-- then for any real `L` there exists a prefix of `a` that is larger than `L`
--   suppose that there exists some `L` that is upper bound of series of `a`
--   since the series is antitone and has upper bound, it converges
--   contradiction

-- series of `a` diverges and it is antitone
-- then for any real `L` there exists a prefix of `a` that is smaller than `L`
--   ditto

-- given sequence `a` of real numbers
-- given that series of `a` is conditionally convergent (series converges, but not absolutely)
-- than for any real `L` there exists a rearrangement of `a` whose series converges to `L`
--   suppose that series of `a` converges to `M`
--   `a` has infinitely many positive elements (for any `N` there exists `n >= N`
--       such that `a n > 0`)
--     suppose the opposite
--     there exists N such that after `N` all elements are nonnpositive
--     drop the first N elements of `a` to obtain sequence `b`
--     `b` is also conditionally convergent
--     absolute series of `b` is equal to `-b`
--     we have that `b` (and hence `-b`) converges, but `-b` (being absolute) diverges
--     contradiction
--   similarly, infinitely many elements of `a` are negative
--   there exists a subsequence of `a` called `a+` that contains exactly positive elements of `a`
--   similarly applies for `a-`
--   series of `a+` is monotone
--   series of `a-` is antitone
--   series of `a+` and series of `a-` cannot both converge
--     suppose that series of `a+` converges to `X`
--     suppose that series of `a-` converges to `-Y`
--     absolute series of `a` is bounded above by `X + Y`
--     since it is monotone and bounded above, it converges
--     contradiction
--   series of `a+` diverges
--     suppose that it converges to some `X`
--     series of `a-` must diverge
--     since series of `a-` diverges and it is antitone,
--       there exists a prefix of `a-` whose sum is smaller than `M - 2 * X - 1`
--     there exists a prefix of `a` whose sum is smaller than `M - X - 1`
--     all subsequent elements of the series of `a` are smaller than `M - 1`
--     therefore series of `a` cannot converge to `M`
--     contradiction
--   similarly `a-` diverges
--   we construct the rearrangement recursively
--     we start from the empty list and the sum `0`
--     in the `n`-th iteration (starting from `n = 0`) we do the following
--       consume the first unconsumed element `x` of `a+`
--       consume the first unconsumed element `y` of `a-`
--       add `x + y` to the current sum
--       let the current sum be `s`
--       let `d = |s - L|`
--       if `s <= L - 1 / (n + 2)`
--         let `N` be the index in `a+` after which all elements are smaller than `1 / (n + 2)`
--           and all elements are unconsumed
--         consume the shortest prefix of `a+` starting from `N`
--           whose sum is larger than `L - 1 / (n + 2)`
--         the new total sum will be between `L - 1 / (n + 2)` and `L` inclusively
--       if `s >= L + 1 / (n + 2)`
--         ditto
--       let `s` be the new sum
--       we now have `|s - L| < 1 / (n + 1)`
--     the `n`-th element of the rearrangement is obtained by constructing the list
--       in `n + 1` iterations and taking the `n`-th element
--     let `f : N -> N` be a function that maps `n` to the index representing the
--       end of the `n`-th generation
--     for all `n`, sum of rearrangement of `a` up to `f n` (inclusively) is
--       at distance from `L` at most `1 / (n + 1)`
--     elements of series of rearrangement of `a` between `f n` and `f (n + 1)`
--       are at distance from `L` at most `2 * |a n| + 1 / (n + 1)`
--     moreover, all elements or series of rearrangement of `a` after `f n`
--       are at distance from `L` at most `2 * |a n| + 1 / (n + 1)`
--     since `a` tends to `0` and `1 / (n + 1)` also tends to `0`,
--       the series of rearrangement of `a` tends to `L`