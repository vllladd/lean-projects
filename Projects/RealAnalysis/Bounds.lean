import Projects.RealAnalysis.Subsequence

namespace RealAnalysis

noncomputable
def bounds (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  lub |(a # n + ·)|

-----

theorem bounds_le_bounds_of_tendsTo {a L k n}
(h₁ : tendsTo a L) (h₂ : k ≤ n) : bounds a n ≤ bounds a k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₂; clear h₂
  unfold bounds lub iSup
  apply csSup_le_csSup
  · apply bddAbove_of_converges
    apply converges_of_tendsTo (L := |L|)
    apply tendsTo_abs
    exact tendsTo_drop_of h₁
  · apply Set.range_nonempty
  dsimp; intro i; simp; intro j h₂; use n + j; grind

theorem bounds_le_bounds_of_converges {a k n}
(h₁ : converges a) (h₂ : k ≤ n) : bounds a n ≤ bounds a k := by
  choose L h₁ using h₁; exact bounds_le_bounds_of_tendsTo h₁ h₂

theorem abs_le_bounds_of_tendsTo {a L n} (h : tendsTo a L) : |a n| ≤ bounds a n := by
  apply le_csSup
  · apply bddAbove_of_converges
    apply converges_of_tendsTo (L := |L|)
    apply tendsTo_abs
    exact tendsTo_drop_of h
  simp; use 0

theorem abs_le_bounds_of_converges {a n} (h : converges a) : |a n| ≤ bounds a n := by
  choose L h using h; exact abs_le_bounds_of_tendsTo h

theorem tendsTo_lub_seq_of_nonneg {a L} (h₁ : tendsTo a L) :
tendsTo (λ n => lub # (a # n + ·)) L := by
  intro e he
  dsimp
  suffices h : eventually # λ n => lub (a # n + · ) - L < e
  · choose N h using h
    use N
    intro n hn
    specialize h n hn
    rwa [abs_of_nonneg]
    simp
    apply le_lub_of_tendsTo _ |>.2
    exact tendsTo_drop_of h₁
  simp_rw [sub_lt_iff_lt_add']
  specialize h₁ (e / 2) (by positivity)
  choose N h₁ using h₁
  use N
  intro n hn
  dsimp at h₁
  simp_rw [abs_sub_lt_iff'] at h₁
  choose h₂ h₁ using h₁; clear h₂
  replace h₁ : ∀ k, (a # n + ·) k < L + e / 2
  · dsimp; intro k; exact h₁ (n + k) (by omega)
  apply lt_of_le_of_lt (b := L + e / 2)
  rotate_left; linarith
  apply csSup_le # Set.range_nonempty _
  simp at h₁ ⊢
  intro k; exact le_of_lt # h₁ k

theorem tendsTo_bounds_of_tendsTo {a L} (h : tendsTo a L) : tendsTo (bounds a) |L| :=
  @tendsTo_lub_seq_of_nonneg |a| |L| # tendsTo_abs h

@[simp]
theorem bounds_abs {a} : bounds |a| = bounds a := by
  ext; unfold bounds; congr 1; ext; simp

theorem bounds_nonneg_of_tendsTo {a L n} (h : tendsTo a L) : 0 ≤ bounds a n := by
  trans |L|; simp
  replace h := tendsTo_drop_of (k := n) # tendsTo_abs h
  exact le_lub_of_tendsTo h |>.2

theorem bounds_nonneg_of_converges {a n} (h : converges a) : 0 ≤ bounds a n := by
  choose L h using h; exact bounds_nonneg_of_tendsTo h

theorem abs_bounds_of_tendsTo {a L n} (h : tendsTo a L) : |bounds a n| = bounds a n := by
  apply abs_of_nonneg; exact bounds_nonneg_of_tendsTo h

theorem abs_bounds_of_converges {a n} (h : converges a) : |bounds a n| = bounds a n := by
  choose L h using h; exact abs_bounds_of_tendsTo h

theorem monoGe_bounds_of_tendsTo {a L} (h : tendsTo a L) : monoGe (bounds a) :=
  λ _ _ h₁ => bounds_le_bounds_of_tendsTo h h₁

theorem monoGe_bounds_of_converges {a} (h : converges a) : monoGe (bounds a) :=
  λ _ _ h₁ => bounds_le_bounds_of_converges h h₁

@[simp]
theorem bounds_neg {a} : bounds (-a) = bounds a := by
  ext n; unfold bounds; simp; change lub |-_| = _; rw [abs_neg]