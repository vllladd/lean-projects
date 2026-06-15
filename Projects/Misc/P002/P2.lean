import Projects.Util

namespace Misc.P002.P2

def CndX (n : ℕ) : Prop :=
  n.Prime ∧ ∃ (a b : ℕ), a.Prime ∧ b.Prime ∧ n = a + b ∧ n = (a : ℤ) - b

def Cnd₁ (n : ℕ) : Prop :=
  n.Prime ∧
  (∃ (a b : ℕ), a.Prime ∧ b.Prime ∧ n = a + b) ∧
  (∃ (a b : ℕ), a.Prime ∧ b.Prime ∧ n = (a : ℤ) - b)

def setX : Set ℕ :=
  setOf CndX

def set₁ : Set ℕ :=
  setOf Cnd₁

noncomputable
def n₁ : ℕ :=
  τ n, Cnd₁ n

-----

theorem cnd₁_of_cndX {n} (h : CndX n) : Cnd₁ n := by
  unfold CndX at h; unfold Cnd₁; tauto

@[simp]
theorem setX_eq : setX = ∅ := by
  ext n; simp [setX, CndX]
  intro h₁ a ha b hb rfl h₂
  rw [eq_sub_iff_add_eq] at h₂
  norm_cast at h₂
  replace h₂ : b = 0; omega
  simp [h₂] at hb

@[simp]
theorem set₁_eq : set₁ = {5} := by
  ext n
  simp only [set₁, Set.mem_setOf_eq, Cnd₁, Set.mem_singleton_iff]
  symm; constructor
  · rintro rfl
    use by norm_num
    split_ands
    · use 2, 3; decide
    · use 7, 2; decide
  rintro ⟨h₁, ⟨a, b, ha, hb, h₂⟩, ⟨c, d, hc, hd, h₃⟩⟩
  rw [eq_sub_iff_add_eq] at h₃
  norm_cast at h₃
  symm at h₂
  revert h₁ h₂ h₃; revert ha hb
  revert n; revert a b
  rw [Nat.prime_add_prime_iff (by tauto)]
  intro a n ha hn h₁ h₂ h₃
  have h₄ : Odd n; simpa [←h₂]
  have h₅ : Even d
  · by_contra h₅; simp at h₅
    replace h₅ : Even c
    · rw [←h₃]; exact h₄.add_odd h₅
    rw [hc.even_iff] at h₅
    subst h₂ h₅
    replace h₃ : a = 0; omega
    simp [h₃] at ha
  rw [hd.even_iff] at h₅
  subst h₅
  subst h₂ h₃
  simp [add_assoc] at hc
  clear hd h₄
  simp
  rename' a => n
  obtain h₂ | h₂ | h₂ := n.three_dvd_add_two_four
  · exact Nat.eq_of_prime_and_dvd (by norm_num) ha h₂
  · have h := Nat.eq_of_prime_and_dvd (by norm_num) hn h₂
    simp at h; simp [h] at ha
  · have h := Nat.eq_of_prime_and_dvd (by norm_num) hc h₂
    simp at h

@[simp]
theorem n₁_eq : n₁ = 5 := by
  apply τ_eq_of_setOf; rw [←set₁]; simp