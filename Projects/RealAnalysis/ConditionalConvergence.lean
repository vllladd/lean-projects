import Projects.RealAnalysis.Bounds

namespace RealAnalysis

def CondConv (a : ℕ → ℝ) : Prop :=
  converges (series a) ∧ ¬AbsConv a

namespace CondConv

noncomputable
def σp (a : ℕ → ℝ) : ℕ → ℕ :=
  mkSubseq a (0 ≤ ·)

noncomputable
def σn (a : ℕ → ℝ) : ℕ → ℕ :=
  mkSubseq a (· < 0)

noncomputable
def ap (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a # σp a n

noncomputable
def an (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a # σn a n

noncomputable
def M (a : ℕ → ℝ) : ℝ :=
  limit # series a

def fgCnd (F : ℝ → ℝ) (a : ℕ → ℝ) (f g : ℕ → ℕ) : Prop :=
  (∀ (n : ℕ), f n + g n = n) ∧ (∀ (i j : ℕ), i ≤ j → f i ≤ f j) ∧
  (∀ (i j : ℕ), i ≤ j → g i ≤ g j) ∧ (∀ (n : ℕ), ∃ k, n ≤ f k) ∧ (∀ (n : ℕ), ∃ k, n ≤ g k) ∧
  ∀ (n : ℕ), series (F # a ·) n = series (F # ap a ·) (f n) + series (F # an a ·) (g n)

noncomputable
def fAux (F : ℝ → ℝ) (a : ℕ → ℝ) : ℕ → ℕ :=
  τ f, ∃ g, fgCnd F a f g

noncomputable
def gAux (F : ℝ → ℝ) (a : ℕ → ℝ) : ℕ → ℕ :=
  τ g, fgCnd F a (fAux F a) g

noncomputable
def f (a : ℕ → ℝ) : ℕ → ℕ :=
  fAux id a

noncomputable
def g (a : ℕ → ℝ) : ℕ → ℕ :=
  gAux id a

noncomputable
def f' (a : ℕ → ℝ) : ℕ → ℕ :=
  fAux abs a

noncomputable
def g' (a : ℕ → ℝ) : ℕ → ℕ :=
  gAux abs a

-----

variable {a : ℕ → ℝ} (H : CondConv a)
include H

theorem converges_series : converges (series a) := H.1
theorem not_absConv : ¬AbsConv a := H.2

theorem drop {N} : CondConv (a # N + ·) := by
  unfold CondConv at H ⊢; rwa [converges_series_drop_iff, absConv_drop_iff]

omit H in
theorem drop_iff {N} : CondConv (a # N + ·) ↔ CondConv a := by
  unfold CondConv; rw [converges_series_drop_iff, absConv_drop_iff]

omit H in
theorem neg_iff : CondConv (-a) ↔ CondConv a := by
  unfold CondConv; rw [←neg_series', converges_neg, absConv_neg]

theorem infp_pos : Infp a (0 < ·) := by
  intro N
  by_contra! h₃
  generalize hb : (a # N + ·) = b
  have h₄ : CondConv b; rwa [←hb, drop_iff]
  have h₅ : |b| = -b
  · subst hb
    rw [abs_of_nonpos]
    intro n
    apply h₃
    simp
  have h₆ := h₄.1
  have h₇ : ¬converges (series b)
  · rw [←converges_neg, neg_series', ←h₅]; exact h₄.2
  contradiction

theorem infp_neg : Infp a (· < 0) := by
  intro N; rw [←neg_iff] at H
  have h₁ := infp_pos H N
  simp at h₁; exact h₁

theorem infp_nonneg : Infp a (0 ≤ ·) := by
  apply infp_of_imp (infp_pos H); intro n; apply le_of_lt

theorem infp_nonpos : Infp a (· ≤ 0) := by
  apply infp_of_imp (infp_neg H); intro n; apply le_of_lt

omit H in
theorem subseq_σp (a : ℕ → ℝ) : Subseq (σp a) :=
  subseq_mkSubseq

omit H in
theorem subseq_σn (a : ℕ → ℝ) : Subseq (σn a) :=
  subseq_mkSubseq

theorem tendsTo_series : tendsTo (series a) (M a) :=
  tendsTo_limit_of_converges H.converges_series

theorem σp_spec {n : ℕ} : 0 ≤ a n ↔ ∃ k, σp a k = n :=
  apply_iff_exi_mkSubseq_eq H.infp_nonneg

theorem σn_spec {n : ℕ} : a n < 0 ↔ ∃ k, σn a k = n :=
  apply_iff_exi_mkSubseq_eq H.infp_neg

theorem σp_spec' : ∀ n, 0 ≤ a n ↔ ∃ k, σp a k = n :=
  λ _ => H.σp_spec

theorem σn_spec' : ∀ n, a n < 0 ↔ ∃ k, σn a k = n :=
  λ _ => H.σn_spec

theorem ap_nonneg {n : ℕ} : 0 ≤ ap a n :=
  H.σp_spec.mpr ⟨_, rfl⟩

theorem an_neg {n : ℕ} : an a n < 0 :=
  H.σn_spec.mpr ⟨_, rfl⟩

theorem an_nonpos {n : ℕ} : an a n ≤ 0 :=
  le_of_lt H.an_neg

theorem ap_fn_nonneg : 0 ≤ ap a :=
  λ _ => H.ap_nonneg

theorem an_fn_neg : an a < 0 := by
  rw [Pi.lt_def]; use λ _ => H.an_nonpos; use 0, H.an_neg

theorem an_fn_nonpos : an a ≤ 0 :=
  le_of_lt H.an_fn_neg

theorem abs_ap {n} : |ap a n| = ap a n :=
  abs_of_nonneg H.ap_nonneg

theorem abs_an {n} : |an a n| = -an a n :=
  abs_of_neg H.an_neg

theorem abs_ap_fn : |ap a| = ap a :=
  abs_of_nonneg # H.ap_fn_nonneg

theorem abs_an_fn : |an a| = -an a :=
  abs_of_neg # H.an_fn_neg

theorem series_ap_nonneg {n : ℕ} : 0 ≤ series (ap a) n :=
  Finset.sum_nonneg # λ _ _ => H.ap_nonneg

theorem series_an_nonpos {n : ℕ} : series (an a) n ≤ 0 :=
  Finset.sum_nonpos # λ _ _ => H.an_nonpos

theorem series_ap_fn_nonneg : 0 ≤ series (ap a) :=
  λ _ => H.series_ap_nonneg

theorem series_an_fn_nonpos : series (an a) ≤ 0 :=
  λ _ => H.series_an_nonpos

theorem exi_fgCnd {F} : ∃ f g, fgCnd F a f g := by
  obtain ⟨f, g, hfg, hf, hg, Hf, Hg, Hfg⟩ :=
    exi_fn_series_of_subseq_cover (F := F) (subseq_σp a) (subseq_σn a)
    H.σp_spec' # by simp; exact H.σn_spec'
  use f, g, hfg, hf, hg, Hf H.infp_nonneg, Hg # by simp [H.infp_neg], Hfg

theorem fgCnd_fAux_gAux {F} : fgCnd F a (fAux F a) (gAux F a) :=
  τ_spec # τ_spec H.exi_fgCnd

theorem fAux_add_gAux {F n} : fAux F a n + gAux F a n = n :=
  H.fgCnd_fAux_gAux.1 n

theorem fAux_le_of_le {F i j} (h : i ≤ j) : fAux F a i ≤ fAux F a j :=
  H.fgCnd_fAux_gAux.2.1 i j h

theorem gAux_le_of_le {F i j} (h : i ≤ j) : gAux F a i ≤ gAux F a j :=
  H.fgCnd_fAux_gAux.2.2.1 i j h

theorem exi_fAux_ge {F n} : ∃ k, n ≤ fAux F a k :=
  H.fgCnd_fAux_gAux.2.2.2.1 n

theorem exi_gAux_ge {F n} : ∃ k, n ≤ gAux F a k :=
  H.fgCnd_fAux_gAux.2.2.2.2.1 n

theorem series_eq_fAux_add_gAux {F n} : series (F # a ·) n =
series (F # ap a ·) (fAux F a n) + series (F # an a ·) (gAux F a n) :=
  H.fgCnd_fAux_gAux.2.2.2.2.2 n

theorem fgCnd_f_g : fgCnd id a (f a) (g a) :=
  H.fgCnd_fAux_gAux

theorem f_add_g {n} : f a n + g a n = n :=
  H.fAux_add_gAux

theorem f_le_of_le {i j} (h : i ≤ j) : f a i ≤ f a j :=
  H.fAux_le_of_le h

theorem g_le_of_le {i j} (h : i ≤ j) : g a i ≤ g a j :=
  H.gAux_le_of_le h

theorem exi_f_ge {n} : ∃ k, n ≤ f a k :=
  H.exi_fAux_ge

theorem exi_g_ge {n} : ∃ k, n ≤ g a k :=
  H.exi_gAux_ge

theorem series_eq_f_add_g {n} : series a n =
series (ap a) (f a n) + series (an a) (g a n) := by
  convert! H.series_eq_fAux_add_gAux <;> rfl

theorem fgCnd_f'_g' : fgCnd abs a (f' a) (g' a) :=
  H.fgCnd_fAux_gAux

theorem f'_add_g' {n} : f' a n + g' a n = n :=
  H.fAux_add_gAux

theorem f'_le_of_le {i j} (h : i ≤ j) : f' a i ≤ f' a j :=
  H.fAux_le_of_le h

theorem g'_le_of_le {i j} (h : i ≤ j) : g' a i ≤ g' a j :=
  H.gAux_le_of_le h

theorem exi_f'_ge {n} : ∃ k, n ≤ f' a k :=
  H.exi_fAux_ge

theorem exi_g'_ge {n} : ∃ k, n ≤ g' a k :=
  H.exi_gAux_ge

theorem series_eq_f'_add_g' {n} : series |a| n =
series |ap a| (f' a n) + series |an a| (g' a n) :=
  H.series_eq_fAux_add_gAux (F := abs)

theorem monoLe_series_ap : monoLe # series # ap a :=
  monoLe_series_of_nonneg H.ap_fn_nonneg

theorem monoGt_series_an : monoGt # series # an a :=
  monoGt_series_of_neg # λ _ => H.an_neg

theorem monoGe_series_an : monoGe # series # an a :=
  monoGe_of_monoGt H.monoGt_series_an

theorem not_converges_series_ap_or_an :
¬converges (series # ap a) ∨ ¬converges (series # an a) := by
  rw [←not_and_iff_or]
  rintro ⟨⟨X, h₇⟩, ⟨Y', h₈⟩⟩
  generalize hY : -Y' = Y
  rw [neg_eq_iff_eq_neg] at hY
  subst hY
  have hX : 0 ≤ X := le_limit_of_forall_le h₇ H.series_ap_fn_nonneg
  have hY : 0 ≤ Y
  · suffices : -Y ≤ 0; linarith
    exact limit_le_of_forall_le h₈ H.series_an_fn_nonpos
  have h₉ : ∀ n, series |a| n ≤ X + Y
  · intro n
    have H₁ : monoLe # series |an a|
    · apply monoLe_series_abs
    have H₂ : tendsTo |series # an a| Y
    · rw [show Y = |-Y| by rw [abs_neg, abs_of_nonneg hY]]
      exact tendsTo_abs h₈
    have H₃ : ∀ n, series |ap a| n ≤ X
    · rw [H.abs_ap_fn]; exact le_limit_of_monoLe H.monoLe_series_ap h₇
    have H₄ : ∀ n, series |an a| n ≤ Y
    · rw [H.abs_an_fn]; intro k
      rw [←neg_series']; apply neg_le_of_neg_le
      apply limit_le_of_monoGe H.monoGe_series_an h₈
    rw [H.series_eq_f'_add_g']
    linarith [H₃ (f' a n), H₄ (g' a n)]
  have H₁ : converges # series |a|
  · apply converges_of_monoLe_and_bounded_top # by simp
    use X + Y, h₉
  exact H.not_absConv H₁

theorem not_converges_series_ap : ¬converges (series # ap a) := by
  have h₇ := H.not_converges_series_ap_or_an
  by_contra h₈
  simp [h₈] at h₇
  choose X h₈ using h₈
  have H₁ : 0 ≤ X := le_limit_of_forall_le h₈ H.series_ap_fn_nonneg
  obtain ⟨N₁, hN₁⟩ := exi_lt_of_monoGe_and_not_converges
    H.monoGe_series_an h₇ # M a - (X + 1)
  have h₁ := H.tendsTo_series
  specialize h₁ 1 # by norm_num
  choose N₃ h₁ using h₁
  obtain ⟨N₂, hN₂⟩ := H.exi_g_ge (n := N₁ + N₃)
  replace hN₁ : series (an a) (g a N₂) < M a - (X + 1)
  · apply lt_of_le_of_lt _ hN₁; apply H.monoGe_series_an; omega
  have H₃ : ∀ n, series (ap a) n ≤ X
  · intro n; apply le_limit_of_monoLe H.monoLe_series_ap h₈
  have H₄ : g a N₂ ≤ N₂
  · have := H.f_add_g (n := N₂); omega
  specialize h₁ N₂ # by linarith
  rw [abs_sub_lt_iff'] at h₁
  replace h₁ := h₁.1
  rw [H.series_eq_f_add_g] at h₁
  contrapose! h₁; clear h₁
  suffices : series (ap a) (f a N₂) ≤ (X + 1) - 1; linarith
  apply H₃ _ |>.trans; linarith

theorem not_converges_series_an : ¬converges (series # an a) := by
  by_contra h₈
  choose Y' h₈ using h₈
  generalize hY : -Y' = Y
  rw [neg_eq_iff_eq_neg] at hY
  subst hY
  have H₁ : 0 ≤ Y
  · suffices : -Y ≤ 0; linarith
    apply limit_le_of_forall_le h₈ H.series_an_fn_nonpos
  obtain ⟨N₁, hN₁⟩ := exi_gt_of_monoLe_and_not_converges
    H.monoLe_series_ap H.not_converges_series_ap # M a + (Y + 1)
  choose N₃ h₁ using H.tendsTo_series 1 # by norm_num
  obtain ⟨N₂, hN₂⟩ := H.exi_f_ge (n := N₁ + N₃)
  replace hN₁ : M a + (Y + 1) < series (ap a) (f a N₂)
  · apply lt_of_lt_of_le hN₁; apply H.monoLe_series_ap; omega
  have H₃ : ∀ n, -Y ≤ series (an a) n
  · intro n; apply limit_le_of_monoGe H.monoGe_series_an h₈
  have H₄ : f a N₂ ≤ N₂
  · have := H.f_add_g (n := N₂); omega
  specialize h₁ N₂ # by linarith
  rw [abs_sub_lt_iff'] at h₁
  replace h₁ := h₁.2
  rw [H.series_eq_f_add_g] at h₁
  contrapose! h₁; clear h₁
  suffices : 1 - (Y + 1) ≤ series (an a) (g a N₂); linarith
  apply H₃ _ |>.trans'; linarith

theorem exi_ap_gt L : ∃ n, L < series (ap a) n :=
  exi_gt_of_monoLe_and_not_converges H.monoLe_series_ap H.not_converges_series_ap L

theorem exi_an_lt L : ∃ n, series (an a) n < L :=
  exi_lt_of_monoGe_and_not_converges H.monoGe_series_an H.not_converges_series_an L

omit H in
theorem neg_of_lt_σp_zero {n} (h : n < σp a 0) : a n < 0 := by
  linarith [not_of_lt_mkSubseq_zero h]

omit H in
theorem nonneg_of_lt_σn_zero {n} (h : n < σn a 0) : 0 ≤ a n := by
  linarith [not_of_lt_mkSubseq_zero h]

theorem sum_map_filter_range_σp {n} :
(List.range (σp a n) |>.filter (0 ≤ a ·) |>.map a).sum = series (ap a) n := by
  induction n
  · simp; convert List.sum_nil; simp; exact λ _ => neg_of_lt_σp_zero
  nm n ih; simp [series_succ, ←ih]; unfold ap σp
  simp [filter_range_mkSubseq_succ H.infp_nonneg]

theorem sum_map_filter_range_σn {n} :
(List.range (σn a n) |>.filter (a · < 0) |>.map a).sum = series (an a) n := by
  induction n
  · simp; convert List.sum_nil; simp; exact λ _ => nonneg_of_lt_σn_zero
  nm n ih; simp [series_succ, ←ih]; unfold an σn
  simp [filter_range_mkSubseq_succ H.infp_neg]

theorem exi_ap_map_range_gt L :
∃ n, L < (List.range n |>.filter (0 ≤ a ·) |>.map a |>.sum) := by
  choose n h₁ using H.exi_ap_gt L; use σp a n; rwa [H.sum_map_filter_range_σp]

theorem exi_an_map_range_lt L :
∃ n, (List.range n |>.filter (a · < 0) |>.map a |>.sum) < L := by
  choose n h₁ using H.exi_an_lt L; use σn a n; rwa [H.sum_map_filter_range_σn]

theorem tendsTo_zero : tendsTo a 0 :=
  tendsTo_zero_of_converges_series H.converges_series

theorem bounds_tendsTo_zero : tendsTo (bounds a) 0 := by
  rw [←abs_zero]; exact tendsTo_bounds_of_tendsTo H.tendsTo_zero

theorem exi_ap_map_range_drop_gt L k :
∃ n, L < (List.range n |>.map (k + ·) |>.filter (0 ≤ a ·) |>.map a |>.sum) := by
  replace H := H.drop (N := k)
  choose n h₁ using H.exi_ap_map_range_gt L
  use n
  convert h₁ using 2
  clear h₁
  induction n
  · rfl
  nm n ih
  simp [List.range_succ]
  rw [ih]; clear ih
  grind

theorem exi_an_map_range_drop_lt L k :
∃ n, (List.range n |>.map (k + ·) |>.filter (a · < 0) |>.map a |>.sum) < L := by
  replace H := H.drop (N := k)
  choose n h₁ using H.exi_an_map_range_lt L
  use n
  convert h₁ using 2
  clear h₁
  induction n
  · rfl
  nm n ih
  simp [List.range_succ]
  rw [ih]; clear ih
  grind

theorem exi_add_ap_map_range_drop_gt s L k :
∃ n, L < s + (List.range n |>.map (k + ·) |>.filter (0 ≤ a ·) |>.map a |>.sum) := by
  simp_rw [←sub_lt_iff_lt_add']; apply H.exi_ap_map_range_drop_gt

theorem exi_add_an_map_range_drop_lt s L k :
∃ n, s + (List.range n |>.map (k + ·) |>.filter (a · < 0) |>.map a |>.sum) < L := by
  simp_rw [←lt_sub_iff_add_lt']; apply H.exi_an_map_range_drop_lt