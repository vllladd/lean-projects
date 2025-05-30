import AP.Strategy

noncomputable section
open scoped Classical

@[simp]
theorem not_state'₀_0_a_has_move : ¬(state'₀ 0).a_has_move := by
  simp [a_has_move_iff]

theorem not_a_has_move_of_pw_0 {s : State'} (h : s.pw = 0) : ¬s.a_has_move := by
  simp [a_has_move_iff, h]

-- theorem card_grid_diff_le_2_and_of_state'₀_0 {g : Game} {n c}
-- (h : g.state' = state'₀ 0)
-- (hc : c = Cardinal.mk (Set.univ \ (g.play n).state'.grid : Set Point)) :
-- c ≤ 1 ∧ (c = 1 → g.a_turn) := by
--   induction n generalizing c; simp [h, hc]
--   nm n ih
--   simp [Game.move] at hc
--   split_ifs at hc with h₁ h₂
--   · exact ih hc
--   · split at hc
--     · nm m h₃
--       exact ih hc
--     · nm m s h₃
--       replace h₃ := of_a_ap_eq_some' h₃
--       contrapose h₃; apply not_a_has_move_of_pw_0
--       simp [Game.pw, State.pw, h]
--   · split at hc
--     · nm m h₃; exact ih hc
--     · nm m s h₃
--       simp [Game.state'] at hc
--       obtain ⟨p, rfl, h₄, h₅⟩ := of_d_ap_eq_some h₃; clear h₃
--       dsimp at hc
--       specialize ih rfl
--       rcases ih with ⟨ih₁, ih₂⟩
--       simp [Set.erase] at hc
--       rw [Set.diff_diff_eq_sdiff_union] at hc
--       ·
--         simp at hc
--         rw [Cardinal.mk_insert, ←Game.state'] at hc
--         · 
-- 
-- #check 0 #exit
-- 
-- theorem card_grid_diff_le_n_of_state'₀_0 {g : Game} {n}
-- (h₁ : g.state' = state'₀ 0) :
-- Cardinal.mk (Set.univ \ (g.play n).state'.grid : Set Point) ≤ n := by
--   -- induction n; simp [h₁]; nm n ih; simp; simp [Game.move]
--   -- split_ifs with h₂ h₃; apply ih.trans; simp
--   -- · split
--   --   · nm m h₄; simp [Game.state']; apply ih.trans; simp
--   --   · nm m s h₄; replace h₄ := of_a_ap_eq_some' h₄
--   --     contrapose h₄; apply not_a_has_move_of_pw_0
--   --     simp [Game.pw, State.pw, h₁]
--   -- · split <;> simp [Game.state']
--   --   · nm m h₄; apply ih.trans; simp
--   --   · nm m s h₄; replace h₄ := of_d_ap_eq_some h₄
--   --     obtain ⟨p, rfl, h₄, h₅⟩ := h₄; simp [Set.erase]
--   --     rw [Set.diff_diff_eq_sdiff_union]; simp
--   --     rw [Cardinal.mk_insert] <;> simpa; simp
-- 
-- theorem not_Reachable'_imp_reachable :
-- ¬(∀ (s₀ s : State'), s₀.Reachable' s → s₀.reachable s) := by
--   push_neg
--   obtain ⟨s₁, hs₁⟩ := hv #
--     {state'₀ 0 with grid := Set.univ \
--     {(⟨0, 1⟩ : Point)}}
--   obtain ⟨s₂, hs₂⟩ := hv #
--     {state'₀ 0 with grid := Set.univ \
--     {(⟨0, 1⟩ : Point), (⟨0, 2⟩ : Point)}}
--   dsimp at hs₁ hs₂
--   use state'₀ 0, s₂
--   constructor
--   · apply State'.Reachable'.hd s₁
--     · apply State'.Reachable'.hd # state'₀ 0
--       constructor
--       use ⟨0, 1⟩
--       simp [hs₁, hs₂, Set.erase]
--     use ⟨0, 2⟩
--     simp [hs₁, hs₂, Set.erase, Set.diff_upair]
--   clear s₁ hs₁
--   simp [State'.reachable]
--   rintro g h₁ n rfl
--   rw [eq_comm] at h₁
--   have h₂ := congrArg State'.grid hs₂
--   clear hs₂
--   dsimp at h₂
--   
--   contrapose! h₂; clear h₂
--   
--   -- by_cases ht : g.a_turn
--   
--   -- revert n
--   -- apply prop_bcs g.a_turn <;> intro ht n
--   -- · cases n; simp [h₁]
--   --   nm n
--   
--     -- induction n; simp [h₁]
--     -- nm n ih
--     -- simp [Game.move]
--     -- split_ifs with h₂ h₃; exact ih
--     -- · split
--     --   · assumption
--     --   · nm m s h₄
--     --     replace h₄ := of_a_ap_eq_some' h₄
--     --     contrapose! h₄
--     --     apply not_a_has_move_of_pw_0
--     --     simp [Game.pw, State.pw, h₁]