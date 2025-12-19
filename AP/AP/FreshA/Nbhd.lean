import AP.AP.FreshA.Fresh1

namespace AP

-- #check 0 #exit

theorem AState.aHwsDisj_nbhd_pw {s : State} {fsp : FSP} [hs : AState s]
(h : s.aHwsDisj fsp) : s.aHwsDisj # fsp.insertSet 3 # s.aPos.nbhd s.pw |>.toSet := by
  replace h := exi_fresh1_of_aHwsDisj h
  choose a ha using h
  sorry