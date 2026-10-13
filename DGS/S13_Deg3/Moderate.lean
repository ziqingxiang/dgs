module

public import DGS.S13_Deg3.Deg34Main
public import DGS.S12_Deg2.Deg2

@[expose] public section

open Filter Topology

namespace DGS

theorem thm_moderate (hTV : TaoVuStatement) : Thm24 := by
  intro ε hε0 hε
  have h1 := prop_deg1 hε0 (by linarith : ε < 1 / 2)
  have h2 := prop_deg2 hε0 (by linarith : ε < 1 / 2)
  have h3 := prop_deg3plus hTV hε0 hε
  have hsum := (h1.add h2).add h3
  rw [add_zero, add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => prob_nonneg _) fun n => ?_
  simp only [probG_eq_prob]
  refine (prob_mono fun G hG => ?_).trans ((prob_or_le _ _).trans (add_le_add (prob_or_le _ _) le_rfl))
  obtain ⟨p, d, hp, hp2, hp1, hp3, hd1, hdl, hE⟩ := hG
  rcases (by omega : d = 1 ∨ d = 2 ∨ 3 ≤ d) with rfl | rfl | hd3
  · exact Or.inl (Or.inl ⟨p, hp, hp2, hp1, hp3, hE⟩)
  · exact Or.inl (Or.inr ⟨p, hp, hp2, hp1, hp3, hE⟩)
  · exact Or.inr ⟨p, d, hp, hp2, hp1, hp3, hd3, hdl, hE⟩

end DGS
