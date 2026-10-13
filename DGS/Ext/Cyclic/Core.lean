module

public import DGS.S04_Reduction.Reduction

@[expose] public section

open Matrix Polynomial Module Filter Topology
open scoped ENNReal

namespace DGS

section Defs

variable {m : ℕ}

def NotCyc (p : ℕ) (T : Matrix (Fin m) (Fin m) ℤ) (u : Fin m → ℤ) : Prop :=
  ∃ U : Submodule (ZMod p) (Fin m → ZMod p), IsSimpleInvariant (modP p T) U ∧
    ∀ x ∈ U, modPVec p u ⬝ᵥ x = 0

def IsFactor (p : ℕ) (T : Matrix (Fin m) (Fin m) ℤ) (β : (ZMod p)[X]) : Prop :=
  β.Monic ∧ Irreducible β ∧ β ∣ (modP p T).charpoly

open Classical in
noncomputable def Nall (p : ℕ) (T : Matrix (Fin m) (Fin m) ℤ) : ℝ≥0∞ :=
  ∑' β : (ZMod p)[X], if IsFactor p T β then ENNReal.ofReal (abeta p T β) else 0

open Classical in
noncomputable def expectNall (p m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℤ)) : ℝ≥0∞ :=
  (∑ ω : Pairs m → Bool, if seidelOf ω ∈ G then Nall p (seidelOf ω) else 0) /
    (Fintype.card (Pairs m → Bool) : ℝ≥0∞)

def UniqSimple (p : ℕ) (T : Matrix (Fin m) (Fin m) ℤ) (β : (ZMod p)[X]) : Prop :=
  ∀ U U' : Submodule (ZMod p) (Fin m → ZMod p), IsSimpleInvariant (modP p T) U → HasType (modP p T) U β →
    IsSimpleInvariant (modP p T) U' → HasType (modP p T) U' β → U = U'

def DelAll (p : ℕ) (T : Matrix (Fin m) (Fin m) ℤ) (s : Fin m → ℤ) : Prop :=
  ∃ β : (ZMod p)[X], (∃ U, IsSimpleInvariant (modP p T) U ∧ HasType (modP p T) U β) ∧
    ∀ v, aeval (modP p T) β *ᵥ v = 0 → modPVec p s ⬝ᵥ v = 0

def UniqEvent (p : ℕ) (T : Matrix (Fin m) (Fin m) ℤ) (u : Fin m → ℤ) : Prop :=
  ∃ β : (ZMod p)[X], UniqSimple p T β ∧ ∃ U, IsSimpleInvariant (modP p T) U ∧ HasType (modP p T) U β ∧
    ∀ y ∈ U, modPVec p u ⬝ᵥ y = 0

def ManyEvent (p : ℕ) (T : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∃ β : (ZMod p)[X], β.Monic ∧ Irreducible β ∧ ¬ UniqSimple p T β

end Defs

section Weights

variable {m : ℕ} {p : ℕ} [Fact p.Prime]

theorem isFactor_of_hasType {T : Matrix (Fin m) (Fin m) ℤ} {U : Submodule (ZMod p) (Fin m → ZMod p)}
    (hU : IsSimpleInvariant (modP p T) U) {β : (ZMod p)[X]} (hβ : HasType (modP p T) U β) :
    IsFactor p T β := by
  refine ⟨hβ.1, hβ.2.1, ?_⟩
  by_contra hnd
  obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hβ.2.1).2 hnd
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.2.1
  apply hu0
  have h1 : (aeval (modP p T) a * aeval (modP p T) β +
      aeval (modP p T) b * aeval (modP p T) (modP p T).charpoly) *ᵥ u = u := by
    rw [← map_mul, ← map_mul, ← map_add, hab, map_one, one_mulVec]
  rw [Matrix.aeval_self_charpoly, mul_zero, add_zero, ← mulVec_mulVec, hβ.2.2 u huU, mulVec_zero] at h1
  exact h1.symm

theorem ofReal_prob_uniq_le (T : Matrix (Fin m) (Fin m) ℤ) :
    ENNReal.ofReal (prob (fun ξ : Fin m → Bool => UniqEvent p T (signVec ξ))) ≤ Nall p T := by
  classical
  refine (ofReal_prob_exists_le_tsum _).trans ?_
  rw [Nall]
  refine ENNReal.tsum_le_tsum fun β => ?_
  by_cases hex : ∃ U, IsSimpleInvariant (modP p T) U ∧ HasType (modP p T) U β
  · obtain ⟨U₀, hU₀, hβ₀⟩ := hex
    rw [ite_eq_left (isFactor_of_hasType hU₀ hβ₀)]
    refine ENNReal.ofReal_le_ofReal ((prob_mono fun ξ hξ => ?_).trans (probPerp_le_abeta hU₀ hβ₀))
    obtain ⟨huniq, U, hU, hβ, horth⟩ := hξ
    rw [huniq U U₀ hU hβ hU₀ hβ₀] at horth
    exact horth
  · have h0 : prob (fun ξ : Fin m → Bool => UniqSimple p T β ∧ ∃ U, IsSimpleInvariant (modP p T) U ∧
        HasType (modP p T) U β ∧ ∀ y ∈ U, modPVec p (signVec ξ) ⬝ᵥ y = 0) = 0 := by
      rw [← prob_false (Ω := Fin m → Bool)]
      exact prob_congr fun ξ => ⟨fun ⟨_, U, hU, hβ, _⟩ => hex ⟨U, hU, hβ⟩, False.elim⟩
    rw [h0, ENNReal.ofReal_zero]
    exact zero_le

theorem ofReal_prob_delAll_le (T : Matrix (Fin m) (Fin m) ℤ) :
    ENNReal.ofReal (prob (fun ξ : Fin m → Bool => DelAll p T (signVec ξ))) ≤ Nall p T := by
  classical
  refine (ofReal_prob_exists_le_tsum _).trans ?_
  rw [Nall]
  refine ENNReal.tsum_le_tsum fun β => ?_
  by_cases hex : ∃ U, IsSimpleInvariant (modP p T) U ∧ HasType (modP p T) U β
  · obtain ⟨U₀, hU₀, hβ₀⟩ := hex
    rw [ite_eq_left (isFactor_of_hasType hU₀ hβ₀)]
    refine ENNReal.ofReal_le_ofReal ((prob_mono fun ξ hξ => ?_).trans (probPerp_le_abeta hU₀ hβ₀))
    intro y hy
    exact hξ.2 y (hβ₀.2.2 y hy)
  · have h0 : prob (fun ξ : Fin m → Bool => (∃ U, IsSimpleInvariant (modP p T) U ∧ HasType (modP p T) U β) ∧
        ∀ v, aeval (modP p T) β *ᵥ v = 0 → modPVec p (signVec ξ) ⬝ᵥ v = 0) = 0 := by
      rw [← prob_false (Ω := Fin m → Bool)]
      exact prob_congr fun ξ => ⟨fun h => hex h.1, False.elim⟩
    rw [h0, ENNReal.ofReal_zero]
    exact zero_le

theorem ofReal_prob_delAll_avg_le (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℤ)) :
    ENNReal.ofReal (prob (fun x : (Pairs n → Bool) × (Fin n → Bool) =>
      DelAll p (seidelOf x.1) (signVec x.2))) ≤
      ENNReal.ofReal (probSeidel n (fun S => S ∉ G)) + expectNall p n G := by
  classical
  have hpt : ∀ ω : Pairs n → Bool,
      ENNReal.ofReal (prob (fun ξ : Fin n → Bool => DelAll p (seidelOf ω) (signVec ξ))) ≤
        (if seidelOf ω ∉ G then (1 : ℝ≥0∞) else 0) +
          (if seidelOf ω ∈ G then Nall p (seidelOf ω) else 0) := by
    intro ω
    by_cases hG : seidelOf ω ∈ G
    · rw [ite_eq_right (not_not.2 hG), ite_eq_left hG, zero_add]
      exact ofReal_prob_delAll_le (seidelOf ω)
    · rw [ite_eq_left hG, ite_eq_right hG, add_zero, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (prob_le_one _)
  have h1 := ofReal_prob_prod_le (fun x : (Pairs n → Bool) × (Fin n → Bool) =>
    DelAll p (seidelOf x.1) (signVec x.2)) _ hpt
  refine h1.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ENNReal.add_div, probSeidel,
    ofReal_prob_eq (fun ω : Pairs n → Bool => seidelOf ω ∉ G), expectNall]

end Weights

section Deletion

variable {n : ℕ}

theorem two_le_finrank_of_not_uniq {p : ℕ} [Fact p.Prime] {T : Matrix (Fin n) (Fin n) ℤ} {β : (ZMod p)[X]}
    [Fact (Irreducible β)] (hβm : β.Monic) (hnu : ¬ UniqSimple p T β) :
    2 ≤ finrank (AdjoinRoot β) (eigsp (modP p T) (AdjoinRoot.root β)) := by
  have : Module.Finite (ZMod p) (AdjoinRoot β) := (AdjoinRoot.powerBasis hβm.ne_zero).finite
  have : Finite (AdjoinRoot β) := finite_adjoinRoot hβm.ne_zero
  have h := isGenRoot_adjoinRoot hβm
  unfold UniqSimple at hnu
  push Not at hnu
  obtain ⟨U, U', hU, hβ, hU', hβ', hne⟩ := hnu
  obtain ⟨w, hw, hw0, rfl⟩ := eq_Uw_of_hasType h hU hβ
  obtain ⟨w', hw', hw'0, rfl⟩ := eq_Uw_of_hasType h hU' hβ'
  have hpos : 1 ≤ finrank (AdjoinRoot β) (eigsp (modP p T) (AdjoinRoot.root β)) :=
    Submodule.one_le_finrank_iff.2 (fun hb => hw0 (by rw [hb] at hw; exact hw))
  by_contra hlt
  have h1 : finrank (AdjoinRoot β) (eigsp (modP p T) (AdjoinRoot.root β)) = 1 := by omega
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hw⟩ : eigsp (modP p T) (AdjoinRoot.root β))
    (fun h0 => hw0 (congrArg Subtype.val h0))).1 h1 ⟨w', hw'⟩
  exact hne ((Uw_eq_Uw_iff h hw hw' hw'0).2 ⟨c, (congrArg Subtype.val hc).symm⟩)

open Classical in
theorem many_deletions_all {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hS : S.IsSymm)
    (hgood : SuppGood S) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {β : (ZMod p)[X]} (hβm : β.Monic)
    (hβi : Irreducible β) (hnu : ¬ UniqSimple p S β) :
    ((n + 1 : ℕ) : ℝ) / 20 < ((Finset.univ.filter fun i => DelAll p (delMat S i) (delCol S i)).card : ℝ) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Irreducible β) := ⟨hβi⟩
  have : Module.Finite (ZMod p) (AdjoinRoot β) := (AdjoinRoot.powerBasis hβm.ne_zero).finite
  have : Finite (AdjoinRoot β) := finite_adjoinRoot hβm.ne_zero
  have h := isGenRoot_adjoinRoot hβm
  have hg := two_le_finrank_of_not_uniq hβm hnu
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) (AdjoinRoot β) :=
    S.map (Int.castRingHom (AdjoinRoot β)) - AdjoinRoot.root β • 1 with hBdef
  have hSL : (modP p S).map (algebraMap (ZMod p) (AdjoinRoot β)) =
      S.map (Int.castRingHom (AdjoinRoot β)) := modP_map_algebraMap p S
  have hBsymm : Bᵀ = B := by
    rw [hBdef, transpose_sub, transpose_smul, transpose_one, ← transpose_map, hS.eq]
  have hkerB : ∀ x, x ∈ LinearMap.ker B.mulVecLin ↔ x ∈ eigsp (modP p S) (AdjoinRoot.root β) := by
    intro x
    rw [hBdef, mem_ker_sub_iff, mem_eigsp, hSL]
  have hkerB' : LinearMap.ker B.mulVecLin = eigsp (modP p S) (AdjoinRoot.root β) := by
    ext x
    exact hkerB x
  set I := Finset.univ.filter fun i => ∃ w ∈ eigsp (modP p S) (AdjoinRoot.root β), w i ≠ 0 with hIdef
  have hIcard : ((n + 1 : ℕ) : ℝ) / 20 < (I.card : ℝ) := by
    obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_finrank_pos (K := eigsp (modP p S) (AdjoinRoot.root β))
      (by omega)
    have hweig : S.map (Int.castRingHom (AdjoinRoot β)) *ᵥ w = AdjoinRoot.root β • w := by
      rw [← hSL]; exact mem_eigsp.1 hw
    refine hgood p hp hp2 (AdjoinRoot β) (AdjoinRoot.root β) w hw0 hweig I fun i hi => ?_
    by_contra hwi
    exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, w, hw, hwi⟩)
  refine lt_of_lt_of_le hIcard ?_
  have hsubset : I ⊆ Finset.univ.filter fun i => DelAll p (delMat S i) (delCol S i) := by
    intro i hi
    obtain ⟨w, hw, hwi⟩ := (Finset.mem_filter.1 hi).2
    obtain ⟨hdim, horth, -⟩ := lem_delete hBsymm i ⟨w, (hkerB w).2 hw, hwi⟩
    have hSLi : (modP p (delMat S i)).map (algebraMap (ZMod p) (AdjoinRoot β)) =
        (delMat S i).map (Int.castRingHom (AdjoinRoot β)) := modP_map_algebraMap p _
    have hdelB : delMat B i =
        (delMat S i).map (Int.castRingHom (AdjoinRoot β)) - AdjoinRoot.root β • 1 := by
      rw [hBdef, delMat_sub_smul_one, delMat_map]
    have hkerBi : ∀ x, x ∈ LinearMap.ker (delMat B i).mulVecLin ↔
        x ∈ eigsp (modP p (delMat S i)) (AdjoinRoot.root β) := by
      intro x
      rw [hdelB, mem_ker_sub_iff, mem_eigsp, hSLi]
    have hkerBi' : LinearMap.ker (delMat B i).mulVecLin =
        eigsp (modP p (delMat S i)) (AdjoinRoot.root β) := by
      ext x
      exact hkerBi x
    have hgi : finrank (AdjoinRoot β) (eigsp (modP p (delMat S i)) (AdjoinRoot.root β)) + 1 =
        finrank (AdjoinRoot β) (eigsp (modP p S) (AdjoinRoot.root β)) := by
      unfold corank at hdim
      rw [hkerBi', hkerB'] at hdim
      exact hdim
    obtain ⟨w', hw', hw'0⟩ := exists_ne_zero_of_finrank_pos
      (K := eigsp (modP p (delMat S i)) (AdjoinRoot.root β)) (by omega)
    obtain ⟨hUs, hUt, -⟩ := (lem_simple_a h (modP p (delMat S i))).1 w' hw' hw'0
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, β, ⟨_, hUs, hUt⟩, fun v hv => ?_⟩
    obtain ⟨w'', hw'', rfl⟩ := (lem_simple_a_iso h (modP p (delMat S i))).2.2.2 v hv
    have hcol : (liftVec (ZMod p) (modPVec p (delCol S i)) : Fin n → AdjoinRoot β) =
        delCol B i := by
      rw [hBdef, delCol_sub_smul_one]
      funext j
      simp [liftVec, modPVec, delCol]
    have h1 := dotProduct_trVec (K := ZMod p) (modPVec p (delCol S i)) w'' 1
    rw [one_smul, one_mul, hcol, horth w'' ((hkerBi w'').2 hw''), map_zero] at h1
    exact h1
  exact_mod_cast Finset.card_le_card hsubset

end Deletion

section Core

variable {p : ℕ} [Fact p.Prime]

theorem notCyc_cases {N : ℕ} {S : Matrix (Fin N) (Fin N) ℤ} {u : Fin N → ℤ} (h : NotCyc p S u) :
    UniqEvent p S u ∨ ManyEvent p S := by
  obtain ⟨U, hU, horth⟩ := h
  obtain ⟨β, hβ, -⟩ := exists_hasType _ U hU
  by_cases hu : UniqSimple p S β
  · exact Or.inl ⟨β, hu, U, hU, hβ, horth⟩
  · exact Or.inr ⟨β, hβ.1, hβ.2.1, hu⟩

theorem core_bound (hp2 : p ≠ 2) (n : ℕ) (G : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ))
    (G' : Set (Matrix (Fin n) (Fin n) ℤ)) :
    ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) =>
      NotCyc p (seidelOf x.1) (signVec x.2))) ≤
      ENNReal.ofReal (probSeidel (n + 1) (fun S => S ∉ G)) + expectNall p (n + 1) G +
        20 * (ENNReal.ofReal (probSeidel n (fun S => S ∉ G')) + expectNall p n G') +
        ENNReal.ofReal (probSeidel (n + 1) (fun S => ¬ SuppGood S)) := by
  classical
  have hsub : ∀ x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool), NotCyc p (seidelOf x.1) (signVec x.2) →
      (seidelOf x.1 ∉ G ∨ (seidelOf x.1 ∈ G ∧ UniqEvent p (seidelOf x.1) (signVec x.2))) ∨
        ((ManyEvent p (seidelOf x.1) ∧ SuppGood (seidelOf x.1)) ∨ ¬ SuppGood (seidelOf x.1)) := by
    intro x hx
    rcases notCyc_cases hx with h1 | h2
    · by_cases hG : seidelOf x.1 ∈ G
      · exact Or.inl (Or.inr ⟨hG, h1⟩)
      · exact Or.inl (Or.inl hG)
    · by_cases hgood : SuppGood (seidelOf x.1)
      · exact Or.inr (Or.inl ⟨h2, hgood⟩)
      · exact Or.inr (Or.inr hgood)
  have hP := prob_mono hsub
  have h1 : prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => seidelOf x.1 ∉ G) =
      probSeidel (n + 1) (fun S => S ∉ G) :=
    prob_fst (fun ω => seidelOf ω ∉ G)
  have h2 : ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) =>
      seidelOf x.1 ∈ G ∧ UniqEvent p (seidelOf x.1) (signVec x.2))) ≤ expectNall p (n + 1) G := by
    have hpt : ∀ ω : Pairs (n + 1) → Bool, ENNReal.ofReal (prob (fun b : Fin (n + 1) → Bool =>
        seidelOf ω ∈ G ∧ UniqEvent p (seidelOf ω) (signVec b))) ≤
          if seidelOf ω ∈ G then Nall p (seidelOf ω) else 0 := by
      intro ω
      by_cases hG : seidelOf ω ∈ G
      · rw [ite_eq_left hG]
        exact le_trans (ENNReal.ofReal_le_ofReal (prob_mono fun b hb => hb.2)) (ofReal_prob_uniq_le _)
      · rw [ite_eq_right hG]
        have h0 : prob (fun b : Fin (n + 1) → Bool => seidelOf ω ∈ G ∧ UniqEvent p (seidelOf ω) (signVec b)) =
            0 := by
          rw [← prob_false (Ω := Fin (n + 1) → Bool)]
          exact prob_congr fun b => ⟨fun h => hG h.1, False.elim⟩
        rw [h0, ENNReal.ofReal_zero]
    refine (ofReal_prob_prod_le (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) =>
      seidelOf x.1 ∈ G ∧ UniqEvent p (seidelOf x.1) (signVec x.2)) _ hpt).trans (le_of_eq ?_)
    rw [expectNall]
  have h3 : ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) =>
      ManyEvent p (seidelOf x.1) ∧ SuppGood (seidelOf x.1))) ≤
      20 * (ENNReal.ofReal (probSeidel n (fun S => S ∉ G')) + expectNall p n G') := by
    rw [prob_fst (fun ω => ManyEvent p (seidelOf ω) ∧ SuppGood (seidelOf ω))]
    have hE := lem_exch (DelAll p) (fun ω => ManyEvent p (seidelOf ω) ∧ SuppGood (seidelOf ω))
      (fun ω hω => by
        obtain ⟨⟨β, hβm, hβi, hnu⟩, hgood⟩ := hω
        exact many_deletions_all (n := n) (isSeidel_seidelOf ω).1 hgood Fact.out hp2 hβm hβi hnu)
    rw [lem_exch_law] at hE
    calc ENNReal.ofReal (prob fun ω => ManyEvent p (seidelOf ω) ∧ SuppGood (seidelOf ω))
        ≤ ENNReal.ofReal (20 * prob (fun x : (Pairs n → Bool) × (Fin n → Bool) =>
            DelAll p (seidelOf x.1) (signVec x.2))) := ENNReal.ofReal_le_ofReal hE
      _ = 20 * ENNReal.ofReal (prob (fun x : (Pairs n → Bool) × (Fin n → Bool) =>
            DelAll p (seidelOf x.1) (signVec x.2))) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          simp
      _ ≤ 20 * (ENNReal.ofReal (probSeidel n (fun S => S ∉ G')) + expectNall p n G') := by
          gcongr
          exact ofReal_prob_delAll_avg_le n G'
  have h4 : prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => ¬ SuppGood (seidelOf x.1)) =
      probSeidel (n + 1) (fun S => ¬ SuppGood S) :=
    prob_fst (fun ω => ¬ SuppGood (seidelOf ω))
  calc ENNReal.ofReal (prob fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) =>
        NotCyc p (seidelOf x.1) (signVec x.2))
      ≤ ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => seidelOf x.1 ∉ G) +
          prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) =>
            seidelOf x.1 ∈ G ∧ UniqEvent p (seidelOf x.1) (signVec x.2)) +
          (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) =>
              ManyEvent p (seidelOf x.1) ∧ SuppGood (seidelOf x.1)) +
            prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => ¬ SuppGood (seidelOf x.1)))) :=
        ENNReal.ofReal_le_ofReal (hP.trans ((prob_or_le _ _).trans
          (add_le_add (prob_or_le _ _) (prob_or_le _ _))))
    _ = ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => seidelOf x.1 ∉ G)) +
          ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) =>
            seidelOf x.1 ∈ G ∧ UniqEvent p (seidelOf x.1) (signVec x.2))) +
          (ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) =>
              ManyEvent p (seidelOf x.1) ∧ SuppGood (seidelOf x.1))) +
            ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) =>
              ¬ SuppGood (seidelOf x.1)))) := by
        rw [ENNReal.ofReal_add (add_nonneg (prob_nonneg _) (prob_nonneg _))
            (add_nonneg (prob_nonneg _) (prob_nonneg _)),
          ENNReal.ofReal_add (prob_nonneg _) (prob_nonneg _),
          ENNReal.ofReal_add (prob_nonneg _) (prob_nonneg _)]
    _ ≤ ENNReal.ofReal (probSeidel (n + 1) (fun S => S ∉ G)) + expectNall p (n + 1) G +
          (20 * (ENNReal.ofReal (probSeidel n (fun S => S ∉ G')) + expectNall p n G') +
            ENNReal.ofReal (probSeidel (n + 1) (fun S => ¬ SuppGood S))) := by
        rw [h1, h4]
        gcongr
    _ = _ := by ring

end Core

end DGS
