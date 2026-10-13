module

public import DGS.S12_Deg2.SEdCons
public import DGS.S11_Deg1.PtrueMain

@[expose] public section

open Finset Filter Topology Matrix Module
open scoped Real

namespace DGS

section Facts

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [Algebra (ZMod p) L]

theorem card_eq_sq_of_finrank [Fintype L] (hL : finrank (ZMod p) L = 2) : Fintype.card L = p ^ 2 := by
  rw [Module.card_eq_pow_finrank (K := ZMod p) (V := L), ZMod.card, hL]

theorem one_ne_neg_one_ext (hp2 : p ≠ 2) : (1 : L) ≠ -1 := by
  intro h
  apply one_ne_neg_one_zmod (p := p) hp2
  apply (algebraMap (ZMod p) L).injective
  rw [map_one, map_neg, map_one]
  exact h

variable [Finite L]

theorem natDegree_minpoly_eq_two (hL : finrank (ZMod p) L = 2) {μ : L}
    (hμ : μ ∉ Set.range (algebraMap (ZMod p) L)) : (minpoly (ZMod p) μ).natDegree = 2 := by
  have hint : IsIntegral (ZMod p) μ := IsIntegral.of_finite (ZMod p) μ
  have h1 : (minpoly (ZMod p) μ).natDegree ≤ 2 := hL ▸ minpoly.natDegree_le μ
  have h2 : (minpoly (ZMod p) μ).natDegree ≠ 1 := fun h => hμ (minpoly.natDegree_eq_one_iff.1 h)
  have h3 : 0 < (minpoly (ZMod p) μ).natDegree := minpoly.natDegree_pos hint
  omega

theorem isGenRoot_minpoly_two (hL : finrank (ZMod p) L = 2) {μ : L}
    (hμ : μ ∉ Set.range (algebraMap (ZMod p) L)) : IsGenRoot (minpoly (ZMod p) μ) μ := by
  have hint : IsIntegral (ZMod p) μ := IsIntegral.of_finite (ZMod p) μ
  exact ⟨minpoly.monic hint, minpoly.irreducible hint, minpoly.aeval _ _,
    by rw [hL, natDegree_minpoly_eq_two hL hμ]⟩

end Facts

section Hyps

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [Fintype L] [Algebra (ZMod p) L]

theorem rank2_hyp_i {m : ℕ} (hp23 : 23 ≤ p) (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (hL : finrank (ZMod p) L = 2) {μ : L} (hμ : μ ∉ Set.range (algebraMap (ZMod p) L))
    (ω : Pairs m → Bool) (hPT : GoodPT (seidelOf ω)) (h0 : geomMult (F := L) 1 (-1) μ ω = 0) :
    prob (fun ξ : Fin m → Bool => geomMult (F := L) 1 (-1) μ (succPairs ω ξ) = 1) ≤
      1 / (p : ℝ) ^ 2 + Real.exp (-(cPT * m) / 2) := by
  set Lm := shiftedMat (F := L) 1 (-1) μ ω with hLm
  have hLT : Lmᵀ = Lm := shiftedMat_transpose μ ω
  have hdet : IsUnit Lm.det := by
    rw [isUnit_iff_ne_zero]
    intro hd
    obtain ⟨v, hv0, hv⟩ := (exists_mulVec_eq_zero_iff).2 hd
    have hpos : 0 < geomMult (F := L) 1 (-1) μ ω := by
      unfold geomMult corank
      refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact hv
      · intro h
        exact hv0 (congrArg Subtype.val h)
    omega
  have hev : ∀ ξ : Fin m → Bool, geomMult (F := L) 1 (-1) μ (succPairs ω ξ) = 1 ↔
      twoValued (1 : L) (-1) ξ ⬝ᵥ (Lm⁻¹ *ᵥ twoValued 1 (-1) ξ) = -μ := by
    intro ξ
    unfold geomMult
    rw [shiftedMat_succPairs, (lem_border_inv hLT hdet).2.1]
    exact eq_comm
  rw [prob_congr hev]
  exact prob_quadL_le hPT hp23 hpm hL hμ hdet (-μ)

theorem rank2_hyp_ii {m : ℕ} (hp23 : 23 ≤ p) (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (hL : finrank (ZMod p) L = 2) {μ : L} (hμ : μ ∉ Set.range (algebraMap (ZMod p) L))
    (ω : Pairs m → Bool) (hSE : GoodSEd 2 (seidelOf ω)) :
    prob (fun ξ : Fin m → Bool => ∀ k ∈ LinearMap.ker (shiftedMat (F := L) 1 (-1) μ ω).mulVecLin,
        twoValued (1 : L) (-1) ξ ⬝ᵥ k = 0) ≤
      ((Fintype.card L : ℝ) ^ geomMult (F := L) 1 (-1) μ ω)⁻¹ + Real.exp (-2 * cSEd * m) := by
  have h := prob_perp_eigsp_le hSE hp23 hpm (fun h => absurd h (by norm_num)) (isGenRoot_minpoly_two hL hμ)
    (natDegree_minpoly_eq_two hL hμ) _ (ker_shiftedMat_le_eigsp (p := p) μ ω)
  unfold geomMult corank
  rw [card_eq_sq_of_finrank hL]
  push_cast
  rw [← pow_mul]
  exact h

end Hyps

def EvR2 (m : ℕ) (ω : Pairs m → Bool) : Prop := GoodPT (seidelOf ω) ∧ GoodSEd 2 (seidelOf ω)

theorem prob_not_EvR2_le :
    ∀ᶠ m : ℕ in atTop, prob (fun ω : Pairs m → Bool => ¬ EvR2 m ω) ≤ 3 * Real.exp (-(m : ℝ) / 200) := by
  filter_upwards [prop_Ptrue, prop_SEd (d := 2) le_rfl (by norm_num)] with m h1 h2
  have h3 : Real.exp (-(m : ℝ) / 9) ≤ Real.exp (-(m : ℝ) / 200) := by
    apply Real.exp_le_exp.2
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  calc prob (fun ω : Pairs m → Bool => ¬ EvR2 m ω)
      ≤ prob (fun ω : Pairs m → Bool => ¬ GoodPT (seidelOf ω) ∨ ¬ GoodSEd 2 (seidelOf ω)) :=
        prob_mono fun ω h => by
          unfold EvR2 at h
          tauto
    _ ≤ probSeidel m (fun T => ¬ GoodPT T) + probSeidel m (fun T => ¬ GoodSEd 2 T) := prob_or_le _ _
    _ ≤ Real.exp (-(m : ℝ) / 200) + Real.exp (-(m : ℝ) / 9) := add_le_add h1 h2
    _ ≤ 3 * Real.exp (-(m : ℝ) / 200) := by
        have := Real.exp_pos (-(m : ℝ) / 200)
        linarith

theorem thm_rank2 :
    ∀ᶠ n : ℕ in atTop, ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p → (p : ℝ) ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 9)) →
      ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], finrank (ZMod p) L = 2 →
      ∀ μ : L, μ ∉ Set.range (algebraMap (ZMod p) L) →
        prob (fun ω : Pairs n → Bool => 1 ≤ geomMult (F := L) 1 (-1) μ ω) ≤
          1 / (p : ℝ) ^ 2 + 1.2 / ((p : ℝ) ^ 2) ^ 2 + Real.exp (-cRK * n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 prob_not_EvR2_le
  have hA : ∀ᶠ n : ℕ in atTop, N ≤ (3 * n + 3) / 4 := by
    filter_upwards [eventually_ge_atTop (2 * N)] with n hn
    omega
  have hC : ∀ᶠ n : ℕ in atTop, Real.exp (-(cPT * ((3 * n + 3) / 4 : ℕ)) / 2) ≤ 1 / 100000 := by
    filter_upwards [eventually_const_le_exp (a := 3 * cPT / 8) (C := 100000) (by have := cPT_pos; positivity)]
      with n hn
    have hm := (m0_bounds n).1
    have hexp : Real.exp (3 * cPT / 8 * n) ≤ Real.exp (cPT * ((3 * n + 3) / 4 : ℕ) / 2) := by
      apply Real.exp_le_exp.2
      have := cPT_pos
      nlinarith
    rw [show -(cPT * ((3 * n + 3) / 4 : ℕ)) / 2 = -(cPT * ((3 * n + 3) / 4 : ℕ) / 2) by ring, Real.exp_neg,
      inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  filter_upwards [hA, hC, eventually_rpow_ninth_le, rankp_err_eventually, eventually_ge_atTop 4]
    with n hA hC hB hD hn4
  intro p _ hp23 hpn L _ _ _ hL μ hμ
  have hp2 : p ≠ 2 := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set m0 := (3 * n + 3) / 4 with hm0
  set ϖ := Real.exp (-(cPT * m0) / 2) with hϖ
  have hpm : ∀ m, m0 ≤ m → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) := by
    intro m hm
    refine hpn.trans (Real.exp_le_exp.2 (hB.trans ?_))
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hm) (by norm_num)
  have hcard : (Fintype.card L : ℝ) = (p : ℝ) ^ 2 := by
    rw [card_eq_sq_of_finrank hL]
    push_cast
    ring
  have hi : ∀ m, m0 ≤ m → m < n → ∀ ω, EvR2 m ω → geomMult (F := L) 1 (-1) μ ω = 0 →
      prob (fun ξ : Fin m → Bool => geomMult (F := L) 1 (-1) μ (succPairs ω ξ) = 1) ≤
        (Fintype.card L : ℝ)⁻¹ + ϖ := by
    intro m hm0' hmn ω hE h0
    rw [hcard, ← one_div]
    refine (rank2_hyp_i hp23 (hpm m hm0') hL hμ ω hE.1 h0).trans (add_le_add le_rfl ?_)
    apply Real.exp_le_exp.2
    have : (m0 : ℝ) ≤ m := by exact_mod_cast hm0'
    have := cPT_pos
    nlinarith
  have hii : ∀ m, m0 ≤ m → m < n → ∀ ω, EvR2 m ω → 1 ≤ geomMult (F := L) 1 (-1) μ ω →
      prob (fun ξ : Fin m → Bool => ∀ k ∈ LinearMap.ker (shiftedMat (F := L) 1 (-1) μ ω).mulVecLin,
        twoValued (1 : L) (-1) ξ ⬝ᵥ k = 0) ≤
        ((Fintype.card L : ℝ) ^ geomMult (F := L) 1 (-1) μ ω)⁻¹ + ϖ := by
    intro m hm0' hmn ω hE _
    refine (rank2_hyp_ii hp23 (hpm m hm0') hL hμ ω hE.2).trans (add_le_add le_rfl ?_)
    apply Real.exp_le_exp.2
    have : (m0 : ℝ) ≤ m := by exact_mod_cast hm0'
    have h1 := cPT_le
    have h2 := cPT_pos
    have h3 : (0 : ℝ) ≤ m0 := Nat.cast_nonneg _
    have h4 : cPT ≤ 4 * cSEd := by
      unfold cPT cSEd
      have : Real.exp (-1500) ≤ Real.exp (-300) := Real.exp_le_exp.2 (by norm_num)
      have := Real.exp_pos (-300)
      linarith
    nlinarith
  have hq : 23 ≤ Fintype.card L := by
    rw [card_eq_sq_of_finrank hL]
    nlinarith
  have hcor := lem_corank (F := L) (one_ne_neg_one_ext (p := p) hp2) hq μ hn4 (Real.exp_pos _).le hC EvR2
    hi hii
  rw [hcard] at hcor
  have hsum : prob (fun ω : Pairs n → Bool => ¬ EaccRec EvR2 m0 n ω) ≤
      n * (3 * Real.exp (-(m0 : ℝ) / 200)) := by
    refine (prob_not_EaccRec_le EvR2 m0 n).trans ?_
    calc ∑ j ∈ Ico m0 n, prob (fun ω : Pairs j → Bool => ¬ EvR2 j ω)
        ≤ ∑ _j ∈ Ico m0 n, 3 * Real.exp (-(m0 : ℝ) / 200) := by
          refine sum_le_sum fun j hj => ?_
          have hj0 : m0 ≤ j := (mem_Ico.1 hj).1
          refine (hN j (hA.trans hj0)).trans ?_
          gcongr
      _ = ((n - m0 : ℕ) : ℝ) * (3 * Real.exp (-(m0 : ℝ) / 200)) := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ n * (3 * Real.exp (-(m0 : ℝ) / 200)) := by
          gcongr
          exact_mod_cast Nat.sub_le n m0
  have h2 := hcor.2
  calc prob (fun ω : Pairs n → Bool => 1 ≤ geomMult (F := L) 1 (-1) μ ω)
      ≤ 1 / (p : ℝ) ^ 2 + 1.2 / ((p : ℝ) ^ 2) ^ 2 + 2 * ϖ +
          C0 * (0.163 : ℝ) ^ (((n : ℝ) - m0 - 2) / 2) +
          prob (fun ω : Pairs n → Bool => ¬ EaccRec EvR2 m0 n ω) := h2
    _ ≤ 1 / (p : ℝ) ^ 2 + 1.2 / ((p : ℝ) ^ 2) ^ 2 + Real.exp (-cRK * n) := by linarith

end DGS
