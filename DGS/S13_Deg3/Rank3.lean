module

public import DGS.S13_Deg3.Simple3
public import DGS.S12_Deg2.Rank2

@[expose] public section

open Finset Filter Topology Matrix Module
open scoped Real

namespace DGS

section Facts

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [Algebra (ZMod p) L]

theorem card_eq_cube_of_finrank [Fintype L] (hL : finrank (ZMod p) L = 3) : Fintype.card L = p ^ 3 := by
  rw [Module.card_eq_pow_finrank (K := ZMod p) (V := L), ZMod.card, hL]

end Facts

section Hyps

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [Fintype L] [Algebra (ZMod p) L]

theorem rank3_hyp_i {m : ℕ} (hp23 : 23 ≤ p) (hp4 : (m : ℝ) ^ (0.4 : ℝ) ≤ p) (hpm : (p : ℝ) ≤ 4 * √(m : ℝ))
    (hL : finrank (ZMod p) L = 3) {μ : L} (hμ : μ ∉ Set.range (algebraMap (ZMod p) L))
    (ω : Pairs m → Bool) (hS3 : GoodS3 (seidelOf ω)) (h0 : geomMult (F := L) 1 (-1) μ ω = 0) :
    prob (fun ξ : Fin m → Bool => geomMult (F := L) 1 (-1) μ (succPairs ω ξ) = 1) ≤
      1 / (p : ℝ) ^ 3 + Real.exp (-(cSEd * m) / 2) := by
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
  exact prob_quadL3_le hS3 hp23 hp4 hpm (isGenRoot_minpoly_three hL hμ) (natDegree_minpoly_eq_three hL hμ)
    hdet (-μ)

theorem rank3_hyp_ii {m : ℕ} (hp23 : 23 ≤ p) (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (hp4 : (m : ℝ) ^ (0.4 : ℝ) ≤ p) (hL : finrank (ZMod p) L = 3) {μ : L}
    (hμ : μ ∉ Set.range (algebraMap (ZMod p) L)) (ω : Pairs m → Bool) (hSE : GoodSEd 3 (seidelOf ω)) :
    prob (fun ξ : Fin m → Bool => ∀ k ∈ LinearMap.ker (shiftedMat (F := L) 1 (-1) μ ω).mulVecLin,
        twoValued (1 : L) (-1) ξ ⬝ᵥ k = 0) ≤
      ((Fintype.card L : ℝ) ^ geomMult (F := L) 1 (-1) μ ω)⁻¹ + Real.exp (-2 * cSEd * m) := by
  have h := prob_perp_eigsp_le hSE hp23 hpm (fun _ => hp4) (isGenRoot_minpoly_three hL hμ)
    (natDegree_minpoly_eq_three hL hμ) _ (ker_shiftedMat_le_eigsp (p := p) μ ω)
  unfold geomMult corank
  rw [card_eq_cube_of_finrank hL]
  push_cast
  rw [← pow_mul]
  exact h

end Hyps

def EvR3 (m : ℕ) (ω : Pairs m → Bool) : Prop := GoodS3 (seidelOf ω) ∧ GoodSEd 3 (seidelOf ω)

theorem prob_not_EvR3_le :
    ∀ᶠ m : ℕ in atTop, prob (fun ω : Pairs m → Bool => ¬ EvR3 m ω) ≤ 3 * Real.exp (-(m : ℝ) / 200) := by
  filter_upwards [prop_simple3, prop_SEd (d := 3) (by norm_num) (by norm_num)] with m h1 h2
  have h3 : Real.exp (-(m : ℝ) / 9) ≤ Real.exp (-(m : ℝ) / 200) := by
    apply Real.exp_le_exp.2
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  calc prob (fun ω : Pairs m → Bool => ¬ EvR3 m ω)
      ≤ prob (fun ω : Pairs m → Bool => ¬ GoodS3 (seidelOf ω) ∨ ¬ GoodSEd 3 (seidelOf ω)) :=
        prob_mono fun ω h => by
          unfold EvR3 at h
          tauto
    _ ≤ probSeidel m (fun T => ¬ GoodS3 T) + probSeidel m (fun T => ¬ GoodSEd 3 T) := prob_or_le _ _
    _ ≤ Real.exp (-(m : ℝ) / 200) + Real.exp (-(m : ℝ) / 9) := add_le_add h1 h2
    _ ≤ 3 * Real.exp (-(m : ℝ) / 200) := by
        have := Real.exp_pos (-(m : ℝ) / 200)
        linarith

theorem eventually_four_sqrt_le_exp :
    ∀ᶠ m : ℕ in atTop, 4 * √(m : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) := by
  have h := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).bound (by norm_num : (0 : ℝ) < 1))
  have h2 : ∀ᶠ m : ℕ in atTop, 2 * Real.log 4 ≤ (m : ℝ) ^ ((1 : ℝ) / 8) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [h, h2, eventually_ge_atTop 1] with m hm hm2 hm1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hmR
  have hr : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 8) := by positivity
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hr, one_mul] at hm
  have hpos : 0 < 4 * √(m : ℝ) := by positivity
  rw [← Real.log_le_iff_le_exp hpos, Real.log_mul (by norm_num) (Real.sqrt_pos.2 (by linarith)).ne',
    Real.log_sqrt (by linarith)]
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

theorem thm_rank3 :
    ∀ᶠ n : ℕ in atTop, ∀ (p : ℕ) [Fact p.Prime], (n : ℝ) ^ (0.4 : ℝ) ≤ p → (p : ℝ) ≤ 2 * √(n : ℝ) →
      ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], finrank (ZMod p) L = 3 →
      ∀ μ : L, μ ∉ Set.range (algebraMap (ZMod p) L) →
        prob (fun ω : Pairs n → Bool => 1 ≤ geomMult (F := L) 1 (-1) μ ω) ≤
          1 / (p : ℝ) ^ 3 + 1.2 / ((p : ℝ) ^ 3) ^ 2 + Real.exp (-cRK * n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 prob_not_EvR3_le
  obtain ⟨M, hM⟩ := eventually_atTop.1 eventually_four_sqrt_le_exp
  have hA : ∀ᶠ n : ℕ in atTop, N ≤ (3 * n + 3) / 4 ∧ M ≤ (3 * n + 3) / 4 := by
    filter_upwards [eventually_ge_atTop (2 * N + 2 * M)] with n hn
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
  have h23 : ∀ᶠ n : ℕ in atTop, (23 : ℝ) ≤ (n : ℝ) ^ (0.4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.4)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hA, hC, h23, rankp_err_eventually, eventually_ge_atTop 4]
    with n hA hC hn23 hD hn4
  intro p _ hpn4 hpn L _ _ _ hL μ hμ
  have hp23 : 23 ≤ p := by
    have : (23 : ℝ) ≤ p := hn23.trans hpn4
    exact_mod_cast this
  have hp2 : p ≠ 2 := by omega
  set m0 := (3 * n + 3) / 4 with hm0
  set ϖ := Real.exp (-(cPT * m0) / 2) with hϖ
  have hp4 : ∀ m, m ≤ n → (m : ℝ) ^ (0.4 : ℝ) ≤ p := fun m hm =>
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hm) (by norm_num)).trans hpn4
  have hpsq : ∀ m, m0 ≤ m → (p : ℝ) ≤ 4 * √(m : ℝ) := by
    intro m hm
    refine hpn.trans ?_
    have h1 := (m0_bounds n).1
    have h2 : (m0 : ℝ) ≤ m := by exact_mod_cast hm
    have h3 : √(4 * (n : ℝ)) ≤ √(16 * (m : ℝ)) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num)] at h3
    have e4 : √(4 : ℝ) = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have e16 : √(16 : ℝ) = 4 := by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [e4, e16] at h3
    exact h3
  have hpm : ∀ m, m0 ≤ m → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) :=
    fun m hm => (hpsq m hm).trans (hM m (hA.2.trans hm))
  have hcard : (Fintype.card L : ℝ) = (p : ℝ) ^ 3 := by
    rw [card_eq_cube_of_finrank hL]
    push_cast
    ring
  have hi : ∀ m, m0 ≤ m → m < n → ∀ ω, EvR3 m ω → geomMult (F := L) 1 (-1) μ ω = 0 →
      prob (fun ξ : Fin m → Bool => geomMult (F := L) 1 (-1) μ (succPairs ω ξ) = 1) ≤
        (Fintype.card L : ℝ)⁻¹ + ϖ := by
    intro m hm0' hmn ω hE h0
    rw [hcard, ← one_div]
    refine (rank3_hyp_i hp23 (hp4 m hmn.le) (hpsq m hm0') hL hμ ω hE.1 h0).trans (add_le_add le_rfl ?_)
    apply Real.exp_le_exp.2
    have : (m0 : ℝ) ≤ m := by exact_mod_cast hm0'
    have h1 := cPT_pos
    have h3 : (0 : ℝ) ≤ m0 := Nat.cast_nonneg _
    have h4 : cPT ≤ cSEd := by
      unfold cPT cSEd
      exact Real.exp_le_exp.2 (by norm_num)
    nlinarith
  have hii : ∀ m, m0 ≤ m → m < n → ∀ ω, EvR3 m ω → 1 ≤ geomMult (F := L) 1 (-1) μ ω →
      prob (fun ξ : Fin m → Bool => ∀ k ∈ LinearMap.ker (shiftedMat (F := L) 1 (-1) μ ω).mulVecLin,
        twoValued (1 : L) (-1) ξ ⬝ᵥ k = 0) ≤
        ((Fintype.card L : ℝ) ^ geomMult (F := L) 1 (-1) μ ω)⁻¹ + ϖ := by
    intro m hm0' hmn ω hE _
    refine (rank3_hyp_ii hp23 (hpm m hm0') (hp4 m hmn.le) hL hμ ω hE.2).trans (add_le_add le_rfl ?_)
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
    rw [card_eq_cube_of_finrank hL]
    exact hp23.trans (Nat.le_self_pow (by norm_num) p)
  have hcor := lem_corank (F := L) (one_ne_neg_one_ext (p := p) hp2) hq μ hn4 (Real.exp_pos _).le hC EvR3
    hi hii
  rw [hcard] at hcor
  have hsum : prob (fun ω : Pairs n → Bool => ¬ EaccRec EvR3 m0 n ω) ≤
      n * (3 * Real.exp (-(m0 : ℝ) / 200)) := by
    refine (prob_not_EaccRec_le EvR3 m0 n).trans ?_
    calc ∑ j ∈ Ico m0 n, prob (fun ω : Pairs j → Bool => ¬ EvR3 j ω)
        ≤ ∑ _j ∈ Ico m0 n, 3 * Real.exp (-(m0 : ℝ) / 200) := by
          refine sum_le_sum fun j hj => ?_
          have hj0 : m0 ≤ j := (mem_Ico.1 hj).1
          refine (hN j (hA.1.trans hj0)).trans ?_
          gcongr
      _ = ((n - m0 : ℕ) : ℝ) * (3 * Real.exp (-(m0 : ℝ) / 200)) := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ n * (3 * Real.exp (-(m0 : ℝ) / 200)) := by
          gcongr
          exact_mod_cast Nat.sub_le n m0
  have h2 := hcor.2
  calc prob (fun ω : Pairs n → Bool => 1 ≤ geomMult (F := L) 1 (-1) μ ω)
      ≤ 1 / (p : ℝ) ^ 3 + 1.2 / ((p : ℝ) ^ 3) ^ 2 + 2 * ϖ +
          C0 * (0.163 : ℝ) ^ (((n : ℝ) - m0 - 2) / 2) +
          prob (fun ω : Pairs n → Bool => ¬ EaccRec EvR3 m0 n ω) := h2
    _ ≤ 1 / (p : ℝ) ^ 3 + 1.2 / ((p : ℝ) ^ 3) ^ 2 + Real.exp (-cRK * n) := by linarith

end DGS
