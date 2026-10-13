module

public import DGS.S11_Deg1.FourierInv
public import DGS.S11_Deg1.SEthm
public import DGS.S11_Deg1.Corank

@[expose] public section

open Finset Filter Topology Matrix
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime]

theorem shiftedMat_eq_modP {m : ℕ} (μ : ZMod p) (ω : Pairs m → Bool) :
    shiftedMat (F := ZMod p) 1 (-1) μ ω = modP p (seidelOf ω) - μ • 1 := rfl

theorem rankp_hyp_i {m : ℕ} (hp23 : 23 ≤ p) (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (μ : ZMod p) (ω : Pairs m → Bool) (hPT : GoodPT (seidelOf ω)) (h0 : geomMult 1 (-1) μ ω = 0) :
    prob (fun ξ : Fin m → Bool => geomMult 1 (-1) μ (succPairs ω ξ) = 1) ≤
      1 / p + Real.exp (-(cPT * m) / 2) := by
  set L := shiftedMat (F := ZMod p) 1 (-1) μ ω with hL
  have hLT : Lᵀ = L := shiftedMat_transpose μ ω
  have hdet : IsUnit L.det := by
    rw [isUnit_iff_ne_zero]
    intro hd
    obtain ⟨v, hv0, hv⟩ := (exists_mulVec_eq_zero_iff).2 hd
    have hpos : 0 < geomMult 1 (-1) μ ω := by
      unfold geomMult corank
      refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact hv
      · intro h
        exact hv0 (congrArg Subtype.val h)
    omega
  have hev : ∀ ξ : Fin m → Bool, geomMult 1 (-1) μ (succPairs ω ξ) = 1 ↔
      sgnP p ξ ⬝ᵥ (L⁻¹ *ᵥ sgnP p ξ) = -μ := by
    intro ξ
    unfold geomMult
    rw [shiftedMat_succPairs, (lem_border_inv hLT hdet).2.1, sgnP_eq_twoValued]
    exact eq_comm
  rw [prob_congr hev]
  exact prob_quad_eq_le _ _ (Real.exp_pos _).le fun t ht =>
    quadSum_resolvent_le hPT hp23 hpm μ hdet ht

theorem rankp_hyp_ii {m : ℕ} (hp23 : 23 ≤ p) (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (μ : ZMod p) (ω : Pairs m → Bool) (hSE : GoodSE (seidelOf ω)) :
    prob (fun ξ : Fin m → Bool => ∀ k ∈ LinearMap.ker (shiftedMat (F := ZMod p) 1 (-1) μ ω).mulVecLin,
        twoValued (1 : ZMod p) (-1) ξ ⬝ᵥ k = 0) ≤
      ((p : ℝ) ^ geomMult 1 (-1) μ ω)⁻¹ + Real.exp (-2 * cSE * m) := by
  have hp2 : p ≠ 2 := by omega
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold geomMult corank
  refine prob_perp_le _ (Real.exp_pos _).le fun v hv hv0 => ?_
  have hvμ : (seidelOf ω).map (Int.castRingHom (ZMod p)) *ᵥ v = μ • v := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, shiftedMat_eq_modP, sub_mulVec, smul_mulVec,
      one_mulVec, sub_eq_zero] at hv
    exact hv
  have h1 := muMin_gt_of_goodSE hSE hp23 hpm hv0 hvμ
  have h2 := lem_dilates hp2 v (one_ne_zero (α := ZMod p))
  simp only [one_mul] at h2
  refine h2.trans (Real.exp_le_exp.2 ?_)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

noncomputable def cRK : ℝ := cPT / 8

theorem cRK_pos : 0 < cRK := by unfold cRK; have := cPT_pos; positivity

theorem cRK_le : cRK ≤ 1 / 800000 := by unfold cRK; have := cPT_le; linarith

theorem C0_pos : 0 < C0 := by
  unfold C0
  have : 0 ≤ ∑' r : ℕ, (10 : ℝ) ^ (r + 1) * (2 : ℝ) ^ (-(((r + 1 : ℕ) : ℝ) ^ 2 / 4)) :=
    tsum_nonneg fun r => by positivity
  linarith

theorem eventually_const_le_exp {a C : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, C ≤ Real.exp (a * n) := by
  filter_upwards [eventually_ge_atTop ⌈C / a⌉₊] with n hn
  have h1 : C / a ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h2 := Real.add_one_le_exp (a * n)
  have h3 : C ≤ a * n := by
    rw [div_le_iff₀ ha] at h1
    linarith
  linarith

theorem eventually_mul_le_exp {b K : ℝ} (hb : 0 < b) (_hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, K * n ≤ Real.exp (b * n) := by
  filter_upwards [eventually_ge_atTop ⌈2 * K / b ^ 2⌉₊] with n hn
  have h1 : 2 * K / b ^ 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ b * n)
  have h3 : 2 * K ≤ b ^ 2 * n := by
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have h4 : K * n ≤ (b * n) ^ 2 / 2 := by nlinarith
  nlinarith

theorem m0_bounds (n : ℕ) :
    3 * (n : ℝ) / 4 ≤ (((3 * n + 3) / 4 : ℕ) : ℝ) ∧ (((3 * n + 3) / 4 : ℕ) : ℝ) ≤ 3 * (n : ℝ) / 4 + 1 := by
  have h1 : 3 * n ≤ 4 * ((3 * n + 3) / 4) := by omega
  have h2 : 4 * ((3 * n + 3) / 4) ≤ 3 * n + 3 := by omega
  have h1' : (3 * n : ℝ) ≤ 4 * (((3 * n + 3) / 4 : ℕ) : ℝ) := by exact_mod_cast h1
  have h2' : 4 * (((3 * n + 3) / 4 : ℕ) : ℝ) ≤ 3 * n + 3 := by exact_mod_cast h2
  constructor <;> linarith

theorem eventually_rpow_ninth_le :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ((1 : ℝ) / 9) ≤ (((3 * n + 3) / 4 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) := by
  filter_upwards [eventually_ge_atTop (2 ^ 72)] with n hn
  have hnR : (2 : ℝ) ^ 72 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnR
  have hm0 : (n : ℝ) / 2 ≤ (((3 * n + 3) / 4 : ℕ) : ℝ) := by
    have := (m0_bounds n).1
    linarith
  have h72 : (2 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 72) := by
    have h := Real.rpow_le_rpow (by positivity) hnR (by norm_num : (0 : ℝ) ≤ 1 / 72)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
    norm_num at h
    exact h
  have h8 : (2 : ℝ) ^ ((1 : ℝ) / 8) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 : ℝ) / 8 ≤ 1)
    rwa [Real.rpow_one] at this
  have hsplit : (n : ℝ) ^ ((1 : ℝ) / 8) = (n : ℝ) ^ ((1 : ℝ) / 9) * (n : ℝ) ^ ((1 : ℝ) / 72) := by
    rw [← Real.rpow_add hn0]
    norm_num
  have hdiv : ((n : ℝ) / 2) ^ ((1 : ℝ) / 8) = (n : ℝ) ^ ((1 : ℝ) / 8) / (2 : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.div_rpow hn0.le (by norm_num) _
  have h9 : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 9) := Real.rpow_nonneg hn0.le _
  have h2p : 0 < (2 : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos (by norm_num) _
  calc (n : ℝ) ^ ((1 : ℝ) / 9) ≤ ((n : ℝ) / 2) ^ ((1 : ℝ) / 8) := by
        rw [hdiv, hsplit, le_div_iff₀ h2p]
        nlinarith
    _ ≤ (((3 * n + 3) / 4 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) :=
        Real.rpow_le_rpow (by positivity) hm0 (by norm_num)

theorem rankp_err_eventually :
    ∀ᶠ n : ℕ in atTop, 2 * Real.exp (-(cPT * ((3 * n + 3) / 4 : ℕ)) / 2) +
      C0 * (0.163 : ℝ) ^ (((n : ℝ) - ((3 * n + 3) / 4 : ℕ) - 2) / 2) +
      n * (3 * Real.exp (-(((3 * n + 3) / 4 : ℕ) : ℝ) / 200)) ≤ Real.exp (-cRK * n) := by
  have hc := cRK_pos
  have hc' := cRK_le
  have hC0 := C0_pos
  filter_upwards [eventually_const_le_exp (a := 2 * cRK) (C := 6) (by positivity),
    eventually_const_le_exp (a := 0.1875 - cRK) (C := 3 * C0 * Real.exp 2.25) (by linarith),
    eventually_mul_le_exp (b := 3 / 800 - cRK) (K := 9) (by linarith) (by norm_num),
    eventually_ge_atTop 12] with n h1 h2 h3 h4
  obtain ⟨hm0a, hm0b⟩ := m0_bounds n
  set m0 : ℝ := (((3 * n + 3) / 4 : ℕ) : ℝ) with hm0
  have hn12 : (12 : ℝ) ≤ n := by exact_mod_cast h4
  have hcPT : cPT = 8 * cRK := by unfold cRK; ring
  have t1 : 2 * Real.exp (-(cPT * m0) / 2) ≤ Real.exp (-cRK * n) / 3 := by
    have e1 : Real.exp (-(cPT * m0) / 2) ≤ Real.exp (-(3 * cRK) * n) := by
      apply Real.exp_le_exp.2
      rw [hcPT]
      nlinarith
    have e2 : Real.exp (-(3 * cRK) * n) * Real.exp (2 * cRK * n) = Real.exp (-cRK * n) := by
      rw [← Real.exp_add]
      ring_nf
    have e3 : 0 < Real.exp (-(3 * cRK) * n) := Real.exp_pos _
    nlinarith
  have t2 : C0 * (0.163 : ℝ) ^ (((n : ℝ) - m0 - 2) / 2) ≤ Real.exp (-cRK * n) / 3 := by
    have hx0 : 0 ≤ ((n : ℝ) - m0 - 2) / 2 := by linarith
    have hb : (0.163 : ℝ) ≤ Real.exp (-1.5) := by
      have := exp_three_halves_le
      rw [show (-1.5 : ℝ) = -(3 / 2) by norm_num, Real.exp_neg]
      rw [le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
      linarith
    have e1 : (0.163 : ℝ) ^ (((n : ℝ) - m0 - 2) / 2) ≤ Real.exp (-1.5 * (((n : ℝ) - m0 - 2) / 2)) := by
      rw [Real.exp_mul]
      exact Real.rpow_le_rpow (by norm_num) hb hx0
    have e2 : Real.exp (-1.5 * (((n : ℝ) - m0 - 2) / 2)) ≤ Real.exp 2.25 * Real.exp (-0.1875 * n) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith
    have e3 : Real.exp (-0.1875 * n) * Real.exp ((0.1875 - cRK) * n) = Real.exp (-cRK * n) := by
      rw [← Real.exp_add]
      ring_nf
    have e4 : 0 < Real.exp (-0.1875 * n) := Real.exp_pos _
    calc C0 * (0.163 : ℝ) ^ (((n : ℝ) - m0 - 2) / 2) ≤ C0 * (Real.exp 2.25 * Real.exp (-0.1875 * n)) :=
          mul_le_mul_of_nonneg_left (e1.trans e2) hC0.le
      _ ≤ Real.exp (-cRK * n) / 3 := by nlinarith
  have t3 : n * (3 * Real.exp (-m0 / 200)) ≤ Real.exp (-cRK * n) / 3 := by
    have e1 : Real.exp (-m0 / 200) ≤ Real.exp (-(3 / 800) * n) := by
      apply Real.exp_le_exp.2
      linarith
    have e3 : Real.exp (-(3 / 800) * n) * Real.exp ((3 / 800 - cRK) * n) = Real.exp (-cRK * n) := by
      rw [← Real.exp_add]
      ring_nf
    have e4 : 0 < Real.exp (-(3 / 800) * n) := Real.exp_pos _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc (n : ℝ) * (3 * Real.exp (-m0 / 200)) ≤ n * (3 * Real.exp (-(3 / 800) * n)) := by gcongr
      _ ≤ Real.exp (-cRK * n) / 3 := by nlinarith
  linarith

def EvRK (m : ℕ) (ω : Pairs m → Bool) : Prop := GoodSE (seidelOf ω) ∧ GoodPT (seidelOf ω)

theorem prob_not_EvRK_le
    (hPT : ∀ᶠ m : ℕ in atTop, probSeidel m (fun T => ¬ GoodPT T) ≤ Real.exp (-(m : ℝ) / 200)) :
    ∀ᶠ m : ℕ in atTop, prob (fun ω : Pairs m → Bool => ¬ EvRK m ω) ≤ 3 * Real.exp (-(m : ℝ) / 200) := by
  filter_upwards [thm_SEplus, hPT] with m h1 h2
  have h3 : (2 : ℝ) ^ (-(m : ℝ) / 8) ≤ Real.exp (-(m : ℝ) / 200) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.2
    have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  calc prob (fun ω : Pairs m → Bool => ¬ EvRK m ω)
      ≤ prob (fun ω : Pairs m → Bool => ¬ GoodSE (seidelOf ω) ∨ ¬ GoodPT (seidelOf ω)) :=
        prob_mono fun ω h => by
          unfold EvRK at h
          tauto
    _ ≤ probSeidel m (fun S => ¬ GoodSE S) + probSeidel m (fun T => ¬ GoodPT T) := prob_or_le _ _
    _ ≤ 2 * (2 : ℝ) ^ (-(m : ℝ) / 8) + Real.exp (-(m : ℝ) / 200) := add_le_add h1 h2
    _ ≤ 3 * Real.exp (-(m : ℝ) / 200) := by linarith

theorem thm_rankp_of
    (hPT : ∀ᶠ m : ℕ in atTop, probSeidel m (fun T => ¬ GoodPT T) ≤ Real.exp (-(m : ℝ) / 200)) :
    ∀ᶠ n : ℕ in atTop, ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p →
      (p : ℝ) ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 9)) → ∀ μ : ZMod p,
        prob (fun ω : Pairs n → Bool => 2 ≤ geomMult 1 (-1) μ ω) ≤
          1.2 / (p : ℝ) ^ 2 + Real.exp (-cRK * n) ∧
        prob (fun ω : Pairs n → Bool => 1 ≤ geomMult 1 (-1) μ ω) ≤
          1 / p + 1.2 / (p : ℝ) ^ 2 + Real.exp (-cRK * n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (prob_not_EvRK_le hPT)
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
  intro p _ hp23 hpn μ
  have hp2 : p ≠ 2 := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set m0 := (3 * n + 3) / 4 with hm0
  set ϖ := Real.exp (-(cPT * m0) / 2) with hϖ
  have hpm : ∀ m, m0 ≤ m → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) := by
    intro m hm
    refine hpn.trans (Real.exp_le_exp.2 (hB.trans ?_))
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hm) (by norm_num)
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  have hi : ∀ m, m0 ≤ m → m < n → ∀ ω, EvRK m ω → geomMult 1 (-1) μ ω = 0 →
      prob (fun ξ : Fin m → Bool => geomMult 1 (-1) μ (succPairs ω ξ) = 1) ≤
        (Fintype.card (ZMod p) : ℝ)⁻¹ + ϖ := by
    intro m hm0' hmn ω hE h0
    rw [hcard, ← one_div]
    refine (rankp_hyp_i hp23 (hpm m hm0') μ ω hE.2 h0).trans (add_le_add le_rfl ?_)
    apply Real.exp_le_exp.2
    have : (m0 : ℝ) ≤ m := by exact_mod_cast hm0'
    have := cPT_pos
    nlinarith
  have hii : ∀ m, m0 ≤ m → m < n → ∀ ω, EvRK m ω → 1 ≤ geomMult 1 (-1) μ ω →
      prob (fun ξ : Fin m → Bool => ∀ k ∈ LinearMap.ker (shiftedMat (F := ZMod p) 1 (-1) μ ω).mulVecLin,
        twoValued (1 : ZMod p) (-1) ξ ⬝ᵥ k = 0) ≤
        ((Fintype.card (ZMod p) : ℝ) ^ geomMult 1 (-1) μ ω)⁻¹ + ϖ := by
    intro m hm0' hmn ω hE _
    rw [hcard]
    refine (rankp_hyp_ii hp23 (hpm m hm0') μ ω hE.1).trans (add_le_add le_rfl ?_)
    apply Real.exp_le_exp.2
    have : (m0 : ℝ) ≤ m := by exact_mod_cast hm0'
    have h1 := cPT_le
    have h2 := cPT_pos
    have h3 : (0 : ℝ) ≤ m0 := Nat.cast_nonneg _
    unfold cSE
    nlinarith
  have hq : 23 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; exact hp23
  have hcor := lem_corank (F := ZMod p) (one_ne_neg_one_zmod hp2) hq μ hn4 (Real.exp_pos _).le hC EvRK
    hi hii
  rw [hcard] at hcor
  have hsum : prob (fun ω : Pairs n → Bool => ¬ EaccRec EvRK m0 n ω) ≤
      n * (3 * Real.exp (-(m0 : ℝ) / 200)) := by
    refine (prob_not_EaccRec_le EvRK m0 n).trans ?_
    calc ∑ j ∈ Ico m0 n, prob (fun ω : Pairs j → Bool => ¬ EvRK j ω)
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
  have hpow : (0.163 : ℝ) ^ (((n : ℝ) - m0 - 1) / 2) ≤ (0.163 : ℝ) ^ (((n : ℝ) - m0 - 2) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
  have hC0 := C0_pos
  have hϖ0 : 0 ≤ ϖ := (Real.exp_pos _).le
  constructor
  · have h1 := hcor.1 n (le_refl _ |>.trans' (by omega)) le_rfl
    calc prob (fun ω : Pairs n → Bool => 2 ≤ geomMult 1 (-1) μ ω)
        ≤ prob (fun ω : Pairs n → Bool => (2 ≤ geomMult 1 (-1) μ ω ∧ EaccRec EvRK m0 n ω) ∨
            ¬ EaccRec EvRK m0 n ω) := prob_mono fun ω h => by tauto
      _ ≤ prob (fun ω : Pairs n → Bool => 2 ≤ geomMult 1 (-1) μ ω ∧ EaccRec EvRK m0 n ω) +
            prob (fun ω : Pairs n → Bool => ¬ EaccRec EvRK m0 n ω) := prob_or_le _ _
      _ ≤ (1.2 / (p : ℝ) ^ 2 + ϖ + C0 * (0.163 : ℝ) ^ (((n : ℝ) - m0 - 1) / 2)) +
            n * (3 * Real.exp (-(m0 : ℝ) / 200)) := add_le_add h1 hsum
      _ ≤ 1.2 / (p : ℝ) ^ 2 + Real.exp (-cRK * n) := by
          have := mul_le_mul_of_nonneg_left hpow hC0.le
          linarith
  · have h2 := hcor.2
    calc prob (fun ω : Pairs n → Bool => 1 ≤ geomMult 1 (-1) μ ω)
        ≤ 1 / (p : ℝ) + 1.2 / (p : ℝ) ^ 2 + 2 * ϖ + C0 * (0.163 : ℝ) ^ (((n : ℝ) - m0 - 2) / 2) +
            prob (fun ω : Pairs n → Bool => ¬ EaccRec EvRK m0 n ω) := h2
      _ ≤ 1 / p + 1.2 / (p : ℝ) ^ 2 + Real.exp (-cRK * n) := by linarith

end DGS
