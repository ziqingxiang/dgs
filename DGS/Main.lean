module

public import DGS.Core.Components
public import DGS.S03_Prelim.LocalFailures
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter Topology Real

namespace DGS

theorem not_isDGS_cases {n : ℕ} (G : SimpleGraph (Fin n)) (ε : ℝ) (hn2 : (2 : ℝ) < (n : ℝ) ^ (1 / 2 - ε))
    (hlog : (log n) ^ 6 < (n : ℝ) ^ (1 / 10 : ℝ)) (h : ¬ IsDGS G) :
    ¬ Controllable G ∨
    (∃ Q ∈ QG G, ¬ IsPermMatrix Q ∧ ∀ p : ℕ, p.Prime → p ∣ level Q → (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε)) ∨
    (∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 * logb 2 n ≤ (d : ℝ) ∧ E p d G) ∨
    (∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ) ∧ (p : ℝ) ≤ exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧
      1 ≤ d ∧ (d : ℝ) < 3 * logb 2 n ∧ E p d G) ∨
    (∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ exp ((log n) ^ 6) < (p : ℝ) ∧ 1 ≤ d ∧ E p d G) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hC, hA, hB, hM, hD⟩ := hcon
  apply h
  rw [thm_wangxu hC]
  intro Q hQ
  by_contra hperm
  obtain ⟨p, hp, hpdvd, hpbig⟩ := hA Q hQ hperm
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hpbig
    linarith
  obtain ⟨d, hd1, hE⟩ := lem_matesfail hQ hp hp2 hpdvd
  by_cases hdlarge : 3 * logb 2 n ≤ (d : ℝ)
  · exact hB p d hp hp2 hdlarge hE
  · push Not at hdlarge
    by_cases hpmod : (p : ℝ) ≤ exp ((n : ℝ) ^ (1 / 10 : ℝ))
    · exact hM p d hp hp2 hpbig hpmod hd1 hdlarge hE
    · push Not at hpmod
      exact hD p d hp hp2 (lt_trans (exp_lt_exp.2 hlog) hpmod) hd1 hE

theorem eventually_two_lt_rpow : ∀ᶠ n : ℕ in atTop, (2 : ℝ) < (n : ℝ) ^ (1 / 2 - 1 / 20 : ℝ) :=
  ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2 - 1 / 20)).comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop 2

theorem eventually_log_pow_lt_rpow : ∀ᶠ n : ℕ in atTop, (log n) ^ 6 < (n : ℝ) ^ (1 / 10 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop 6 (by norm_num : (0 : ℝ) < 1 / 10)).comp_tendsto
    tendsto_natCast_atTop_atTop
  have h2 := h.def (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [h2, eventually_ge_atTop 2] with n hn hn2
  simp only [Function.comp_apply, Real.norm_eq_abs] at hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ log n := Real.log_nonneg hn1
  have hpos : 0 < (n : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have e : (log n) ^ 6 = (log n) ^ (6 : ℝ) := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [abs_of_nonneg (Real.rpow_nonneg hlog _), abs_of_pos hpos] at hn
  rw [e]
  linarith

theorem main_of_components (hOT : ORourkeTouriStatement) (h22 : Thm22) (h23 : Thm23) (h24 : Thm24) (h26 : Thm26) :
    MainStatement := by
  have hA := h23 (1 / 20) (by norm_num) (by norm_num)
  have hM := h24 (1 / 20) (by norm_num) (by norm_num)
  have hNC : Tendsto (fun n : ℕ => probG n (fun G => ¬ Controllable G)) atTop (𝓝 0) := by
    have h1 := thm_OT hOT
    have : (fun n : ℕ => probG n (fun G => ¬ Controllable G)) =
        fun n : ℕ => 1 - probG n Controllable := by
      funext n
      rw [probG_eq_prob, probG_eq_prob, prob_compl]
    rw [this]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
  have hbound : ∀ᶠ n : ℕ in atTop, probG n (fun G => ¬ IsDGS G) ≤
      probG n (fun G => ¬ Controllable G) +
      (probG n (fun G => ∃ Q ∈ QG G, ¬ IsPermMatrix Q ∧ ∀ p : ℕ, p.Prime → p ∣ level Q →
          (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - 1 / 20 : ℝ)) +
        (probG n (fun G => ∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 * logb 2 n ≤ (d : ℝ) ∧ E p d G) +
          (probG n (fun G => ∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ (n : ℝ) ^ (1 / 2 - 1 / 20 : ℝ) < (p : ℝ) ∧
              (p : ℝ) ≤ exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧ 1 ≤ d ∧ (d : ℝ) < 3 * logb 2 n ∧ E p d G) +
            probG n (fun G => ∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ exp ((log n) ^ 6) < (p : ℝ) ∧ 1 ≤ d ∧
              E p d G)))) := by
    filter_upwards [eventually_two_lt_rpow, eventually_log_pow_lt_rpow] with n hn2 hlog
    simp only [probG_eq_prob]
    refine (prob_mono fun G hG => not_isDGS_cases G (1 / 20) hn2 hlog hG).trans ?_
    refine (prob_or_le _ _).trans (add_le_add le_rfl ?_)
    refine (prob_or_le _ _).trans (add_le_add le_rfl ?_)
    refine (prob_or_le _ _).trans (add_le_add le_rfl ?_)
    exact prob_or_le _ _
  have hsum := hNC.add (hA.add (h22.add (hM.add h26)))
  simp only [add_zero] at hsum
  have h0 : Tendsto (fun n : ℕ => probG n (fun G => ¬ IsDGS G)) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun n => prob_nonneg _) hbound hsum
  exact tendsto_prob_one_of_compl (Ω := fun n => SimpleGraph (Fin n)) (P := fun n => @IsDGS n) h0

end DGS
