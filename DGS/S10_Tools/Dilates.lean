module

public import DGS.S10_Tools.Signs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

open Finset
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

def normSqLift (y : ι → ZMod p) : ℤ := ∑ j, (y j).valMinAbs ^ 2

omit [Fact (Nat.Prime p)] [DecidableEq ι] in
theorem normSqLift_nonneg (y : ι → ZMod p) : 0 ≤ normSqLift y :=
  sum_nonneg fun _j _ => sq_nonneg _

omit [DecidableEq ι] in
theorem normSqLift_le (y : ι → ZMod p) (z : ι → ℤ) (hz : ∀ j, ((z j : ℤ) : ZMod p) = y j) :
    normSqLift y ≤ ∑ j, z j ^ 2 := by
  refine sum_le_sum fun j _ => ?_
  have h := ZMod.natAbs_min_of_le_div_two p (y j).valMinAbs (z j)
    (by rw [ZMod.coe_valMinAbs, hz]) (ZMod.natAbs_valMinAbs_le (y j))
  have h1 : (y j).valMinAbs ^ 2 = (((y j).valMinAbs.natAbs : ℕ) : ℤ) ^ 2 := by
    rw [Int.natCast_natAbs, sq_abs]
  have h2 : z j ^ 2 = (((z j).natAbs : ℕ) : ℤ) ^ 2 := by
    rw [Int.natCast_natAbs, sq_abs]
  rw [h1, h2]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast h) 2

noncomputable def muMin (w : ι → ZMod p) : ℤ :=
  (univ.filter fun c : ZMod p => c ≠ 0).inf' ⟨1, by simp⟩ fun c => normSqLift fun j => c * w j

omit [DecidableEq ι] in
theorem muMin_le (w : ι → ZMod p) {c : ZMod p} (hc : c ≠ 0) :
    muMin w ≤ normSqLift fun j => c * w j :=
  inf'_le _ (by simp [hc])

omit [DecidableEq ι] in
theorem exists_muMin_eq (w : ι → ZMod p) :
    ∃ c : ZMod p, c ≠ 0 ∧ muMin w = normSqLift fun j => c * w j := by
  obtain ⟨c, hc, h⟩ := exists_mem_eq_inf' (s := univ.filter fun c : ZMod p => c ≠ 0)
    ⟨1, by simp⟩ (fun c => normSqLift fun j => c * w j)
  exact ⟨c, (mem_filter.1 hc).2, h⟩

omit [DecidableEq ι] in
theorem muMin_nonneg (w : ι → ZMod p) : 0 ≤ muMin w := by
  obtain ⟨c, -, h⟩ := exists_muMin_eq w
  rw [h]
  exact normSqLift_nonneg _

theorem abs_cos_pi_mul_le {θ : ℝ} (hθ : |θ| ≤ 1 / 2) : |Real.cos (π * θ)| ≤ Real.exp (-2 * θ ^ 2) := by
  have hx : |π * θ| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hnn : 0 ≤ Real.cos (π * θ) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [abs_le.1 hx]
  rw [abs_of_nonneg hnn]
  have h1 := Real.cos_le_one_sub_mul_cos_sq (x := π * θ) (by linarith [Real.pi_pos])
  have h2 : 1 - 2 / π ^ 2 * (π * θ) ^ 2 = 1 - 2 * θ ^ 2 := by
    field_simp
  have h3 := Real.add_one_le_exp (-2 * θ ^ 2)
  linarith

theorem cosP_eq_of_cast (x : ZMod p) (z : ℤ) (hz : ((z : ℤ) : ZMod p) = x) :
    cosP x = Real.cos (2 * π * z / p) := by
  have hdvd : (p : ℤ) ∣ z - (x.val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hz, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨k, hk⟩ := hdvd
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hz' : (z : ℝ) = x.val + p * k := by
    have : (z : ℤ) = x.val + p * k := by linarith
    exact_mod_cast this
  rw [cosP, hz']
  have : 2 * π * ((x.val : ℝ) + p * k) / p = 2 * π * x.val / p + k * (2 * π) := by
    field_simp
  rw [this, Real.cos_add_int_mul_two_pi]

theorem abs_cosP_eq (x : ZMod p) :
    |cosP x| = |Real.cos (π * (((2 * x).valMinAbs : ℤ) : ℝ) / p)| := by
  have hdvd : (p : ℤ) ∣ (2 * x).valMinAbs - 2 * (x.val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [ZMod.coe_valMinAbs]
  obtain ⟨k, hk⟩ := hdvd
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hb : (((2 * x).valMinAbs : ℤ) : ℝ) = 2 * x.val + p * k := by
    have : (2 * x).valMinAbs = 2 * (x.val : ℤ) + p * k := by linarith
    exact_mod_cast this
  rw [hb, cosP]
  have : π * (2 * (x.val : ℝ) + p * k) / p = 2 * π * x.val / p + k * π := by
    field_simp
  rw [this, Real.cos_add_int_mul_pi, abs_mul]
  simp

theorem abs_cosP_le_exp (x : ZMod p) :
    |cosP x| ≤ Real.exp (-2 * ((((2 * x).valMinAbs : ℤ) : ℝ) / p) ^ 2) := by
  rw [abs_cosP_eq]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hθ : |(((2 * x).valMinAbs : ℤ) : ℝ) / p| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have h1 := ZMod.natAbs_valMinAbs_le (2 * x)
    have h2 : (((2 * x).valMinAbs.natAbs : ℕ) : ℝ) ≤ ((p / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : ((p / 2 : ℕ) : ℝ) ≤ (p : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have : (p / 2) * 2 ≤ p := Nat.div_mul_le_self p 2
      exact_mod_cast this
    rw [Nat.cast_natAbs, Int.cast_abs] at h2
    linarith
  have := abs_cos_pi_mul_le hθ
  rwa [mul_div_assoc]

omit [DecidableEq ι] in
theorem lem_dilates (hp2 : p ≠ 2) (w : ι → ZMod p) {c : ZMod p} (hc : c ≠ 0) :
    ∏ j, |cosP (c * w j)| ≤ Real.exp (-2 * (muMin w : ℝ) / (p : ℝ) ^ 2) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h2c : (2 : ZMod p) * c ≠ 0 := by
    refine mul_ne_zero ?_ hc
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h2
    exact hp2 this
  calc ∏ j, |cosP (c * w j)|
      ≤ ∏ j, Real.exp (-2 * ((((2 * (c * w j)).valMinAbs : ℤ) : ℝ) / p) ^ 2) :=
        prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => abs_cosP_le_exp _
    _ = Real.exp (-2 * ((normSqLift fun j => (2 * c) * w j : ℤ) : ℝ) / (p : ℝ) ^ 2) := by
        rw [← Real.exp_sum]
        congr 1
        have h1 : ((normSqLift fun j => (2 * c) * w j : ℤ) : ℝ) =
            ∑ j, (((2 * (c * w j)).valMinAbs : ℤ) : ℝ) ^ 2 := by
          rw [normSqLift]
          push_cast
          refine sum_congr rfl fun j _ => ?_
          rw [mul_assoc]
        rw [h1, mul_div_assoc, Finset.sum_div, Finset.mul_sum]
        refine sum_congr rfl fun j _ => ?_
        ring
    _ ≤ Real.exp (-2 * (muMin w : ℝ) / (p : ℝ) ^ 2) := by
        rw [Real.exp_le_exp]
        have h := muMin_le w h2c
        have h' : (muMin w : ℝ) ≤ ((normSqLift fun j => (2 * c) * w j : ℤ) : ℝ) := by
          exact_mod_cast h
        have hp2' : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
        rw [div_le_div_iff_of_pos_right hp2']
        linarith

theorem lem_dilates_rho (hp2 : p ≠ 2) (w : ι → ZMod p) :
    rhoG w ≤ rhoHatP w ∧ rhoHatP w ≤ 1 / p + Real.exp (-2 * (muMin w : ℝ) / (p : ℝ) ^ 2) := by
  refine ⟨rhoG_le_rhoHatP w, ?_⟩
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set E := Real.exp (-2 * (muMin w : ℝ) / (p : ℝ) ^ 2) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  unfold rhoHatP
  rw [← add_sum_erase _ _ (mem_univ (0 : ZMod p))]
  have h0 : ∏ j, |cosP ((0 : ZMod p) * w j)| = 1 := by
    simp [cosP]
  have hrest : ∑ c ∈ univ.erase (0 : ZMod p), ∏ j, |cosP (c * w j)| ≤ (p - 1 : ℝ) * E := by
    calc ∑ c ∈ univ.erase (0 : ZMod p), ∏ j, |cosP (c * w j)|
        ≤ ∑ c ∈ univ.erase (0 : ZMod p), E :=
          sum_le_sum fun c hc => lem_dilates hp2 w (ne_of_mem_erase hc)
      _ = (p - 1 : ℝ) * E := by
          rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, ZMod.card, nsmul_eq_mul]
          have : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
          push_cast [this]
          ring
  rw [h0, mul_add, mul_one]
  have : (p : ℝ)⁻¹ * ((p - 1 : ℝ) * E) ≤ E := by
    rw [← mul_assoc, inv_mul_eq_div]
    have h1 : (p - 1 : ℝ) / p ≤ 1 := by
      rw [div_le_one hp]
      linarith
    calc (p - 1 : ℝ) / p * E ≤ 1 * E := mul_le_mul_of_nonneg_right h1 hE0
      _ = E := one_mul E
  have h2 := mul_le_mul_of_nonneg_left hrest (inv_nonneg.2 hp.le)
  rw [one_div]
  linarith

end DGS
