module

public import DGS.S10_Tools.Signs
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Finset Set MeasureTheory
open scoped Real

namespace DGS

noncomputable def gaussW (σ : ℝ) (z : ℤ) : ℝ := Real.exp (-σ * (z : ℝ) ^ 2)

theorem gaussW_pos (σ : ℝ) (z : ℤ) : 0 < gaussW σ z := Real.exp_pos _

theorem gaussW_nonneg (σ : ℝ) (z : ℤ) : 0 ≤ gaussW σ z := (gaussW_pos σ z).le

theorem gaussW_neg (σ : ℝ) (z : ℤ) : gaussW σ (-z) = gaussW σ z := by
  simp [gaussW]

theorem gaussW_zero (σ : ℝ) : gaussW σ 0 = 1 := by simp [gaussW]

section Integral

variable {σ : ℝ}

theorem gauss_antitoneOn (hσ : 0 < σ) :
    AntitoneOn (fun x : ℝ => Real.exp (-σ * x ^ 2)) (Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  apply Real.exp_le_exp.2
  have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  nlinarith

theorem gauss_integrableOn (hσ : 0 < σ) :
    IntegrableOn (fun x : ℝ => Real.exp (-σ * x ^ 2)) (Ioi 0) :=
  (integrable_exp_neg_mul_sq hσ).integrableOn

theorem summable_gauss_nat (hσ : 0 < σ) : Summable fun n : ℕ => gaussW σ n := by
  have := (gauss_antitoneOn hσ).summable_of_integrableOn_Ioi_zero (gauss_integrableOn hσ)
    (fun t _ => (Real.exp_pos _).le)
  simpa [gaussW] using this

theorem tsum_gauss_succ_le (hσ : 0 < σ) :
    ∑' n : ℕ, gaussW σ ((n + 1 : ℕ) : ℤ) ≤ √(π / σ) / 2 := by
  have := (gauss_antitoneOn hσ).tsum_add_one_le_integral (gauss_integrableOn hσ)
    (fun t _ => (Real.exp_pos _).le)
  rw [integral_gaussian_Ioi] at this
  simpa [gaussW] using this

theorem summable_gauss_succ (hσ : 0 < σ) : Summable fun n : ℕ => gaussW σ ((n + 1 : ℕ) : ℤ) := by
  have h := (summable_nat_add_iff 1).2 (summable_gauss_nat hσ)
  simpa using h

theorem summable_gaussW (hσ : 0 < σ) : Summable (gaussW σ) := by
  refine Summable.of_nat_of_neg_add_one (summable_gauss_nat hσ) ?_
  have h := summable_gauss_succ hσ
  refine h.congr fun n => ?_
  rw [← gaussW_neg]
  push_cast
  ring_nf

theorem tsum_gaussW_le (hσ : 0 < σ) : ∑' z : ℤ, gaussW σ z ≤ 1 + √(π / σ) := by
  have h2 : Summable fun n : ℕ => gaussW σ (-((n : ℤ) + 1)) := by
    refine (summable_gauss_succ hσ).congr fun n => ?_
    rw [← gaussW_neg]
    push_cast
    ring_nf
  rw [tsum_of_nat_of_neg_add_one (summable_gauss_nat hσ) h2]
  have h3 : ∑' n : ℕ, gaussW σ (-((n : ℤ) + 1)) = ∑' n : ℕ, gaussW σ ((n + 1 : ℕ) : ℤ) := by
    congr 1
    funext n
    rw [← gaussW_neg]
    push_cast
    ring_nf
  have h4 : ∑' n : ℕ, gaussW σ (n : ℤ) = 1 + ∑' n : ℕ, gaussW σ ((n + 1 : ℕ) : ℤ) := by
    rw [(summable_gauss_nat hσ).tsum_eq_zero_add]
    simp [gaussW_zero]
  rw [h3, h4]
  have h5 := tsum_gauss_succ_le hσ
  linarith

end Integral

theorem tsum_exp_sq_succ_le {A : ℝ} (hA : 0 < A) :
    ∑' n : ℕ, Real.exp (-A * ((n : ℝ) + 1) ^ 2) ≤ Real.exp (-A) / (1 - Real.exp (-A)) := by
  set q := Real.exp (-A) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq, Real.exp_lt_one_iff]; linarith
  have hle : ∀ n : ℕ, Real.exp (-A * ((n : ℝ) + 1) ^ 2) ≤ q * q ^ n := by
    intro n
    rw [← pow_succ', hq, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have h1 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    push_cast
    nlinarith
  have hs : Summable fun n : ℕ => q * q ^ n := (summable_geometric_of_lt_one hq0 hq1).mul_left q
  calc ∑' n : ℕ, Real.exp (-A * ((n : ℝ) + 1) ^ 2) ≤ ∑' n : ℕ, q * q ^ n :=
        Summable.tsum_le_tsum hle (hs.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hle) hs
    _ = q / (1 - q) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

theorem summable_exp_sq_succ {A : ℝ} (hA : 0 < A) :
    Summable fun n : ℕ => Real.exp (-A * ((n : ℝ) + 1) ^ 2) := by
  set q := Real.exp (-A) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq, Real.exp_lt_one_iff]; linarith
  have hle : ∀ n : ℕ, Real.exp (-A * ((n : ℝ) + 1) ^ 2) ≤ q * q ^ n := by
    intro n
    rw [← pow_succ', hq, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have h1 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    push_cast
    nlinarith
  exact ((summable_geometric_of_lt_one hq0 hq1).mul_left q).of_nonneg_of_le
    (fun n => (Real.exp_pos _).le) hle

theorem tsum_exp_sq_half_le {A : ℝ} (hA : 0 < A) :
    ∑' n : ℕ, Real.exp (-A * ((n : ℝ) + 1 / 2) ^ 2) ≤
      Real.exp (-A / 4) / (1 - Real.exp (-A)) := by
  set q := Real.exp (-A) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq, Real.exp_lt_one_iff]; linarith
  have hle : ∀ n : ℕ, Real.exp (-A * ((n : ℝ) + 1 / 2) ^ 2) ≤ Real.exp (-A / 4) * q ^ n := by
    intro n
    rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : (n : ℝ) + 1 / 4 ≤ ((n : ℝ) + 1 / 2) ^ 2 := by nlinarith
    nlinarith
  have hs : Summable fun n : ℕ => Real.exp (-A / 4) * q ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  calc ∑' n : ℕ, Real.exp (-A * ((n : ℝ) + 1 / 2) ^ 2) ≤ ∑' n : ℕ, Real.exp (-A / 4) * q ^ n :=
        Summable.tsum_le_tsum hle (hs.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hle) hs
    _ = Real.exp (-A / 4) / (1 - q) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
        ring

theorem summable_exp_sq_half {A : ℝ} (hA : 0 < A) :
    Summable fun n : ℕ => Real.exp (-A * ((n : ℝ) + 1 / 2) ^ 2) := by
  set q := Real.exp (-A) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq, Real.exp_lt_one_iff]; linarith
  have hle : ∀ n : ℕ, Real.exp (-A * ((n : ℝ) + 1 / 2) ^ 2) ≤ Real.exp (-A / 4) * q ^ n := by
    intro n
    rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : (n : ℝ) + 1 / 4 ≤ ((n : ℝ) + 1 / 2) ^ 2 := by nlinarith
    nlinarith
  exact ((summable_geometric_of_lt_one hq0 hq1).mul_left _).of_nonneg_of_le
    (fun n => (Real.exp_pos _).le) hle

theorem exp_neg_le_small {x : ℝ} (hx : 3000 ≤ x) : Real.exp (-x) ≤ 1 / 3000 := by
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num), one_mul]
  have := Real.add_one_le_exp x
  linarith

variable (p : ℕ) [Fact p.Prime]

noncomputable def gaussTheta0 (σ : ℝ) : ℝ := ∑' z : ℤ, if (p : ℤ) ∣ z then gaussW σ z else 0

noncomputable def gaussMu0 (σ : ℝ) : ℝ := ∑' z : ℤ, if (p : ℤ) ∣ z then 0 else gaussW σ z

noncomputable def gaussClass (σ : ℝ) (a : ZMod p) : ℝ :=
  ∑' z : ℤ, if ((z : ZMod p) = a) then gaussW σ z else 0

variable {p}

theorem summable_ite_gaussW {σ : ℝ} (hσ : 0 < σ) (P : ℤ → Prop) [DecidablePred P] :
    Summable fun z : ℤ => if P z then gaussW σ z else 0 :=
  (summable_gaussW hσ).of_nonneg_of_le (fun z => by split_ifs <;> simp [gaussW_nonneg])
    (fun z => by split_ifs <;> simp [gaussW_nonneg])

theorem summable_ite_gaussW' {σ : ℝ} (hσ : 0 < σ) (P : ℤ → Prop) [DecidablePred P] :
    Summable fun z : ℤ => if P z then 0 else gaussW σ z :=
  (summable_gaussW hσ).of_nonneg_of_le (fun z => by split_ifs <;> simp [gaussW_nonneg])
    (fun z => by split_ifs <;> simp [gaussW_nonneg])

theorem gaussTheta0_eq (σ : ℝ) : gaussTheta0 p σ = ∑' k : ℤ, gaussW (σ * (p : ℝ) ^ 2) k := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hinj : Function.Injective fun k : ℤ => (p : ℤ) * k := fun a b h =>
    mul_left_cancel₀ hp0 h
  rw [gaussTheta0, ← hinj.tsum_eq]
  · congr 1
    funext k
    rw [ite_eq_left (dvd_mul_right _ _), gaussW, gaussW]
    push_cast
    ring_nf
  · intro z hz
    rw [Function.mem_support] at hz
    split_ifs at hz with h
    · obtain ⟨k, rfl⟩ := h
      exact ⟨k, rfl⟩
    · exact absurd rfl hz

theorem tsum_gaussW_le_geom {A : ℝ} (hA : 0 < A) :
    ∑' k : ℤ, gaussW A k ≤ 1 + 2 * (Real.exp (-A) / (1 - Real.exp (-A))) := by
  have h2 : Summable fun n : ℕ => gaussW A (-((n : ℤ) + 1)) := by
    refine (summable_gauss_succ hA).congr fun n => ?_
    rw [← gaussW_neg]
    push_cast
    ring_nf
  rw [tsum_of_nat_of_neg_add_one (summable_gauss_nat hA) h2,
    (summable_gauss_nat hA).tsum_eq_zero_add]
  have e1 : ∀ n : ℕ, gaussW A ((n + 1 : ℕ) : ℤ) = Real.exp (-A * ((n : ℝ) + 1) ^ 2) := by
    intro n
    simp [gaussW]
  have e2 : ∀ n : ℕ, gaussW A (-((n : ℤ) + 1)) = Real.exp (-A * ((n : ℝ) + 1) ^ 2) := by
    intro n
    rw [gaussW_neg]
    simp [gaussW]
  simp only [e1, e2, Nat.cast_zero, gaussW_zero]
  have := tsum_exp_sq_succ_le hA
  linarith

theorem gaussClass_eq (σ : ℝ) (a : ZMod p) :
    gaussClass p σ a = ∑' j : ℤ, gaussW σ (a.valMinAbs + (p : ℤ) * j) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hinj : Function.Injective fun j : ℤ => a.valMinAbs + (p : ℤ) * j := fun x y h => by
    have : (p : ℤ) * x = (p : ℤ) * y := by linarith
    exact mul_left_cancel₀ hp0 this
  rw [gaussClass, ← hinj.tsum_eq]
  · congr 1
    funext j
    rw [ite_eq_left]
    simp
  · intro z hz
    rw [Function.mem_support] at hz
    split_ifs at hz with h
    · have hdvd : (p : ℤ) ∣ z - a.valMinAbs := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        simp [h]
      obtain ⟨j, hj⟩ := hdvd
      exact ⟨j, by simp only; linarith⟩
    · exact absurd rfl hz

section Lemma

variable {c : ℝ}

theorem gaussW_sigma_eq (hc0 : 0 < c) :
    (1 / (2 * c * (p : ℝ) ^ 2)) * (p : ℝ) ^ 2 = 1 / (2 * c) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  field_simp

theorem gaussTheta0_le (hc0 : 0 < c) (hc : c ≤ 1 / 100000) :
    gaussTheta0 p (1 / (2 * c * p ^ 2)) ≤ 1.001 := by
  have hA : (50000 : ℝ) ≤ 1 / (2 * c) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [gaussTheta0_eq, gaussW_sigma_eq hc0]
  have hApos : 0 < 1 / (2 * c) := by positivity
  refine (tsum_gaussW_le_geom hApos).trans ?_
  have hq := exp_neg_le_small (x := 1 / (2 * c)) (by linarith)
  have hq0 : 0 < Real.exp (-(1 / (2 * c))) := Real.exp_pos _
  have h1 : Real.exp (-(1 / (2 * c))) / (1 - Real.exp (-(1 / (2 * c)))) ≤
      Real.exp (-(1 / (2 * c))) * (3 / 2) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  nlinarith

theorem sqrt_pi_div_sigma (hc0 : 0 < c) :
    √(π / (1 / (2 * c * (p : ℝ) ^ 2))) = √(2 * π * c) * p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have : π / (1 / (2 * c * (p : ℝ) ^ 2)) = (2 * π * c) * (p : ℝ) ^ 2 := by
    field_simp
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hp.le]

theorem gaussTheta0_add_gaussMu0_le (hc0 : 0 < c) :
    gaussTheta0 p (1 / (2 * c * p ^ 2)) + gaussMu0 p (1 / (2 * c * p ^ 2)) ≤
      1 + √(2 * π * c) * p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hσ : 0 < 1 / (2 * c * (p : ℝ) ^ 2) := by positivity
  rw [gaussTheta0, gaussMu0, ← Summable.tsum_add (summable_ite_gaussW hσ _)
    (summable_ite_gaussW' hσ _)]
  have : (fun z : ℤ => (if (p : ℤ) ∣ z then gaussW (1 / (2 * c * (p : ℝ) ^ 2)) z else 0) +
      (if (p : ℤ) ∣ z then 0 else gaussW (1 / (2 * c * (p : ℝ) ^ 2)) z)) =
      gaussW (1 / (2 * c * (p : ℝ) ^ 2)) := by
    funext z
    split_ifs <;> simp
  rw [this, ← sqrt_pi_div_sigma hc0]
  exact tsum_gaussW_le hσ

omit [Fact (Nat.Prime p)] in
theorem one_le_gaussTheta0 {σ : ℝ} (hσ : 0 < σ) : 1 ≤ gaussTheta0 p σ := by
  have h := (summable_ite_gaussW hσ (fun z : ℤ => (p : ℤ) ∣ z)).le_tsum 0
    (fun z _ => by split_ifs <;> simp [gaussW_nonneg])
  simp only [dvd_zero, ite_true, gaussW_zero] at h
  exact h

theorem two_abs_valMinAbs_le (a : ZMod p) : 2 * |((a.valMinAbs : ℤ) : ℝ)| ≤ p := by
  have h1 := ZMod.natAbs_valMinAbs_le a
  have h2 : 2 * a.valMinAbs.natAbs ≤ p := by
    have := Nat.mul_div_le p 2
    omega
  have h3 : ((2 * a.valMinAbs.natAbs : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
  push_cast at h3
  rwa [Nat.cast_natAbs, Int.cast_abs] at h3

theorem gaussW_shift_eq (hc0 : 0 < c) (z0 j : ℤ) :
    gaussW (1 / (2 * c * (p : ℝ) ^ 2)) (z0 + (p : ℤ) * j) =
      Real.exp (-(1 / (2 * c)) * ((z0 : ℝ) / p + j) ^ 2) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [gaussW]
  congr 1
  push_cast
  field_simp

theorem gaussW_shift_pos (hc0 : 0 < c) (a : ZMod p) (n : ℕ) :
    gaussW (1 / (2 * c * (p : ℝ) ^ 2)) (a.valMinAbs + (p : ℤ) * ((n : ℤ) + 1)) ≤
      Real.exp (-(1 / (2 * c)) * ((n : ℝ) + 1 / 2) ^ 2) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hz0b := two_abs_valMinAbs_le a
  rw [gaussW_shift_eq hc0]
  apply Real.exp_le_exp.2
  have h1 : (n : ℝ) + 1 / 2 ≤ ((a.valMinAbs : ℤ) : ℝ) / p + (((n : ℤ) + 1 : ℤ) : ℝ) := by
    have : -(1 / 2 : ℝ) ≤ ((a.valMinAbs : ℤ) : ℝ) / p := by
      rw [le_div_iff₀ hp]
      have := neg_abs_le ((a.valMinAbs : ℤ) : ℝ)
      linarith
    push_cast
    linarith
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  have hc' : 0 < 1 / (2 * c) := by positivity
  exact mul_le_mul_of_nonpos_left h2 (by linarith)

theorem gaussW_shift_neg (hc0 : 0 < c) (a : ZMod p) (n : ℕ) :
    gaussW (1 / (2 * c * (p : ℝ) ^ 2)) (a.valMinAbs + (p : ℤ) * (-((n : ℤ) + 1))) ≤
      Real.exp (-(1 / (2 * c)) * ((n : ℝ) + 1 / 2) ^ 2) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hz0b := two_abs_valMinAbs_le a
  rw [gaussW_shift_eq hc0]
  apply Real.exp_le_exp.2
  have h1 : (n : ℝ) + 1 / 2 ≤ -(((a.valMinAbs : ℤ) : ℝ) / p + ((-((n : ℤ) + 1) : ℤ) : ℝ)) := by
    have : ((a.valMinAbs : ℤ) : ℝ) / p ≤ 1 / 2 := by
      rw [div_le_iff₀ hp]
      have := le_abs_self ((a.valMinAbs : ℤ) : ℝ)
      linarith
    push_cast
    linarith
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [neg_sq] at h2
  have hc' : 0 < 1 / (2 * c) := by positivity
  exact mul_le_mul_of_nonpos_left h2 (by linarith)

theorem class_tail_le {A : ℝ} (hA : 50000 ≤ A) :
    1 + 2 * (Real.exp (-(A / 4)) / (1 - Real.exp (-A))) ≤ 1.001 := by
  have hr := exp_neg_le_small (x := A / 4) (by linarith)
  have hq := exp_neg_le_small (x := A) (by linarith)
  have hq0 : 0 < Real.exp (-A) := Real.exp_pos _
  have hr0 : 0 < Real.exp (-(A / 4)) := Real.exp_pos _
  have h1 : Real.exp (-(A / 4)) / (1 - Real.exp (-A)) ≤ Real.exp (-(A / 4)) * (3 / 2) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

theorem gaussClass_le (hc0 : 0 < c) (hc : c ≤ 1 / 100000) (a : ZMod p) :
    gaussClass p (1 / (2 * c * p ^ 2)) a ≤ 1.001 := by
  have hA : (50000 : ℝ) ≤ 1 / (2 * c) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hA' : 0 < 1 / (2 * c) := by positivity
  have hsH := summable_exp_sq_half hA'
  have hpos : ∀ n : ℕ, gaussW (1 / (2 * c * (p : ℝ) ^ 2)) (a.valMinAbs + (p : ℤ) * ((n + 1 : ℕ) : ℤ)) ≤
      Real.exp (-(1 / (2 * c)) * ((n : ℝ) + 1 / 2) ^ 2) := fun n => by
    have := gaussW_shift_pos hc0 a n
    push_cast at this ⊢
    exact this
  have hneg := gaussW_shift_neg hc0 a
  have hs1 : Summable fun n : ℕ => gaussW (1 / (2 * c * (p : ℝ) ^ 2))
      (a.valMinAbs + (p : ℤ) * ((n + 1 : ℕ) : ℤ)) :=
    hsH.of_nonneg_of_le (fun n => gaussW_nonneg _ _) hpos
  have hs0 : Summable fun n : ℕ => gaussW (1 / (2 * c * (p : ℝ) ^ 2))
      (a.valMinAbs + (p : ℤ) * (n : ℤ)) :=
    (summable_nat_add_iff 1).1 hs1
  have hs2 : Summable fun n : ℕ => gaussW (1 / (2 * c * (p : ℝ) ^ 2))
      (a.valMinAbs + (p : ℤ) * (-((n : ℤ) + 1))) :=
    hsH.of_nonneg_of_le (fun n => gaussW_nonneg _ _) hneg
  rw [gaussClass_eq, tsum_of_nat_of_neg_add_one
    (f := fun z : ℤ => gaussW (1 / (2 * c * (p : ℝ) ^ 2)) (a.valMinAbs + (p : ℤ) * z)) hs0 hs2,
    hs0.tsum_eq_zero_add]
  have hT := tsum_exp_sq_half_le hA'
  have hb1 := Summable.tsum_le_tsum hpos hs1 hsH
  have hb2 := Summable.tsum_le_tsum hneg hs2 hsH
  have hb0 : gaussW (1 / (2 * c * (p : ℝ) ^ 2)) (a.valMinAbs + (p : ℤ) * ((0 : ℕ) : ℤ)) ≤ 1 := by
    rw [gaussW, Real.exp_le_one_iff]
    have : 0 ≤ (1 / (2 * c * (p : ℝ) ^ 2)) *
      ((a.valMinAbs + (p : ℤ) * ((0 : ℕ) : ℤ) : ℤ) : ℝ) ^ 2 := by positivity
    linarith
  have hneg4 : -(1 / (2 * c)) / 4 = -(1 / (2 * c) / 4) := by ring
  rw [hneg4] at hT
  have htail := class_tail_le hA
  simp only [Nat.cast_zero] at hb0
  linarith

theorem lem_gauss {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 100000) :
    gaussTheta0 p (1 / (2 * c * p ^ 2)) ≤ 1.001 ∧
    gaussMu0 p (1 / (2 * c * p ^ 2)) ≤ √(2 * π * c) * p ∧
    gaussTheta0 p (1 / (2 * c * p ^ 2)) + gaussMu0 p (1 / (2 * c * p ^ 2)) ≤
      1 + √(2 * π * c) * p ∧
    √(2 * π * c) < 1 ∧
    ∀ a : ZMod p, gaussClass p (1 / (2 * c * p ^ 2)) a ≤ 1.001 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hσ : 0 < 1 / (2 * c * (p : ℝ) ^ 2) := by positivity
  have h1 := gaussTheta0_add_gaussMu0_le (p := p) hc0
  have h2 := one_le_gaussTheta0 (p := p) hσ
  have hc2 : √(2 * π * c) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    have := Real.pi_le_four
    nlinarith
  exact ⟨gaussTheta0_le hc0 hc, by linarith, h1, hc2, gaussClass_le hc0 hc⟩

end Lemma

end DGS
