module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open Finset

namespace DGS

theorem primeCounting_le_cheb {N : ℕ} (hN : 2 ≤ N) :
    (Nat.primeCounting N : ℝ) ≤ 2 * Real.log 4 * N / Real.log N + √(N : ℝ) := by
  have hx : (1 : ℝ) < N := by exact_mod_cast hN
  have h := Chebyshev.pi_le_log4_mul_div hx
  rw [Nat.floor_natCast, Real.log_sqrt (by positivity)] at h
  have hl : 0 < Real.log N := Real.log_pos hx
  calc (Nat.primeCounting N : ℝ) ≤ Real.log 4 * N / (Real.log N / 2) + √(N : ℝ) := h
    _ = 2 * Real.log 4 * N / Real.log N + √(N : ℝ) := by
        field_simp

theorem sum_Ioc_prime_inv_cube_le (a b : ℕ) (ha : 0 < a) :
    ∑ p ∈ Ioc a b, (if p.Prime then ((p : ℝ) ^ 3)⁻¹ else 0) ≤ (Nat.primeCounting b : ℝ) / (a : ℝ) ^ 3 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  calc ∑ p ∈ Ioc a b, (if p.Prime then ((p : ℝ) ^ 3)⁻¹ else 0)
      ≤ ∑ p ∈ Ioc a b, (if p.Prime then ((a : ℝ) ^ 3)⁻¹ else 0) := by
        refine sum_le_sum fun p hp => ?_
        split_ifs
        · have : (a : ℝ) ≤ p := by exact_mod_cast (mem_Ioc.1 hp).1.le
          gcongr
        · exact le_rfl
    _ = (((Ioc a b).filter Nat.Prime).card : ℝ) * ((a : ℝ) ^ 3)⁻¹ := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ (Nat.primeCounting b : ℝ) * ((a : ℝ) ^ 3)⁻¹ := by
        gcongr
        rw [← Nat.primesLE_card_eq_primeCounting]
        exact_mod_cast card_le_card fun p hp => by
          rw [mem_filter, mem_Ioc] at hp
          exact Nat.mem_primesLE.2 ⟨hp.1.2, hp.2⟩
    _ = (Nat.primeCounting b : ℝ) / (a : ℝ) ^ 3 := by rw [div_eq_mul_inv]

theorem sum_Ioc_dyadic (f : ℕ → ℝ) (s : ℕ) : ∀ J : ℕ,
    ∑ p ∈ Ioc s (2 ^ J * s), f p = ∑ j ∈ range J, ∑ p ∈ Ioc (2 ^ j * s) (2 ^ (j + 1) * s), f p
  | 0 => by simp
  | J + 1 => by
    rw [sum_range_succ, ← sum_Ioc_dyadic f s J]
    refine (Finset.sum_Ioc_consecutive f ?_ ?_).symm
    · exact Nat.le_mul_of_pos_left s (Nat.two_pow_pos J)
    · exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J))

theorem dyadic_block_le {s : ℕ} (hs : 2 ≤ s) (j : ℕ) :
    ∑ p ∈ Ioc (2 ^ j * s) (2 ^ (j + 1) * s), (if p.Prime then ((p : ℝ) ^ 3)⁻¹ else 0) ≤
      (4 * Real.log 4 / ((s : ℝ) ^ 2 * Real.log s) + 2 * √(s : ℝ) / (s : ℝ) ^ 3) * ((1 : ℝ) / 4) ^ j := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hL : 0 < Real.log s := Real.log_pos (by linarith)
  set t : ℝ := (2 : ℝ) ^ j with ht
  have ht1 : 1 ≤ t := one_le_pow₀ (by norm_num)
  have ht0 : 0 < t := by linarith
  have h1 := sum_Ioc_prime_inv_cube_le (2 ^ j * s) (2 ^ (j + 1) * s) (by positivity)
  have hN : 2 ≤ 2 ^ (j + 1) * s := le_trans hs (Nat.le_mul_of_pos_left s (Nat.two_pow_pos _))
  have h2 := primeCounting_le_cheb hN
  have eN : ((2 ^ (j + 1) * s : ℕ) : ℝ) = 2 * t * s := by
    push_cast
    rw [ht, pow_succ]
    ring
  have ea : ((2 ^ j * s : ℕ) : ℝ) = t * s := by
    push_cast
    rfl
  rw [eN] at h2
  rw [ea] at h1
  have hlog : Real.log s ≤ Real.log (2 * t * s) :=
    Real.log_le_log hs0 (by nlinarith)
  have hsq : √(2 * t * s) ≤ 2 * t * √(s : ℝ) := by
    rw [Real.sqrt_mul (by positivity)]
    have : √(2 * t) ≤ 2 * t := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  have hL2 : 0 < Real.log (2 * t * s) := lt_of_lt_of_le hL hlog
  have h3 : 2 * Real.log 4 * (2 * t * s) / Real.log (2 * t * s) ≤ 2 * Real.log 4 * (2 * t * s) / Real.log s := by
    apply div_le_div_of_nonneg_left (by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity) hL hlog
  have h4 : (Nat.primeCounting (2 ^ (j + 1) * s) : ℝ) ≤ 2 * Real.log 4 * (2 * t * s) / Real.log s + 2 * t * √(s : ℝ) := by
    linarith
  have e4 : ((1 : ℝ) / 4) ^ j = 1 / t ^ 2 := by
    rw [ht, ← pow_mul, mul_comm, pow_mul, one_div_pow]
    norm_num
  rw [e4]
  refine h1.trans ?_
  rw [div_le_iff₀ (by positivity)]
  calc (Nat.primeCounting (2 ^ (j + 1) * s) : ℝ)
      ≤ 2 * Real.log 4 * (2 * t * s) / Real.log s + 2 * t * √(s : ℝ) := h4
    _ = (4 * Real.log 4 / ((s : ℝ) ^ 2 * Real.log s) + 2 * √(s : ℝ) / (s : ℝ) ^ 3) * (1 / t ^ 2) * (t * s) ^ 3 := by
        field_simp
        ring

theorem sum_prime_inv_cube_le {s : ℕ} (hs : 2 ≤ s) (B : ℕ) :
    ∑ p ∈ Ioc s B, (if p.Prime then ((p : ℝ) ^ 3)⁻¹ else 0) ≤
      8 / ((s : ℝ) ^ 2 * Real.log s) + 3 * √(s : ℝ) / (s : ℝ) ^ 3 := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hL : 0 < Real.log s := Real.log_pos (by linarith)
  set c := 4 * Real.log 4 / ((s : ℝ) ^ 2 * Real.log s) + 2 * √(s : ℝ) / (s : ℝ) ^ 3 with hc
  have hc0 : 0 ≤ c := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    positivity
  have hnn : ∀ p : ℕ, 0 ≤ (if p.Prime then ((p : ℝ) ^ 3)⁻¹ else 0) := fun p => by
    split_ifs
    · positivity
    · exact le_rfl
  have hsub : Ioc s B ⊆ Ioc s (2 ^ B * s) := by
    intro p hp
    rw [mem_Ioc] at hp ⊢
    refine ⟨hp.1, hp.2.trans ?_⟩
    calc B ≤ 2 ^ B := (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ B * s := Nat.le_mul_of_pos_right _ (by omega)
  have hgeom : ∑ j ∈ range B, ((1 : ℝ) / 4) ^ j ≤ 4 / 3 := by
    rw [geom_sum_eq (by norm_num)]
    have : 0 ≤ ((1 : ℝ) / 4) ^ B := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    linarith
  have hlog4 : Real.log 4 ≤ 1.3863 := by
    have h := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  calc ∑ p ∈ Ioc s B, (if p.Prime then ((p : ℝ) ^ 3)⁻¹ else 0)
      ≤ ∑ p ∈ Ioc s (2 ^ B * s), (if p.Prime then ((p : ℝ) ^ 3)⁻¹ else 0) :=
        sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hnn p
    _ = ∑ j ∈ range B, ∑ p ∈ Ioc (2 ^ j * s) (2 ^ (j + 1) * s), (if p.Prime then ((p : ℝ) ^ 3)⁻¹ else 0) :=
        sum_Ioc_dyadic _ s B
    _ ≤ ∑ j ∈ range B, c * ((1 : ℝ) / 4) ^ j := sum_le_sum fun j _ => dyadic_block_le hs j
    _ = c * ∑ j ∈ range B, ((1 : ℝ) / 4) ^ j := by rw [mul_sum]
    _ ≤ c * (4 / 3) := mul_le_mul_of_nonneg_left hgeom hc0
    _ ≤ 8 / ((s : ℝ) ^ 2 * Real.log s) + 3 * √(s : ℝ) / (s : ℝ) ^ 3 := by
        rw [hc]
        have h1 : 4 * Real.log 4 / ((s : ℝ) ^ 2 * Real.log s) * (4 / 3) ≤ 8 / ((s : ℝ) ^ 2 * Real.log s) := by
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
          linarith
        have h2 : 2 * √(s : ℝ) / (s : ℝ) ^ 3 * (4 / 3) ≤ 3 * √(s : ℝ) / (s : ℝ) ^ 3 := by
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
          have := Real.sqrt_nonneg (s : ℝ)
          linarith
        linarith

end DGS
