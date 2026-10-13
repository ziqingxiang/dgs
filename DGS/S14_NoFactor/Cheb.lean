module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

open Finset

namespace DGS

theorem chebyshev_theta_le (N : ℕ) : ∑ p ∈ Nat.primesLE N, Real.log p ≤ Real.log 4 * N := by
  rw [← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)

theorem div_le_padicValNat_factorial {p N : ℕ} [Fact p.Prime] : N / p ≤ padicValNat p N.factorial := by
  rw [padicValNat_factorial (b := Nat.log p N + 2) (by omega)]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 2) := by simp
  calc N / p = N / p ^ 1 := by rw [pow_one]
    _ ≤ ∑ i ∈ Ico 1 (Nat.log p N + 2), N / p ^ i :=
        single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1

theorem sum_div_log_le_log_factorial (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, ((N / p : ℕ) : ℝ) * Real.log p ≤ Real.log (N.factorial : ℕ) := by
  have hN : N.factorial ≠ 0 := Nat.factorial_ne_zero N
  have h := Nat.prod_pow_prime_padicValNat (N.factorial) hN (N.factorial + 1) (Nat.lt_succ_self _)
  have hlog : Real.log (N.factorial : ℕ) = ∑ p ∈ (range (N.factorial + 1)).filter Nat.Prime,
      (padicValNat p N.factorial : ℝ) * Real.log p := by
    conv_lhs => rw [← h]
    push_cast
    rw [Real.log_prod]
    · refine sum_congr rfl fun p _ => ?_
      rw [Real.log_pow]
    · intro p hp
      have : p.Prime := (mem_filter.1 hp).2
      have : (0 : ℝ) < p := by exact_mod_cast this.pos
      positivity
  rw [hlog]
  have hsub : Nat.primesLE N ⊆ (range (N.factorial + 1)).filter Nat.Prime := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    rw [mem_filter, mem_range]
    exact ⟨by have := Nat.self_le_factorial N; omega, hp.2⟩
  calc ∑ p ∈ Nat.primesLE N, ((N / p : ℕ) : ℝ) * Real.log p
      ≤ ∑ p ∈ Nat.primesLE N, (padicValNat p N.factorial : ℝ) * Real.log p := by
        refine sum_le_sum fun p hp => ?_
        have hpr : p.Prime := (Nat.mem_primesLE.1 hp).2
        have : Fact p.Prime := ⟨hpr⟩
        have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
        have : ((N / p : ℕ) : ℝ) ≤ (padicValNat p N.factorial : ℝ) := by
          exact_mod_cast div_le_padicValNat_factorial
        exact mul_le_mul_of_nonneg_right this hl
    _ ≤ ∑ p ∈ (range (N.factorial + 1)).filter Nat.Prime, (padicValNat p N.factorial : ℝ) * Real.log p :=
        sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => by
          have hpr : p.Prime := (mem_filter.1 hp).2
          have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
          positivity

theorem sum_log_div_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := sum_div_log_le_log_factorial N
  have h2 := chebyshev_theta_le N
  have h3 : Real.log (N.factorial : ℕ) ≤ N * Real.log N := by
    have : ((N.factorial : ℕ) : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
    calc Real.log (N.factorial : ℕ) ≤ Real.log ((N : ℝ) ^ N) :=
          Real.log_le_log (by exact_mod_cast Nat.factorial_pos N) this
      _ = N * Real.log N := by rw [Real.log_pow]
  have hterm : ∀ p ∈ Nat.primesLE N, (N : ℝ) * (Real.log p / p) ≤
      ((N / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    have hpr : p.Prime := (Nat.mem_primesLE.1 hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
    have hdiv : (N : ℝ) / p ≤ ((N / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0]
      have : N < (N / p + 1) * p := by
        have := Nat.lt_div_mul_add (a := N) hpr.pos
        nlinarith
      have : (N : ℝ) < ((N / p + 1 : ℕ) : ℝ) * p := by exact_mod_cast this
      push_cast at this
      linarith
    calc (N : ℝ) * (Real.log p / p) = (N : ℝ) / p * Real.log p := by ring
      _ ≤ (((N / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right hdiv hl
      _ = ((N / p : ℕ) : ℝ) * Real.log p + Real.log p := by ring
  have hsum : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * Real.log N + Real.log 4 * N := by
    rw [mul_sum]
    calc ∑ p ∈ Nat.primesLE N, (N : ℝ) * (Real.log p / p)
        ≤ ∑ p ∈ Nat.primesLE N, (((N / p : ℕ) : ℝ) * Real.log p + Real.log p) := sum_le_sum hterm
      _ = ∑ p ∈ Nat.primesLE N, ((N / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ Nat.primesLE N, Real.log p :=
          sum_add_distrib
      _ ≤ N * Real.log N + Real.log 4 * N := by linarith
  have h4 : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left h4 hNR

end DGS
