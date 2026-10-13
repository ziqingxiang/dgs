module

public import DGS.S11_Deg1.SEplus
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Finset Filter Topology
open scoped Real

namespace DGS

noncomputable def seT (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((1 : ℝ) / 8)⌋₊

theorem seT_le_rpow (n : ℕ) : (seT n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 8) :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem rpow_lt_seT_add_one (n : ℕ) : (n : ℝ) ^ ((1 : ℝ) / 8) < seT n + 1 :=
  Nat.lt_floor_add_one _

theorem seT_pow_le (n : ℕ) : seT n ^ 8 ≤ n := by
  have h := seT_le_rpow n
  have h8 : ((seT n : ℝ)) ^ 8 ≤ ((n : ℝ) ^ ((1 : ℝ) / 8)) ^ 8 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h 8
  rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 8)), ← Real.rpow_mul (Nat.cast_nonneg n)] at h8
  norm_num at h8
  exact_mod_cast h8

theorem tendsto_seT : Tendsto seT atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp tendsto_natCast_atTop_atTop)

theorem exp_half_le : Real.exp (1 / 2) ≤ 1.65 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  nlinarith [Real.exp_pos (1 / 2)]

theorem exp_three_halves_le : Real.exp (3 / 2) ≤ 5 := by
  have h := Real.exp_one_lt_d9
  have h2 := exp_half_le
  have e : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    norm_num
  rw [e]
  nlinarith [Real.exp_pos (1 / 2)]

theorem exp_pow_ge {x : ℝ} (hx : 2.7 ≤ x) (k : ℕ) : (2.7 : ℝ) ^ k ≤ x ^ k :=
  pow_le_pow_left₀ (by norm_num) hx k

theorem log_le_of_le_exp_nat {x : ℝ} (hx : 0 < x) {k : ℕ} (h : x ≤ (2.7 : ℝ) ^ k) :
    Real.log x ≤ k := by
  rw [Real.log_le_iff_le_exp hx]
  have he : Real.exp (k : ℝ) = Real.exp 1 ^ k := by rw [← Real.exp_nat_mul]; ring_nf
  rw [he]
  exact h.trans (exp_pow_ge (by linarith [Real.exp_one_gt_d9]) k)

theorem sqrt_two_pi_cSE_le : √(2 * π * cSE) ≤ 0.008 := by
  rw [Real.sqrt_le_left (by norm_num)]
  have := Real.pi_lt_d2
  unfold cSE
  nlinarith

theorem SE_hs1 {T p : ℕ} (hT : 4 ≤ T) (hp : 0 < p) (hpT : Real.log p ≤ T + 1) :
    16 * ((T + 1 : ℕ) : ℝ) * Real.log (2 * (p : ℝ) / (1 / 100)) ≤ ((T ^ 5 : ℕ) : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h200 : Real.log 200 ≤ 6 := log_le_of_le_exp_nat (by norm_num) (by norm_num)
  have hlog : Real.log (2 * (p : ℝ) / (1 / 100)) ≤ T + 7 := by
    rw [show 2 * (p : ℝ) / (1 / 100) = 200 * p by ring, Real.log_mul (by norm_num) hpR.ne']
    linarith
  have hlog0 : 0 ≤ Real.log (2 * (p : ℝ) / (1 / 100)) := Real.log_nonneg (by
    rw [show 2 * (p : ℝ) / (1 / 100) = 200 * p by ring]
    linarith)
  have hT' : (4 : ℝ) ≤ T := by exact_mod_cast hT
  push_cast
  have h3 : (64 : ℝ) ≤ (T : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hT' 3
    norm_num at this
    linarith
  calc 16 * ((T : ℝ) + 1) * Real.log (2 * (p : ℝ) / (1 / 100)) ≤ 16 * ((T : ℝ) + 1) * (T + 7) := by
        gcongr
    _ ≤ (T : ℝ) ^ 5 := by nlinarith [mul_le_mul_of_nonneg_right h3 (sq_nonneg (T : ℝ))]

theorem SE_hs2 {T p : ℕ} (hT : Real.exp 30 ≤ T) (hp : 0 < p) (hpT : Real.log p ≤ T + 1) :
    32 * (1 + 1 / 100) / (1 / 100) * √(π * ((T + 1 : ℕ) : ℝ)) * (p : ℝ) *
        (3 * ((T + 1 : ℕ) : ℝ) / 2) ^ (2 * (T + 1)) ≤
      ((T ^ 5 : ℕ) : ℝ) ^ ((((T + 1 : ℕ) : ℝ) + 1) / 2) := by
  set t : ℝ := (T : ℝ) with ht
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have he30 : (1 : ℝ) ≤ Real.exp 30 := Real.one_le_exp (by norm_num)
  have ht1 : 1 ≤ t := he30.trans hT
  have ht0 : 0 < t := by linarith
  have hL : 30 ≤ Real.log t := by rw [Real.le_log_iff_exp_le ht0]; exact hT
  have ht5 : 5 ≤ t := by
    have : (5 : ℝ) ≤ Real.exp 30 := by
      have := Real.add_one_le_exp (30 : ℝ)
      linarith
    linarith
  have hsq : √(π * (t + 1)) ≤ t := by
    rw [Real.sqrt_le_left ht0.le]
    have := Real.pi_lt_d2
    nlinarith
  have hp' : (p : ℝ) ≤ Real.exp (t + 1) := by
    rw [← Real.exp_log hpR]
    exact Real.exp_le_exp.2 hpT
  have hb : 3 * (t + 1) / 2 ≤ 3 * t := by linarith
  push_cast
  rw [← ht]
  calc 32 * (1 + 1 / 100) / (1 / 100) * √(π * (t + 1)) * (p : ℝ) * (3 * (t + 1) / 2) ^ (2 * (T + 1))
      ≤ 3232 * t * Real.exp (t + 1) * (3 * t) ^ (2 * (T + 1)) := by
        have e : (32 : ℝ) * (1 + 1 / 100) / (1 / 100) = 3232 := by norm_num
        rw [e]
        gcongr
    _ ≤ (t ^ 5) ^ ((t + 1 + 1) / 2) := by
        rw [← Real.log_le_log_iff (by positivity) (by positivity)]
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) ht0.ne', Real.log_exp, Real.log_pow,
          Real.log_mul (by norm_num) ht0.ne', Real.log_rpow (by positivity), Real.log_pow]
        have h3232 : Real.log 3232 ≤ 9 := log_le_of_le_exp_nat (by norm_num) (by norm_num)
        have h3 : Real.log 3 ≤ 2 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
          linarith
        have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        push_cast
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 0.5 * t + 2) (by linarith : 0 ≤ Real.log t - 30)]

theorem SE_term1 {T n p : ℕ} (hT : 5 ≤ T) (hn : T ^ 8 ≤ n) (hp23 : 23 ≤ p) (hpT : Real.log p ≤ T + 1) :
    (p : ℝ) * 2 ^ n * Real.exp ((n : ℝ) / 2) *
        ((1 + 1 / 100) ^ n * (p : ℝ) ^ (T ^ 6) * (1 / (p : ℝ) + 0.008) ^ n) ≤
      Real.exp (-(n : ℝ)) / 2 := by
  have hpR : (23 : ℝ) ≤ p := by exact_mod_cast hp23
  have hp0 : (0 : ℝ) < p := by linarith
  have hT' : (5 : ℝ) ≤ T := by exact_mod_cast hT
  have hnR : (T : ℝ) ^ 8 ≤ n := by exact_mod_cast hn
  have hp' : (p : ℝ) ≤ Real.exp (T + 1) := by
    rw [← Real.exp_log hp0]
    exact Real.exp_le_exp.2 hpT
  have hbase : 2 * Real.exp (1 / 2) * (1 + 1 / 100) * (1 / (p : ℝ) + 0.008) ≤ Real.exp (-(3 / 2)) := by
    have h1 : 1 / (p : ℝ) ≤ 1 / 23 := one_div_le_one_div_of_le (by norm_num) hpR
    have h2 := exp_half_le
    have h3 : Real.exp (-(3 / 2)) = (Real.exp (3 / 2))⁻¹ := Real.exp_neg _
    have h4 := exp_three_halves_le
    have h5 : (1 / 5 : ℝ) ≤ Real.exp (-(3 / 2)) := by
      rw [h3, one_div]
      exact inv_anti₀ (Real.exp_pos _) h4
    have h6 : 0 ≤ 1 / (p : ℝ) := by positivity
    nlinarith [Real.exp_pos (1 / 2)]
  have hexpn : Real.exp ((n : ℝ) / 2) = Real.exp (1 / 2) ^ n := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hpow : (p : ℝ) ^ (T ^ 6 + 1) ≤ Real.exp (((T : ℝ) + 1) * ((T : ℝ) ^ 6 + 1)) := by
    calc (p : ℝ) ^ (T ^ 6 + 1) ≤ Real.exp (T + 1) ^ (T ^ 6 + 1) := pow_le_pow_left₀ hp0.le hp' _
      _ = Real.exp (((T : ℝ) + 1) * ((T : ℝ) ^ 6 + 1)) := by
          rw [← Real.exp_nat_mul]
          push_cast
          ring_nf
  calc (p : ℝ) * 2 ^ n * Real.exp ((n : ℝ) / 2) *
        ((1 + 1 / 100) ^ n * (p : ℝ) ^ (T ^ 6) * (1 / (p : ℝ) + 0.008) ^ n)
      = (p : ℝ) ^ (T ^ 6 + 1) *
          (2 * Real.exp (1 / 2) * (1 + 1 / 100) * (1 / (p : ℝ) + 0.008)) ^ n := by
        rw [hexpn, pow_succ]
        simp only [mul_pow]
        ring
    _ ≤ Real.exp (((T : ℝ) + 1) * ((T : ℝ) ^ 6 + 1)) * Real.exp (-(3 / 2)) ^ n := by
        gcongr
    _ = Real.exp (((T : ℝ) + 1) * ((T : ℝ) ^ 6 + 1) - 3 / 2 * n) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(n : ℝ) - Real.log 2) := by
        apply Real.exp_le_exp.2
        have hl2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        have hT6 : (1 : ℝ) ≤ (T : ℝ) ^ 6 := one_le_pow₀ (by linarith)
        have h7a : 5 * (T : ℝ) ^ 6 ≤ (T : ℝ) ^ 7 := by
          rw [show (T : ℝ) ^ 7 = T * T ^ 6 by ring]
          exact mul_le_mul_of_nonneg_right hT' (by positivity)
        have h7b : (T : ℝ) ≤ (T : ℝ) ^ 6 := by
          rw [show (T : ℝ) ^ 6 = T * T ^ 5 by ring]
          have : (1 : ℝ) ≤ (T : ℝ) ^ 5 := one_le_pow₀ (by linarith)
          nlinarith
        have h7 : ((T : ℝ) + 1) * ((T : ℝ) ^ 6 + 1) ≤ 2 * (T : ℝ) ^ 7 := by nlinarith
        have h8a : 5 * (T : ℝ) ^ 7 ≤ (T : ℝ) ^ 8 := by
          rw [show (T : ℝ) ^ 8 = T * T ^ 7 by ring]
          exact mul_le_mul_of_nonneg_right hT' (by positivity)
        have h8b : (1 : ℝ) ≤ (T : ℝ) ^ 7 := one_le_pow₀ (by linarith)
        have h8 : 2 * (T : ℝ) ^ 7 + 1 ≤ (T : ℝ) ^ 8 / 2 := by linarith
        linarith
    _ = Real.exp (-(n : ℝ)) / 2 := by
        rw [Real.exp_sub, Real.exp_log (by norm_num)]

theorem cast_sub_sub_ge (a b c : ℕ) : (a : ℝ) - b - c ≤ ((a - b - c : ℕ) : ℝ) := by
  rcases le_total (b + c) a with h | h
  · rw [Nat.sub_sub, Nat.cast_sub h]
    push_cast
    ring_nf
    exact le_rfl
  · have : (a : ℝ) ≤ b + c := by exact_mod_cast h
    have : (0 : ℝ) ≤ ((a - b - c : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith

set_option maxHeartbeats 400000 in
theorem SE_term2 {T n p A : ℕ} (hT : Real.exp 170 ≤ T) (hn : T ^ 8 ≤ n) (hp : 0 < p)
    (hpT : Real.log p ≤ T + 1) (hA : (A : ℝ) ≤ 2 * (T + 1)) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ ≤ 16222 / (T : ℝ) ^ 2) :
    (p : ℝ) * 2 ^ n * Real.exp ((n : ℝ) / 2) *
        (A * (2 ^ n * (γ ^ (n / 20 - T ^ 6 - n / T) * (p : ℝ) ^ (T ^ 6 + n / T)))) ≤
      Real.exp (-(n : ℝ)) / 2 := by
  set t : ℝ := (T : ℝ) with ht
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have he : (1 : ℝ) ≤ Real.exp 170 := Real.one_le_exp (by norm_num)
  have ht1 : 1 ≤ t := he.trans hT
  have ht0 : 0 < t := by linarith
  have hL : 170 ≤ Real.log t := by rw [Real.le_log_iff_exp_le ht0]; exact hT
  have hLt : Real.log t ≤ t := by
    have := Real.log_le_sub_one_of_pos ht0
    linarith
  have ht100 : 100 ≤ t := by
    have : (100 : ℝ) ≤ Real.exp 170 := by
      have := Real.add_one_le_exp (170 : ℝ)
      linarith
    linarith
  have hnR : t ^ 8 ≤ n := by rw [ht]; exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le (by positivity) hnR
  have hp' : (p : ℝ) ≤ Real.exp (t + 1) := by
    rw [← Real.exp_log hpR]
    exact Real.exp_le_exp.2 hpT
  set K : ℝ := 2 * Real.log t - 10 with hK
  have hK0 : 330 ≤ K := by rw [hK]; linarith
  have hγK : γ ≤ Real.exp (-K) := by
    refine hγ.trans ?_
    have h16 : (16222 : ℝ) ≤ Real.exp 10 := by
      have h := exp_pow_ge (x := Real.exp 1) (by linarith [Real.exp_one_gt_d9]) 10
      have e : Real.exp 1 ^ 10 = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e] at h
      nlinarith
    rw [hK, show -(2 * Real.log t - 10) = 10 - 2 * Real.log t by ring, Real.exp_sub,
      show 2 * Real.log t = Real.log (t ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
    exact div_le_div_of_nonneg_right h16 (by positivity)
  set N2 : ℕ := n / 20 - T ^ 6 - n / T with hN2
  have hN2R : (n : ℝ) / 20 - 1 - n / t ^ 2 - n / t ≤ N2 := by
    have h1 := cast_sub_sub_ge (n / 20) (T ^ 6) (n / T)
    have h2 : (n : ℝ) / 20 - 1 ≤ ((n / 20 : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := n) (b := 20) (by norm_num)
      have h3 : (n : ℝ) < ((n / 20 : ℕ) : ℝ) * 20 + 20 := by exact_mod_cast this
      linarith
    have h3 : ((T ^ 6 : ℕ) : ℝ) ≤ n / t ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      push_cast
      rw [← ht]
      nlinarith
    have h4 : ((n / T : ℕ) : ℝ) ≤ n / t := Nat.cast_div_le
    linarith
  have hγN : γ ^ N2 ≤ Real.exp (-K * ((n : ℝ) / 20 - 1 - n / t ^ 2 - n / t)) := by
    calc γ ^ N2 ≤ Real.exp (-K) ^ N2 := pow_le_pow_left₀ hγ0 hγK _
      _ = Real.exp (-K * N2) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          nlinarith
  have hpe : (p : ℝ) ^ (T ^ 6 + n / T) ≤ Real.exp ((t + 1) * (n / t ^ 2 + n / t)) := by
    calc (p : ℝ) ^ (T ^ 6 + n / T) ≤ Real.exp (t + 1) ^ (T ^ 6 + n / T) :=
          pow_le_pow_left₀ hpR.le hp' _
      _ = Real.exp ((T ^ 6 + n / T : ℕ) * (t + 1)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((t + 1) * (n / t ^ 2 + n / t)) := by
          apply Real.exp_le_exp.2
          have h3 : ((T ^ 6 : ℕ) : ℝ) ≤ n / t ^ 2 := by
            rw [le_div_iff₀ (by positivity)]
            push_cast
            rw [← ht]
            nlinarith
          have h4 : ((n / T : ℕ) : ℝ) ≤ n / t := Nat.cast_div_le
          push_cast at h3 ⊢
          nlinarith
  have hA' : (A : ℝ) ≤ Real.exp (t + 1) := by
    refine hA.trans ?_
    have := Real.add_one_le_exp (t + 1)
    have h2 : 2 * (t + 1) ≤ (t + 1) ^ 2 / 2 + 1 := by nlinarith
    have h3 := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ t + 1)
    nlinarith
  have h4n : (2 : ℝ) ^ n * 2 ^ n * Real.exp ((n : ℝ) / 2) ≤ Real.exp (2 * n) := by
    have e : (2 : ℝ) ^ n * 2 ^ n = 4 ^ n := by rw [← mul_pow]; norm_num
    rw [e, show (4 : ℝ) ^ n = Real.exp (Real.log 4) ^ n by rw [Real.exp_log (by norm_num)],
      ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h4 : Real.log 4 ≤ 1.5 := by
      have h := log_le_of_le_exp_nat (x := 4) (k := 2) (by norm_num) (by norm_num)
      have e2 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      linarith
    nlinarith
  calc (p : ℝ) * 2 ^ n * Real.exp ((n : ℝ) / 2) *
        (A * (2 ^ n * (γ ^ N2 * (p : ℝ) ^ (T ^ 6 + n / T))))
      = (p : ℝ) * A * ((2 : ℝ) ^ n * 2 ^ n * Real.exp ((n : ℝ) / 2)) *
          (γ ^ N2 * (p : ℝ) ^ (T ^ 6 + n / T)) := by ring
    _ ≤ Real.exp (t + 1) * Real.exp (t + 1) * Real.exp (2 * n) *
          (Real.exp (-K * ((n : ℝ) / 20 - 1 - n / t ^ 2 - n / t)) *
            Real.exp ((t + 1) * (n / t ^ 2 + n / t))) := by
        gcongr
    _ = Real.exp ((t + 1) + (t + 1) + 2 * n + (-K * ((n : ℝ) / 20 - 1 - n / t ^ 2 - n / t)) +
          (t + 1) * (n / t ^ 2 + n / t)) := by
        simp only [← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(n : ℝ) - Real.log 2) := by
        apply Real.exp_le_exp.2
        have hl2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        have hq1 : (n : ℝ) / t ^ 2 ≤ n / 10000 := by
          apply div_le_div_of_nonneg_left hn0.le (by norm_num)
          nlinarith
        have hq2 : (n : ℝ) / t ≤ n / 100 := div_le_div_of_nonneg_left hn0.le (by norm_num) ht100
        have hq3 : (t + 1) * ((n : ℝ) / t ^ 2 + n / t) ≤ 1.1 * n := by
          have e1 : (t + 1) * ((n : ℝ) / t ^ 2 + n / t) = n * (1 + 2 / t + 1 / t ^ 2) := by
            field_simp
            ring
          rw [e1]
          have : 2 / t ≤ 0.02 := by rw [div_le_iff₀ ht0]; linarith
          have : 1 / t ^ 2 ≤ 0.0001 := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith
          nlinarith
        have hlin : (n : ℝ) / 20 - 1 - n / t ^ 2 - n / t ≥ (n : ℝ) / 30 - 1 := by linarith
        have hKn : K * ((n : ℝ) / 30 - 1) ≤ K * ((n : ℝ) / 20 - 1 - n / t ^ 2 - n / t) :=
          mul_le_mul_of_nonneg_left hlin (by linarith)
        have h3 : K * ((n : ℝ) / 30 - 1) = K * ((n : ℝ) / 30) - K := by ring
        have h5 : K * ((n : ℝ) / 30) - K ≤ K * ((n : ℝ) / 20 - 1 - n / t ^ 2 - n / t) := by
          rw [← h3]
          exact hKn
        have h2 : (330 : ℝ) * ((n : ℝ) / 30) ≤ K * ((n : ℝ) / 30) :=
          mul_le_mul_of_nonneg_right hK0 (by positivity)
        have h4 : -K * ((n : ℝ) / 20 - 1 - n / t ^ 2 - n / t) =
            -(K * ((n : ℝ) / 20 - 1 - n / t ^ 2 - n / t)) := by ring
        have hKt : K ≤ 2 * t := by rw [hK]; linarith
        have htn : t ≤ n := by
          have h7 : 1 ≤ t ^ 7 := one_le_pow₀ ht1
          have : t ≤ t ^ 8 := by
            rw [show t ^ 8 = t * t ^ 7 by ring]
            nlinarith
          linarith
        rw [h4]
        linarith
    _ = Real.exp (-(n : ℝ)) / 2 := by
        rw [Real.exp_sub, Real.exp_log (by norm_num)]

theorem SE_gamma_le {T : ℕ} (hT : 1 ≤ T) :
    6464 * √(π * ((T + 1 : ℕ) : ℝ)) * 1.001 / √(((T ^ 5 : ℕ) : ℝ)) ≤ 16222 / (T : ℝ) ^ 2 := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : (0 : ℝ) < T := by linarith
  push_cast
  have hs : √((T : ℝ) ^ 5) = (T : ℝ) ^ 2 * √(T : ℝ) := by
    rw [show (T : ℝ) ^ 5 = ((T : ℝ) ^ 2) ^ 2 * T by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  have hsT : 0 < √(T : ℝ) := Real.sqrt_pos.2 ht0
  rw [hs, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : √(π * ((T : ℝ) + 1)) ≤ 2.5067 * √(T : ℝ) := by
    rw [show (2.5067 : ℝ) * √(T : ℝ) = √(2.5067 ^ 2 * T) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    have := Real.pi_lt_d4
    nlinarith
  have h2 : 6464 * (2.5067 * √(T : ℝ)) * 1.001 * (T : ℝ) ^ 2 ≤ 16222 * ((T : ℝ) ^ 2 * √(T : ℝ)) := by
    have : (0 : ℝ) ≤ (T : ℝ) ^ 2 * √(T : ℝ) := by positivity
    nlinarith
  calc 6464 * √(π * ((T : ℝ) + 1)) * 1.001 * (T : ℝ) ^ 2
      ≤ 6464 * (2.5067 * √(T : ℝ)) * 1.001 * (T : ℝ) ^ 2 := by gcongr
    _ ≤ 16222 * ((T : ℝ) ^ 2 * √(T : ℝ)) := h2

end DGS
