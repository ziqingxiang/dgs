module

public import DGS.S11_Deg1.PtPsiSum
public import DGS.S11_Deg1.SEnumeric

@[expose] public section

open Finset Filter Topology
open scoped Real

namespace DGS

noncomputable def ptV (m : ℕ) : ℕ := ⌊(m : ℝ) ^ ((1 : ℝ) / 16)⌋₊

theorem ptV_le_rpow (m : ℕ) : (ptV m : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 16) :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg m) _)

theorem rpow_lt_ptV_add_one (m : ℕ) : (m : ℝ) ^ ((1 : ℝ) / 16) < ptV m + 1 :=
  Nat.lt_floor_add_one _

theorem ptV_pow_le (m : ℕ) : ptV m ^ 16 ≤ m := by
  have h := ptV_le_rpow m
  have h16 : ((ptV m : ℝ)) ^ 16 ≤ ((m : ℝ) ^ ((1 : ℝ) / 16)) ^ 16 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h 16
  rw [← Real.rpow_natCast ((m : ℝ) ^ ((1 : ℝ) / 16)), ← Real.rpow_mul (Nat.cast_nonneg m)] at h16
  norm_num at h16
  exact_mod_cast h16

theorem tendsto_ptV : Tendsto ptV atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp tendsto_natCast_atTop_atTop)

theorem log_le_ptV {m p : ℕ} (hV : 3 ≤ ptV m) (hp : 0 < p)
    (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) : Real.log p ≤ 2 * (ptV m : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : Real.log p ≤ (m : ℝ) ^ ((1 : ℝ) / 8) := (Real.log_le_iff_le_exp hpR).2 hpm
  have h2 : (m : ℝ) ^ ((1 : ℝ) / 8) = ((m : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
    norm_num
  have h3 := rpow_lt_ptV_add_one m
  have h0 : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hV' : (3 : ℝ) ≤ ptV m := by exact_mod_cast hV
  rw [h2] at h1
  nlinarith

theorem exp_one_le_272' : Real.exp 1 ≤ 2.72 := by have := Real.exp_one_lt_d9; linarith

theorem three_le_exp : (3 : ℝ) ≤ Real.exp 1.2 := by
  have h1 : (2.718 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h2 : (1.2 : ℝ) ≤ Real.exp 0.2 := by have := Real.add_one_le_exp (0.2 : ℝ); linarith
  have e : Real.exp 1.2 = Real.exp 1 * Real.exp 0.2 := by rw [← Real.exp_add]; norm_num
  rw [e]
  nlinarith

theorem two_le_exp : (2 : ℝ) ≤ Real.exp 0.7 := by
  have h := Real.log_two_lt_d9
  have : Real.log 2 ≤ 0.7 := by linarith
  calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp 0.7 := Real.exp_le_exp.2 this

theorem exp_three_le : Real.exp 3 ≤ 20.2 := by
  have h := exp_one_le_272'
  have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc Real.exp 1 ^ 3 ≤ 2.72 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le h 3
    _ ≤ 20.2 := by norm_num

theorem pt_BDHyp {V p : ℕ} (hV : Real.exp 200 ≤ (V : ℝ)) (hp23 : 23 ≤ p)
    (hpV : Real.log p ≤ 2 * (V : ℝ) ^ 2) : BDHyp p 2 (V ^ 2 + 50) (V ^ 10) := by
  set t : ℝ := (V : ℝ) with ht
  have h23 : (23 : ℝ) ≤ p := by exact_mod_cast hp23
  have hpR : (0 : ℝ) < p := by linarith
  have he : (201 : ℝ) ≤ Real.exp 200 := by have := Real.add_one_le_exp (200 : ℝ); linarith
  have ht201 : 201 ≤ t := he.trans hV
  have ht0 : 0 < t := by linarith
  have hlogt : 200 ≤ Real.log t := by rw [Real.le_log_iff_exp_le ht0]; exact hV
  have hV1 : 201 ≤ V := by
    have h' : (201 : ℝ) ≤ (V : ℝ) := ht201
    exact_mod_cast h'
  have hl : (((V ^ 2 + 50 : ℕ) : ℝ)) = t ^ 2 + 50 := by push_cast; ring
  have hs : (((V ^ 10 : ℕ) : ℝ)) = t ^ 10 := by push_cast; ring
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlog3' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hl32 : Real.log (3 * (t ^ 2 + 50) / 2) ≤ Real.log 3 + 2 * Real.log t := by
    have e : Real.log 3 + 2 * Real.log t = Real.log (3 * t ^ 2) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    rw [e]
    apply Real.log_le_log (by positivity)
    nlinarith
  have hl32' : 0 ≤ Real.log (3 * (t ^ 2 + 50) / 2) := Real.log_nonneg (by nlinarith)
  refine ⟨by omega, le_rfl, by norm_num, by omega, ?_, ?_, ?_, ?_, fun h => absurd h (by norm_num)⟩
  ·
    rw [hl, hs]
    have hlog200 : Real.log 200 ≤ 6 := log_le_of_le_exp_nat (by norm_num) (by norm_num)
    have hlg : Real.log (2 * (p : ℝ) ^ 2 / (1 / 100)) ≤ 6 + 4 * t ^ 2 := by
      rw [show 2 * (p : ℝ) ^ 2 / (1 / 100) = 200 * p ^ 2 by ring, Real.log_mul (by norm_num) (by positivity),
        Real.log_pow]
      push_cast
      nlinarith
    have hlg0 : 0 ≤ Real.log (2 * (p : ℝ) ^ 2 / (1 / 100)) := Real.log_nonneg (by
      have : (23 : ℝ) ≤ p := by exact_mod_cast hp23
      rw [show 2 * (p : ℝ) ^ 2 / (1 / 100) = 200 * p ^ 2 by ring]
      nlinarith)
    have ht8 : (201 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num) ht201 2
    calc 16 * (t ^ 2 + 50) * Real.log (2 * (p : ℝ) ^ 2 / (1 / 100)) ≤ 16 * (t ^ 2 + 50) * (6 + 4 * t ^ 2) := by
          gcongr
      _ ≤ t ^ 10 := by
          have h4 : t ^ 4 * t ^ 2 ≤ t ^ 4 * t ^ 6 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ t) 4]
          nlinarith [pow_pos ht0 4, pow_pos ht0 2, pow_pos ht0 6]
  ·
    rw [hl, hs]
    have hsq : √(π * (t ^ 2 + 50)) ≤ 2 * t := by
      rw [Real.sqrt_le_left (by positivity)]
      have := Real.pi_lt_d2
      nlinarith
    have hp' : (p : ℝ) ≤ Real.exp (2 * t ^ 2) := by
      rw [← Real.exp_log hpR]
      exact Real.exp_le_exp.2 hpV
    have e : (32 : ℝ) * (1 + 1 / 100) / (1 / 100) = 3232 := by norm_num
    rw [e]
    calc 3232 * √(π * (t ^ 2 + 50)) * (p : ℝ) ^ 2 * (3 * (t ^ 2 + 50) / 2) ^ (2 * (V ^ 2 + 50))
        ≤ 3232 * (2 * t) * Real.exp (2 * t ^ 2) ^ 2 * (3 * (t ^ 2 + 50) / 2) ^ (2 * (V ^ 2 + 50)) := by
          gcongr
      _ ≤ (t ^ 10) ^ ((t ^ 2 + 50 + 1) / 2) := by
          rw [← Real.log_le_log_iff (by positivity) (by positivity)]
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) ht0.ne', Real.log_pow,
            Real.log_exp, Real.log_pow, Real.log_rpow (by positivity), Real.log_pow]
          have h3232 : Real.log 3232 ≤ 9 := log_le_of_le_exp_nat (by norm_num) (by norm_num)
          have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
          push_cast
          have hV2 : ((V ^ 2 + 50 : ℕ) : ℝ) = t ^ 2 + 50 := hl
          nlinarith [mul_le_mul_of_nonneg_left hl32 (by positivity : (0 : ℝ) ≤ 2 * (t ^ 2 + 50)),
            mul_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2 + 50) (by linarith : (0 : ℝ) ≤ Real.log t - 200)]
  ·
    rw [hl, hs]
    have hp' : (p : ℝ) ≤ Real.exp (2 * t ^ 2) := by
      rw [← Real.exp_log hpR]
      exact Real.exp_le_exp.2 hpV
    norm_num only [Nat.add_sub_cancel, pow_one]
    calc 100 * (p : ℝ) * (3 * (t ^ 2 + 50) / 2) ^ (2 * (V ^ 2 + 50))
        ≤ 100 * Real.exp (2 * t ^ 2) * (3 * (t ^ 2 + 50) / 2) ^ (2 * (V ^ 2 + 50)) := by gcongr
      _ ≤ (t ^ 10) ^ ((t ^ 2 + 50) / 2) := by
          rw [← Real.log_le_log_iff (by positivity) (by positivity)]
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
            Real.log_exp, Real.log_pow, Real.log_rpow (by positivity), Real.log_pow]
          have h100 : Real.log 100 ≤ 5 := log_le_of_le_exp_nat (by norm_num) (by norm_num)
          push_cast
          nlinarith [mul_le_mul_of_nonneg_left hl32 (by positivity : (0 : ℝ) ≤ 2 * (t ^ 2 + 50)),
            mul_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2 + 50) (by linarith : (0 : ℝ) ≤ Real.log t - 200)]
  ·
    have h1 : V ^ 2 + 50 ≤ 2 * V ^ 2 := by nlinarith
    have h2 : 2800 * V ^ 2 ≤ V ^ 10 := by
      have : 2800 ≤ V ^ 8 := le_trans (by norm_num) (Nat.pow_le_pow_left hV1 8)
      calc 2800 * V ^ 2 ≤ V ^ 8 * V ^ 2 := Nat.mul_le_mul_right _ this
        _ = V ^ 10 := by ring
    omega

theorem pt_hMB {V m : ℕ} (hV : 10 ≤ V) (hm : V ^ 16 ≤ m) (n : ℕ) (hn : m ≤ 100 * n) :
    m / 200 ≤ (V ^ 13 - V ^ 10) * (n / V ^ 13) := by
  set k := V ^ 13 with hk
  set s := V ^ 10 with hs
  set q := n / k with hq
  have hk0 : 0 < k := by positivity
  have hsk : s ≤ k := Nat.pow_le_pow_right (by omega) (by norm_num)
  apply Nat.div_le_of_le_mul
  have h1 : n < k * (q + 1) := Nat.lt_mul_div_succ n hk0
  have hVR : (10 : ℝ) ≤ V := by exact_mod_cast hV
  have hkR : (k : ℝ) = (V : ℝ) ^ 13 := by rw [hk]; push_cast; ring
  have hsR : (s : ℝ) = (V : ℝ) ^ 10 := by rw [hs]; push_cast; ring
  have hmR : (V : ℝ) ^ 16 ≤ m := by exact_mod_cast hm
  have hnR : (m : ℝ) ≤ 100 * n := by exact_mod_cast hn
  have h1R : (n : ℝ) < k * (q + 1) := by exact_mod_cast h1
  have hV3 : (1000 : ℝ) ≤ (V : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hVR 3
    norm_num at this
    linarith
  have hsk' : (s : ℝ) * (V : ℝ) ^ 3 = k := by rw [hsR, hkR]; ring
  have hkm : 1000 * (k : ℝ) ≤ m := by
    have : (k : ℝ) * (V : ℝ) ^ 3 = (V : ℝ) ^ 16 := by rw [hkR]; ring
    nlinarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hsq : (s : ℝ) * q * 1000 ≤ k * q := by nlinarith
  have hgoal : (m : ℝ) ≤ 200 * (((k : ℝ) - s) * q) := by nlinarith
  have hcast : ((200 * ((k - s) * q) : ℕ) : ℝ) = 200 * (((k : ℝ) - s) * q) := by
    push_cast [Nat.cast_sub hsk]
    ring
  have : (m : ℝ) ≤ ((200 * ((k - s) * q) : ℕ) : ℝ) := by rw [hcast]; exact hgoal
  exact_mod_cast this

theorem pt_gam0_le {V : ℕ} (hV : Real.exp 200 ≤ (V : ℝ)) : gam0 (V ^ 2 + 50) (V ^ 10) ≤ Real.exp (-760) := by
  set t : ℝ := (V : ℝ) with ht
  have he : (201 : ℝ) ≤ Real.exp 200 := by have := Real.add_one_le_exp (200 : ℝ); linarith
  have ht0 : 0 < t := by linarith
  unfold gam0
  have hsq : √(π * (((V ^ 2 + 50 : ℕ) : ℝ))) ≤ 2 * t := by
    rw [Real.sqrt_le_left (by positivity)]
    push_cast
    have := Real.pi_lt_d2
    nlinarith
  have hs : √(((V ^ 10 : ℕ) : ℝ)) = t ^ 5 := by
    push_cast
    rw [show (t : ℝ) ^ 10 = (t ^ 5) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hs, div_le_iff₀ (by positivity)]
  have h4 : Real.exp 800 ≤ t ^ 4 := by
    have : Real.exp 800 = Real.exp 200 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hV 4
  have h13 : (12928 : ℝ) ≤ Real.exp 40 := by
    have h2 : Real.exp 40 = Real.exp 1 ^ 40 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    rw [h2]
    calc (12928 : ℝ) ≤ 2.7 ^ 40 := by norm_num
      _ ≤ Real.exp 1 ^ 40 := pow_le_pow_left₀ (by norm_num) h3 40
  have e1 : Real.exp (-760) * Real.exp 800 = Real.exp 40 := by rw [← Real.exp_add]; norm_num
  calc 6464 * √(π * (((V ^ 2 + 50 : ℕ) : ℝ))) ≤ 6464 * (2 * t) := by gcongr
    _ = 12928 * t := by ring
    _ ≤ Real.exp 40 * t := by gcongr
    _ = Real.exp (-760) * Real.exp 800 * t := by rw [e1]
    _ ≤ Real.exp (-760) * t ^ 4 * t := by gcongr
    _ = Real.exp (-760) * t ^ 5 := by ring

theorem pt_T1 {m k nU p : ℕ} {L μ : ℝ} (hp23 : 23 ≤ p) (hL : Real.log p ≤ L) (hμ0 : 0 ≤ μ)
    (hμ : μ ≤ 0.0006 * p) (hkm : k ≤ m) (hnU : 5 * nU ≤ 3 * m) (hkL : 2 * L * (k + 1) ≤ 0.01 * m)
    (hm : 100 ≤ m) :
    (p : ℝ) ^ 2 * (Real.exp ((m : ℝ) / 2) * (((p : ℝ) ^ 2) ^ nU * ((p : ℝ) * (1 + μ)) ^ (m - nU) *
      ((1 + 1 / 100) / (p : ℝ) ^ 2) ^ (m - k))) ≤ Real.exp (-(m : ℝ) / 2) / 2 := by
  have hpR : (23 : ℝ) ≤ p := by exact_mod_cast hp23
  have hp0 : (0 : ℝ) < p := by linarith
  have hnUm : nU ≤ m := by omega
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  set a : ℕ := m - nU with ha
  set b : ℕ := m - k with hb
  have haR : (a : ℝ) = m - nU := by rw [ha]; push_cast [hnUm]; ring
  have hbR : (b : ℝ) = m - k := by rw [hb]; push_cast [hkm]; ring
  have ha5 : (2 : ℝ) / 5 * m ≤ a := by
    have : ((5 * nU : ℕ) : ℝ) ≤ ((3 * m : ℕ) : ℝ) := by exact_mod_cast hnU
    push_cast at this
    linarith
  have hb0 : (b : ℝ) ≤ m := by rw [hbR]; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hlp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hq : Real.log (1 + μ) - Real.log p ≤ -3 := by
    rw [← Real.log_div (by linarith) hp0.ne']
    have h1 : (1 + μ) / p ≤ 0.0446 := by
      rw [div_le_iff₀ hp0]
      nlinarith
    have h2 : Real.log ((1 + μ) / p) ≤ Real.log 0.0446 := Real.log_le_log (by positivity) h1
    have h3 : Real.log 0.0446 ≤ -3 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h4 := exp_three_le
      have h5 : Real.exp (-3) = (Real.exp 3)⁻¹ := Real.exp_neg 3
      rw [h5]
      rw [le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
      linarith
    linarith
  have hl101 : Real.log (1 + 1 / 100) ≤ 0.01 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 100)
    linarith
  have hlog2 : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_div (by positivity) (by norm_num),
    Real.log_exp]
  have l1 : Real.log ((p : ℝ) ^ 2) = 2 * Real.log p := by rw [Real.log_pow]; push_cast; ring
  have l2 : Real.log (((p : ℝ) ^ 2) ^ nU) = nU * (2 * Real.log p) := by rw [Real.log_pow, l1]
  have l3 : Real.log (((p : ℝ) * (1 + μ)) ^ a) = a * (Real.log p + Real.log (1 + μ)) := by
    rw [Real.log_pow, Real.log_mul hp0.ne' (by positivity)]
  have l4 : Real.log (((1 + 1 / 100) / (p : ℝ) ^ 2) ^ b) = b * (Real.log (1 + 1 / 100) - 2 * Real.log p) := by
    rw [Real.log_pow, Real.log_div (by norm_num) (by positivity), l1]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    l1, l2, l3, l4]
  have key : (nU : ℝ) * (2 * Real.log p) + (a : ℝ) * (Real.log p + Real.log (1 + μ)) +
      (b : ℝ) * (Real.log (1 + 1 / 100) - 2 * Real.log p) =
      2 * Real.log p * k + a * (Real.log (1 + μ) - Real.log p) + b * Real.log (1 + 1 / 100) := by
    rw [haR, hbR]
    ring
  have hkl : 2 * Real.log p * (k + 1) ≤ 0.01 * m := by
    have : 2 * Real.log p * ((k : ℝ) + 1) ≤ 2 * L * ((k : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    linarith
  have hlast : (a : ℝ) * (Real.log (1 + μ) - Real.log p) ≤ a * (-3) :=
    mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
  have hlast2 : (b : ℝ) * Real.log (1 + 1 / 100) ≤ m * 0.01 := by
    have h0 : 0 ≤ Real.log (1 + 1 / 100) := Real.log_nonneg (by norm_num)
    nlinarith
  nlinarith

theorem pt_T2 {m k s A p : ℕ} {L β : ℝ} (hp23 : 23 ≤ p) (hL : Real.log p ≤ L) (hβ0 : 0 ≤ β)
    (hβ : β ≤ Real.exp (-748)) (hA : (A : ℝ) ≤ Real.exp (0.01 * m))
    (hkL : 2 * L * (((4 * k + s * (m / k) : ℕ) : ℝ) + 1) ≤ 0.01 * m) (hm : 100000 ≤ m) :
    (p : ℝ) ^ 2 * (Real.exp ((m : ℝ) / 2) * (3 ^ m * (A * (2 ^ m * ((p : ℝ) ^ 2) ^ (4 * k + s * (m / k)) *
      1.23 ^ m * β ^ (m / 200))))) ≤ Real.exp (-(m : ℝ) / 2) / 2 := by
  have hpR : (23 : ℝ) ≤ p := by exact_mod_cast hp23
  have hp0 : (0 : ℝ) < p := by linarith
  have hmR : (100000 : ℝ) ≤ m := by exact_mod_cast hm
  have hlp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  set N := 4 * k + s * (m / k) with hN
  have hL0 : 0 ≤ L := hlp0.trans hL
  have hpe : (p : ℝ) ≤ Real.exp L := by rw [← Real.exp_log hp0]; exact Real.exp_le_exp.2 hL
  have hp2 : (p : ℝ) ^ 2 ≤ Real.exp (2 * L) := by
    calc (p : ℝ) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ hp0.le hpe 2
      _ = Real.exp (2 * L) := by rw [← Real.exp_nat_mul]; norm_num
  have hpN : ((p : ℝ) ^ 2) ^ N ≤ Real.exp (2 * L * N) := by
    calc ((p : ℝ) ^ 2) ^ N ≤ Real.exp (2 * L) ^ N := pow_le_pow_left₀ (by positivity) hp2 N
      _ = Real.exp (2 * L * N) := by rw [← Real.exp_nat_mul]; ring_nf
  have h3 : (3 : ℝ) ^ m ≤ Real.exp (1.2 * m) := by
    calc (3 : ℝ) ^ m ≤ Real.exp 1.2 ^ m := pow_le_pow_left₀ (by norm_num) three_le_exp m
      _ = Real.exp (1.2 * m) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : (2 : ℝ) ^ m ≤ Real.exp (0.7 * m) := by
    calc (2 : ℝ) ^ m ≤ Real.exp 0.7 ^ m := pow_le_pow_left₀ (by norm_num) two_le_exp m
      _ = Real.exp (0.7 * m) := by rw [← Real.exp_nat_mul]; ring_nf
  have h123 : (1.23 : ℝ) ^ m ≤ Real.exp (0.23 * m) := by
    have : (1.23 : ℝ) ≤ Real.exp 0.23 := by have := Real.add_one_le_exp (0.23 : ℝ); linarith
    calc (1.23 : ℝ) ^ m ≤ Real.exp 0.23 ^ m := pow_le_pow_left₀ (by norm_num) this m
      _ = Real.exp (0.23 * m) := by rw [← Real.exp_nat_mul]; ring_nf
  have hm200 : (m : ℝ) / 200 - 1 ≤ ((m / 200 : ℕ) : ℝ) := by
    have h1 := Nat.div_add_mod m 200
    have h2 := Nat.mod_lt m (by norm_num : 0 < 200)
    have : (m : ℝ) < 200 * ((m / 200 : ℕ) : ℝ) + 200 := by
      have : m < 200 * (m / 200) + 200 := by omega
      exact_mod_cast this
    linarith
  have hβp : β ^ (m / 200) ≤ Real.exp (748 - 3.74 * m) := by
    calc β ^ (m / 200) ≤ Real.exp (-748) ^ (m / 200) := pow_le_pow_left₀ hβ0 hβ _
      _ = Real.exp (-748 * ((m / 200 : ℕ) : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (748 - 3.74 * m) := Real.exp_le_exp.2 (by nlinarith)
  have hlog2 : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  have hkL' : 2 * L + 2 * L * N ≤ 0.01 * m := by linarith
  calc (p : ℝ) ^ 2 * (Real.exp ((m : ℝ) / 2) * (3 ^ m * (A * (2 ^ m * ((p : ℝ) ^ 2) ^ N *
        1.23 ^ m * β ^ (m / 200)))))
      ≤ Real.exp (2 * L) * (Real.exp ((m : ℝ) / 2) * (Real.exp (1.2 * m) * (Real.exp (0.01 * m) *
          (Real.exp (0.7 * m) * Real.exp (2 * L * N) * Real.exp (0.23 * m) *
            Real.exp (748 - 3.74 * m))))) := by
        gcongr
    _ = Real.exp (2 * L + 2 * L * N + 748 - 1.1 * m) := by
        simp only [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-(m : ℝ) / 2) / 2 := by
        rw [le_div_iff₀ (by norm_num)]
        calc Real.exp (2 * L + 2 * L * N + 748 - 1.1 * m) * 2
            = Real.exp (2 * L + 2 * L * N + 748 - 1.1 * m + Real.log 2) := by
              rw [Real.exp_add, Real.exp_log (by norm_num)]
          _ ≤ Real.exp (-(m : ℝ) / 2) := Real.exp_le_exp.2 (by linarith)

end DGS
