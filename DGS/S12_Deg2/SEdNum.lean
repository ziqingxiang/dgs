module

public import DGS.S12_Deg2.SEdUnion
public import DGS.S11_Deg1.Ptrue

@[expose] public section

open Finset Filter Topology
open scoped Real

namespace DGS

noncomputable def cSEd : ℝ := Real.exp (-300)

theorem cSEd_pos : 0 < cSEd := Real.exp_pos _

theorem cSEd_le : cSEd ≤ 1 / 100000 := by
  unfold cSEd
  have h1 : Real.exp (-300) ≤ Real.exp (-17) := Real.exp_le_exp.2 (by norm_num)
  have h2 : (100000 : ℝ) ≤ Real.exp 17 := by
    have h3 : Real.exp 17 = Real.exp 1 ^ 17 := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    rw [h3]
    calc (100000 : ℝ) ≤ 2 ^ 17 := by norm_num
      _ ≤ Real.exp 1 ^ 17 := pow_le_pow_left₀ (by norm_num) h4 17
  have h5 : Real.exp (-17) = (Real.exp 17)⁻¹ := Real.exp_neg 17
  calc Real.exp (-300) ≤ Real.exp (-17) := h1
    _ = (Real.exp 17)⁻¹ := h5
    _ ≤ (100000 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
    _ = 1 / 100000 := by norm_num

theorem sqrt_two_pi_cSEd_le : √(2 * π * cSEd) ≤ Real.exp (-149) := by
  rw [Real.sqrt_le_left (Real.exp_pos _).le, ← Real.exp_nat_mul]
  unfold cSEd
  have h1 : 2 * π ≤ Real.exp 2 := by
    have h := Real.pi_lt_d2
    have h2 : (7.3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 : (2.718 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      rw [e]
      nlinarith
    linarith
  calc 2 * π * Real.exp (-300) ≤ Real.exp 2 * Real.exp (-300) := by gcongr
    _ = Real.exp (((2 : ℕ) : ℝ) * (-149)) := by rw [← Real.exp_add]; norm_num

theorem sed_BDHyp {V p n : ℕ} (hn : 1 ≤ n) (hn3 : n ≤ 3) (hV : Real.exp 200 ≤ (V : ℝ)) (hp23 : 23 ≤ p)
    (hpV : Real.log p ≤ 2 * (V : ℝ) ^ 2) (hp4 : 2 ≤ n → (V : ℝ) ^ 4 ≤ p) :
    BDHyp p (n + 1) (V ^ 2 + 50) (V ^ 10) := by
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
  have hlp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hn1R : ((n : ℝ) + 1) ≤ 4 := by
    have : (n : ℝ) ≤ 3 := by exact_mod_cast hn3
    linarith
  have hpd : (p : ℝ) ^ (n + 1) ≤ Real.exp (8 * t ^ 2) := by
    calc (p : ℝ) ^ (n + 1) = Real.exp (((n + 1 : ℕ) : ℝ) * Real.log p) := by
          rw [Real.exp_nat_mul, Real.exp_log hpR]
      _ ≤ Real.exp (8 * t ^ 2) := by
          apply Real.exp_le_exp.2
          push_cast
          nlinarith
  have hpn : (p : ℝ) ^ n ≤ Real.exp (6 * t ^ 2) := by
    calc (p : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log p) := by
          rw [Real.exp_nat_mul, Real.exp_log hpR]
      _ ≤ Real.exp (6 * t ^ 2) := by
          apply Real.exp_le_exp.2
          have : (n : ℝ) ≤ 3 := by exact_mod_cast hn3
          nlinarith
  have hl32 : Real.log (3 * (t ^ 2 + 50) / 2) ≤ Real.log 3 + 2 * Real.log t := by
    have e : Real.log 3 + 2 * Real.log t = Real.log (3 * t ^ 2) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    rw [e]
    apply Real.log_le_log (by positivity)
    nlinarith
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hl, hs]
    have hlog200 : Real.log 200 ≤ 6 := log_le_of_le_exp_nat (by norm_num) (by norm_num)
    have hlg : Real.log (2 * (p : ℝ) ^ (n + 1) / (1 / 100)) ≤ 6 + 8 * t ^ 2 := by
      rw [show 2 * (p : ℝ) ^ (n + 1) / (1 / 100) = 200 * p ^ (n + 1) by ring,
        Real.log_mul (by norm_num) (by positivity)]
      have : Real.log ((p : ℝ) ^ (n + 1)) ≤ 8 * t ^ 2 := by
        rw [Real.log_le_iff_le_exp (by positivity)]
        exact hpd
      linarith
    have hlg0 : 0 ≤ Real.log (2 * (p : ℝ) ^ (n + 1) / (1 / 100)) := Real.log_nonneg (by
      rw [show 2 * (p : ℝ) ^ (n + 1) / (1 / 100) = 200 * p ^ (n + 1) by ring]
      have : (1 : ℝ) ≤ (p : ℝ) ^ (n + 1) := one_le_pow₀ (by linarith)
      linarith)
    have ht8 : (201 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num) ht201 2
    calc 16 * (t ^ 2 + 50) * Real.log (2 * (p : ℝ) ^ (n + 1) / (1 / 100))
        ≤ 16 * (t ^ 2 + 50) * (6 + 8 * t ^ 2) := by gcongr
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
    have e : (32 : ℝ) * (1 + 1 / 100) / (1 / 100) = 3232 := by norm_num
    rw [e]
    calc 3232 * √(π * (t ^ 2 + 50)) * (p : ℝ) ^ (n + 1) * (3 * (t ^ 2 + 50) / 2) ^ (2 * (V ^ 2 + 50))
        ≤ 3232 * (2 * t) * Real.exp (8 * t ^ 2) * (3 * (t ^ 2 + 50) / 2) ^ (2 * (V ^ 2 + 50)) := by
          gcongr
      _ ≤ (t ^ 10) ^ ((t ^ 2 + 50 + 1) / 2) := by
          rw [← Real.log_le_log_iff (by positivity) (by positivity)]
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) ht0.ne', Real.log_pow,
            Real.log_exp, Real.log_rpow (by positivity), Real.log_pow]
          have h3232 : Real.log 3232 ≤ 9 := log_le_of_le_exp_nat (by norm_num) (by norm_num)
          have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
          push_cast
          nlinarith [mul_le_mul_of_nonneg_left hl32 (by positivity : (0 : ℝ) ≤ 2 * (t ^ 2 + 50)),
            mul_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2 + 50) (by linarith : (0 : ℝ) ≤ Real.log t - 200)]
  ·
    rw [hl, hs]
    simp only [Nat.add_sub_cancel]
    calc 100 * (p : ℝ) ^ n * (3 * (t ^ 2 + 50) / 2) ^ (2 * (V ^ 2 + 50))
        ≤ 100 * Real.exp (6 * t ^ 2) * (3 * (t ^ 2 + 50) / 2) ^ (2 * (V ^ 2 + 50)) := by gcongr
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
  ·
    intro h3
    have hp4' := hp4 (by omega)
    rw [hl, hs]
    calc √(t ^ 10 / (t ^ 2 + 50)) ≤ √((t ^ 4) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_le_iff₀ (by positivity)]
          nlinarith [pow_pos ht0 8]
      _ = t ^ 4 := Real.sqrt_sq (by positivity)
      _ ≤ p := hp4'

theorem sed_hMB {V m : ℕ} (hV : 10 ≤ V) (hm : V ^ 16 ≤ m) (q : ℕ) (hq : m ≤ 20 * q) :
    m / 40 ≤ (V ^ 13 - V ^ 10) * (q / V ^ 13) := by
  set k := V ^ 13 with hk
  set s := V ^ 10 with hs
  set Q := q / k with hQ
  have hk0 : 0 < k := by positivity
  have hsk : s ≤ k := Nat.pow_le_pow_right (by omega) (by norm_num)
  apply Nat.div_le_of_le_mul
  have h1 : q < k * (Q + 1) := Nat.lt_mul_div_succ q hk0
  have hVR : (10 : ℝ) ≤ V := by exact_mod_cast hV
  have hkR : (k : ℝ) = (V : ℝ) ^ 13 := by rw [hk]; push_cast; ring
  have hsR : (s : ℝ) = (V : ℝ) ^ 10 := by rw [hs]; push_cast; ring
  have hmR : (V : ℝ) ^ 16 ≤ m := by exact_mod_cast hm
  have hqR : (m : ℝ) ≤ 20 * q := by exact_mod_cast hq
  have h1R : (q : ℝ) < k * (Q + 1) := by exact_mod_cast h1
  have hV3 : (1000 : ℝ) ≤ (V : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hVR 3
    norm_num at this
    linarith
  have hsk' : (s : ℝ) * (V : ℝ) ^ 3 = k := by rw [hsR, hkR]; ring
  have hkm : 1000 * (k : ℝ) ≤ m := by
    have : (k : ℝ) * (V : ℝ) ^ 3 = (V : ℝ) ^ 16 := by rw [hkR]; ring
    nlinarith
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hsq : (s : ℝ) * Q * 1000 ≤ k * Q := by nlinarith
  have hgoal : (m : ℝ) ≤ 40 * (((k : ℝ) - s) * Q) := by nlinarith
  have hcast : ((40 * ((k - s) * Q) : ℕ) : ℝ) = 40 * (((k : ℝ) - s) * Q) := by
    push_cast [Nat.cast_sub hsk]
    ring
  have : (m : ℝ) ≤ ((40 * ((k - s) * Q) : ℕ) : ℝ) := by rw [hcast]; exact hgoal
  exact_mod_cast this

theorem sed_T1 {m k n p : ℕ} {L μ : ℝ} (hn3 : n ≤ 3) (hp23 : 23 ≤ p) (hL : Real.log p ≤ L) (hμ0 : 0 ≤ μ)
    (hμ : μ ≤ 0.0006 * p) (hkm : k ≤ m) (hkL : 4 * L * (k + 1) ≤ 0.01 * m) (hm : 100 ≤ m) :
    (p : ℝ) ^ (n + 1) * (Real.exp ((m : ℝ) / 2) * (((p : ℝ) ^ n * (1 + μ)) ^ m *
      ((1 + 1 / 100) / (p : ℝ) ^ (n + 1)) ^ (m - k))) ≤ Real.exp (-(m : ℝ) / 2) / 2 := by
  have hpR : (23 : ℝ) ≤ p := by exact_mod_cast hp23
  have hp0 : (0 : ℝ) < p := by linarith
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  set b : ℕ := m - k with hb
  have hbR : (b : ℝ) = m - k := by rw [hb]; push_cast [hkm]; ring
  have hb0 : (b : ℝ) ≤ m := by rw [hbR]; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hlp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hn3R : (n : ℝ) ≤ 3 := by exact_mod_cast hn3
  have hn0R : (0 : ℝ) ≤ n := Nat.cast_nonneg n
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
  have l1 : Real.log ((p : ℝ) ^ (n + 1)) = ((n : ℝ) + 1) * Real.log p := by
    rw [Real.log_pow]; push_cast; ring
  have l3 : Real.log (((p : ℝ) ^ n * (1 + μ)) ^ m) = m * (n * Real.log p + Real.log (1 + μ)) := by
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have l4 : Real.log (((1 + 1 / 100) / (p : ℝ) ^ (n + 1)) ^ b) =
      b * (Real.log (1 + 1 / 100) - ((n : ℝ) + 1) * Real.log p) := by
    rw [Real.log_pow, Real.log_div (by norm_num) (by positivity), l1]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_mul (by positivity) (by positivity), l1, l3, l4]
  have key : ((n : ℝ) + 1) * Real.log p + (m / 2 + ((m : ℝ) * (n * Real.log p + Real.log (1 + μ)) +
      (b : ℝ) * (Real.log (1 + 1 / 100) - ((n : ℝ) + 1) * Real.log p))) =
      ((n : ℝ) + 1) * Real.log p * (k + 1) + m / 2 + m * (Real.log (1 + μ) - Real.log p) +
        b * Real.log (1 + 1 / 100) := by
    rw [hbR]
    ring
  rw [key]
  have hkl : ((n : ℝ) + 1) * Real.log p * ((k : ℝ) + 1) ≤ 0.01 * m := by
    have h1 : ((n : ℝ) + 1) * Real.log p ≤ 4 * L := by nlinarith
    have : ((n : ℝ) + 1) * Real.log p * ((k : ℝ) + 1) ≤ 4 * L * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    linarith
  have hlast : (m : ℝ) * (Real.log (1 + μ) - Real.log p) ≤ m * (-3) :=
    mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
  have hlast2 : (b : ℝ) * Real.log (1 + 1 / 100) ≤ m * 0.01 := by
    have h0 : 0 ≤ Real.log (1 + 1 / 100) := Real.log_nonneg (by norm_num)
    nlinarith
  nlinarith

theorem sed_T2 {m k s A n p : ℕ} {L β : ℝ} (hn3 : n ≤ 3) (hp23 : 23 ≤ p) (hL : Real.log p ≤ L) (hβ0 : 0 ≤ β)
    (hβ : β ≤ Real.exp (-148)) (hA : (A : ℝ) ≤ Real.exp (0.01 * m))
    (hkL : 4 * L * (((3 * k + s * (m / k) : ℕ) : ℝ) + 1) ≤ 0.01 * m) (hm : 100000 ≤ m) :
    (p : ℝ) ^ (n + 1) * (Real.exp ((m : ℝ) / 2) * (3 ^ m * (A * (2 ^ m *
      ((p : ℝ) ^ (n + 1)) ^ (3 * k + s * (m / k)) * 1.23 ^ m * β ^ (m / 40))))) ≤
      Real.exp (-(m : ℝ) / 2) / 2 := by
  have hpR : (23 : ℝ) ≤ p := by exact_mod_cast hp23
  have hp0 : (0 : ℝ) < p := by linarith
  have hmR : (100000 : ℝ) ≤ m := by exact_mod_cast hm
  have hlp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  set N := 3 * k + s * (m / k) with hN
  have hL0 : 0 ≤ L := hlp0.trans hL
  have hpe : (p : ℝ) ≤ Real.exp L := by rw [← Real.exp_log hp0]; exact Real.exp_le_exp.2 hL
  have hpd : (p : ℝ) ^ (n + 1) ≤ Real.exp (4 * L) := by
    calc (p : ℝ) ^ (n + 1) ≤ Real.exp L ^ (n + 1) := pow_le_pow_left₀ hp0.le hpe _
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * L) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (4 * L) := by
          apply Real.exp_le_exp.2
          have : ((n + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (by omega : n + 1 ≤ 4)
          nlinarith
  have hpN : ((p : ℝ) ^ (n + 1)) ^ N ≤ Real.exp (4 * L * N) := by
    calc ((p : ℝ) ^ (n + 1)) ^ N ≤ Real.exp (4 * L) ^ N := pow_le_pow_left₀ (by positivity) hpd N
      _ = Real.exp (4 * L * N) := by rw [← Real.exp_nat_mul]; ring_nf
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
  have hm40 : (m : ℝ) / 40 - 1 ≤ ((m / 40 : ℕ) : ℝ) := by
    have h1 := Nat.div_add_mod m 40
    have h2 := Nat.mod_lt m (by norm_num : 0 < 40)
    have : (m : ℝ) < 40 * ((m / 40 : ℕ) : ℝ) + 40 := by
      have : m < 40 * (m / 40) + 40 := by omega
      exact_mod_cast this
    linarith
  have hβp : β ^ (m / 40) ≤ Real.exp (148 - 3.7 * m) := by
    calc β ^ (m / 40) ≤ Real.exp (-148) ^ (m / 40) := pow_le_pow_left₀ hβ0 hβ _
      _ = Real.exp (-148 * ((m / 40 : ℕ) : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (148 - 3.7 * m) := Real.exp_le_exp.2 (by nlinarith)
  have hlog2 : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  have hkL' : 4 * L + 4 * L * N ≤ 0.01 * m := by linarith
  calc (p : ℝ) ^ (n + 1) * (Real.exp ((m : ℝ) / 2) * (3 ^ m * (A * (2 ^ m * ((p : ℝ) ^ (n + 1)) ^ N *
        1.23 ^ m * β ^ (m / 40)))))
      ≤ Real.exp (4 * L) * (Real.exp ((m : ℝ) / 2) * (Real.exp (1.2 * m) * (Real.exp (0.01 * m) *
          (Real.exp (0.7 * m) * Real.exp (4 * L * N) * Real.exp (0.23 * m) *
            Real.exp (148 - 3.7 * m))))) := by
        gcongr
    _ = Real.exp (4 * L + 4 * L * N + 148 - 1.06 * m) := by
        simp only [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-(m : ℝ) / 2) / 2 := by
        rw [le_div_iff₀ (by norm_num)]
        calc Real.exp (4 * L + 4 * L * N + 148 - 1.06 * m) * 2
            = Real.exp (4 * L + 4 * L * N + 148 - 1.06 * m + Real.log 2) := by
              rw [Real.exp_add, Real.exp_log (by norm_num)]
          _ ≤ Real.exp (-(m : ℝ) / 2) := Real.exp_le_exp.2 (by linarith)

end DGS
