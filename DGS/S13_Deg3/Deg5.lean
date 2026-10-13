module

public import DGS.S12_Deg2.Deg2
public import DGS.S10_Tools.LittlewoodOfford

@[expose] public section

open Finset Filter Topology Matrix Polynomial Module
open scoped Real ENNReal

namespace DGS

def SuppGoodS {m : ℕ} (T : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) → ¬ (p : ℤ) ∣ 1 - -1 →
    ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) →
    ∀ g : (ZMod p)[X], g.Monic → g.natDegree = d →
    ∀ y : Fin m → ZMod p, y ≠ 0 → aeval (modP p T) g *ᵥ y = 0 →
      (m : ℝ) / (4 * (d + 1)) < ((Finset.univ.filter fun i => y i ≠ 0).card : ℝ)

theorem suppGoodS_seidelOf {m : ℕ} (ω : Pairs m → Bool) : SuppGoodS (seidelOf ω) ↔ SuppGoodPM ω := Iff.rfl

theorem not_dvd_two_of_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ 1 - -1 := by
  intro hdvd
  have h2 : (p : ℤ) ∣ 2 := by simpa using hdvd
  have h3 : p ∣ 2 := by exact_mod_cast h2
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3
  exact hp2 this

theorem abeta_le_of_suppGood {m : ℕ} {T : Matrix (Fin m) (Fin m) ℤ} (hS : SuppGoodS T) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) {β : (ZMod p)[X]} {d : ℕ}
    (hβd : β.natDegree = d) (hd1 : 1 ≤ d) (hdm : (d : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4))
    (ht : 2 ≤ ((m / (4 * (d + 1)) + 1) + d - 1) / d) :
    abeta p T β ≤ (1 / p + 1 / √(π * ((((m / (4 * (d + 1)) + 1) + d - 1) / d / 2 : ℕ) : ℝ))) ^ d := by
  have hb0 : 0 ≤ (1 / (p : ℝ) + 1 / √(π * ((((m / (4 * (d + 1)) + 1) + d - 1) / d / 2 : ℕ) : ℝ))) ^ d := by
    positivity
  refine Real.sSup_le ?_ hb0
  rintro x ⟨U, hU, hβU, rfl⟩
  obtain ⟨β', hβ', hdim⟩ := exists_hasType _ U hU
  rw [hasType_unique _ U hU hβ' hβU, hβd] at hdim
  refine lem_LObases_c hp2 U hdim (fun y hyU hy0 => ?_) ht
  have hβy : aeval (modP p T) β *ᵥ y = 0 := hβU.2.2 y hyU
  have h1 := hS p (Fact.out) hpm (not_dvd_two_of_odd Fact.out hp2) d hd1 hdm β hβU.1 hβd y hy0 hβy
  set s := (Finset.univ.filter fun i => y i ≠ 0).card with hs
  have h2 : ((m / (4 * (d + 1)) : ℕ) : ℝ) ≤ (m : ℝ) / (4 * (d + 1)) := by
    have := Nat.cast_div_le (m := m) (n := 4 * (d + 1)) (α := ℝ)
    push_cast at this
    exact this
  have h3 : ((m / (4 * (d + 1)) : ℕ) : ℝ) < s := lt_of_le_of_lt h2 h1
  have h4 : m / (4 * (d + 1)) < s := by exact_mod_cast h3
  omega

theorem eventually_logb_sq_le {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, C * (Real.logb 2 N) ^ 2 ≤ (N : ℝ) ^ δ := by
  have htend : Tendsto (fun N : ℕ => (N : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop (36 * C / (δ / 4) ^ 2 / 16 + 1), eventually_ge_atTop 1]
    with N hN hN1
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1R
  have hlog : Real.log N ≤ (N : ℝ) ^ (δ / 4) / (δ / 4) := Real.log_le_rpow_div hN0 (by linarith)
  have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogb : Real.logb 2 N ≤ 1.5 * Real.log N := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have hlogb0 : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) hN1R
  have hq : (N : ℝ) ^ (δ / 4) * (N : ℝ) ^ (δ / 4) = (N : ℝ) ^ (δ / 2) := by
    rw [← Real.rpow_add (by linarith)]
    ring_nf
  have hh : (N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (δ / 2) = (N : ℝ) ^ δ := by
    rw [← Real.rpow_add (by linarith)]
    ring_nf
  have hq0 : 0 ≤ (N : ℝ) ^ (δ / 4) := Real.rpow_nonneg hN0 _
  have hh0 : 0 ≤ (N : ℝ) ^ (δ / 2) := Real.rpow_nonneg hN0 _
  have h1 : (Real.logb 2 N) ^ 2 ≤ 2.25 * ((N : ℝ) ^ (δ / 2) / (δ / 4) ^ 2) := by
    have h2 : (Real.logb 2 N) ^ 2 ≤ (1.5 * Real.log N) ^ 2 := pow_le_pow_left₀ hlogb0 hlogb 2
    have h3 : (Real.log N) ^ 2 ≤ ((N : ℝ) ^ (δ / 4) / (δ / 4)) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
    have h4 : ((N : ℝ) ^ (δ / 4) / (δ / 4)) ^ 2 = (N : ℝ) ^ (δ / 2) / (δ / 4) ^ 2 := by
      rw [div_pow, sq, hq]
    nlinarith
  have hδ4 : 0 < (δ / 4) ^ 2 := by positivity
  have h5 : 36 * C / (δ / 4) ^ 2 / 16 ≤ (N : ℝ) ^ (δ / 2) := by linarith
  have h6 : C * (2.25 * ((N : ℝ) ^ (δ / 2) / (δ / 4) ^ 2)) ≤ (N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (δ / 2) := by
    have e : C * (2.25 * ((N : ℝ) ^ (δ / 2) / (δ / 4) ^ 2)) =
        (36 * C / (δ / 4) ^ 2 / 16) * (N : ℝ) ^ (δ / 2) := by
      field_simp
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h5 hh0
  rw [← hh]
  calc C * Real.logb 2 N ^ 2 ≤ C * (2.25 * ((N : ℝ) ^ (δ / 2) / (δ / 4) ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 hC.le
    _ ≤ (N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (δ / 2) := h6

theorem deg5_eventually {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ Real.logb 2 N ∧ 200 * (Real.logb 2 N) ^ 2 ≤ (N : ℝ) ^ (2 * ε) ∧
      2 * (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) - 1 ∧ 100 * (Real.logb 2 N) ^ 4 ≤ (N : ℝ) ∧
      2 ≤ (N : ℝ) ^ (1 / 2 - ε) ∧ 32 ≤ N ∧
      (N : ℝ) ^ (1 / 10 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) := by
  have hA := eventually_logb_sq_le (δ := 2 * ε) (C := 200) (by linarith) (by norm_num)
  have hB := eventually_logb_sq_le (δ := 1 / 2) (C := 10) (by norm_num) (by norm_num)
  have hC : ∀ᶠ N : ℕ in atTop, 2 * (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) - 1 := by
    have htend : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - 2 * ε)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    filter_upwards [htend.eventually_ge_atTop 4, eventually_ge_atTop 2] with N hN hN2
    have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hN0 : (0 : ℝ) < N := by linarith
    have e : (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ (1 - 2 * ε) = N := by
      rw [← Real.rpow_add hN0]
      norm_num
    have h0 : 0 ≤ (N : ℝ) ^ (2 * ε) := Real.rpow_nonneg hN0.le _
    nlinarith
  have hD : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε) :=
    ((tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hE : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 / 10 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) := by
    have h := eventually_rpow_tenth_succ_le_ninth
    rw [eventually_atTop] at h ⊢
    obtain ⟨N0, hN0⟩ := h
    refine ⟨N0 + 2, fun N hN => ?_⟩
    have h1 := hN0 (N - 1) (by omega)
    have e : ((N - 1 : ℕ) : ℝ) + 1 = N := by
      have : N - 1 + 1 = N := by omega
      exact_mod_cast this
    rw [e] at h1
    refine h1.trans (Real.rpow_le_rpow_of_exponent_le ?_ (by norm_num))
    have : 1 ≤ N - 1 := by omega
    exact_mod_cast this
  filter_upwards [hA, hB, hC, hD, hE, eventually_ge_atTop 32] with N hA hB hC hD hE h32
  have h32R : (32 : ℝ) ≤ N := by exact_mod_cast h32
  have hL1 : 1 ≤ Real.logb 2 N := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num
    linarith
  refine ⟨hL1, hA, hC, ?_, hD, h32, hE⟩
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hsq : ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    norm_num
  have hL0 : 0 ≤ 10 * Real.logb 2 N ^ 2 := by positivity
  have := pow_le_pow_left₀ hL0 hB 2
  rw [hsq] at this
  nlinarith

theorem one_le_of_one_le_sq {x : ℝ} (h0 : 0 ≤ x) (h1 : 1 ≤ x ^ 2) : 1 ≤ x := by nlinarith

theorem deg5_numbers {ε : ℝ} {N m d p : ℕ} (hL1 : 1 ≤ Real.logb 2 N)
    (hA : 200 * (Real.logb 2 N) ^ 2 ≤ (N : ℝ) ^ (2 * ε)) (hC : 2 * (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) - 1)
    (hB : 100 * (Real.logb 2 N) ^ 4 ≤ (N : ℝ)) (hm : N - 1 ≤ m) (h32 : 32 ≤ N) (hd5 : 5 ≤ d)
    (hdL : (d : ℝ) < 3 * Real.logb 2 N) (hp : (N : ℝ) ^ (1 / 2 - ε) < p) :
    2 ≤ ((m / (4 * (d + 1)) + 1) + d - 1) / d ∧ (d : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) ∧
      1 / (p : ℝ) + 1 / √(π * ((((m / (4 * (d + 1)) + 1) + d - 1) / d / 2 : ℕ) : ℝ)) ≤
        2 * (N : ℝ) ^ (-(1 / 2 - ε)) := by
  set L := Real.logb 2 N with hLdef
  have hN32 : (32 : ℝ) ≤ N := by exact_mod_cast h32
  have hN0 : (0 : ℝ) < N := by linarith
  have hmR : (N : ℝ) - 1 ≤ m := by
    have : ((N - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    have e : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    linarith
  have hd5R : (5 : ℝ) ≤ d := by exact_mod_cast hd5
  have hd0 : (0 : ℝ) < d := by linarith
  set k := m / (4 * (d + 1)) + 1 with hk
  set t := (k + d - 1) / d with ht
  set h := t / 2 with hh
  have hkR : (m : ℝ) / (4 * (d + 1)) ≤ k := by
    have h1 := Nat.lt_div_mul_add (a := m) (b := 4 * (d + 1)) (by positivity)
    have h2 : (m : ℝ) < ((m / (4 * (d + 1)) * (4 * (d + 1)) + 4 * (d + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    rw [div_le_iff₀ (by positivity), hk]
    push_cast
    nlinarith
  have htR : (k : ℝ) ≤ t * d := by
    have h1 := Nat.div_add_mod (k + d - 1) d
    have h2 := Nat.mod_lt (k + d - 1) (by omega : 0 < d)
    have h3 : k ≤ d * t := by
      rw [ht]
      omega
    have : ((k : ℕ) : ℝ) ≤ ((d * t : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at this
    linarith
  have hhR : (t : ℝ) - 1 ≤ 2 * h := by
    have h1 := Nat.div_add_mod t 2
    have h2 := Nat.mod_lt t (by norm_num : 0 < 2)
    have h3 : t ≤ 2 * h + 1 := by rw [hh]; omega
    have : ((t : ℕ) : ℝ) ≤ ((2 * h + 1 : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at this
    linarith
  have hdd : 4 * (d : ℝ) * (d + 1) ≤ 48 * L ^ 2 := by nlinarith
  have hL2 : (0 : ℝ) < L ^ 2 := by positivity
  have hmd : ((N : ℝ) - 1) / (48 * L ^ 2) ≤ (m : ℝ) / (4 * d * (d + 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm0 : (0 : ℝ) ≤ N - 1 := by linarith
    nlinarith
  have htd : (m : ℝ) / (4 * d * (d + 1)) ≤ t := by
    have e : (m : ℝ) / (4 * d * (d + 1)) = (m : ℝ) / (4 * (d + 1)) / d := by
      field_simp
    rw [e, div_le_iff₀ hd0]
    linarith
  have hN1 : 400 * L ^ 2 ≤ (N : ℝ) - 1 := by linarith
  have hh1 : ((N : ℝ) - 1) / (192 * L ^ 2) ≤ h := by
    have h1 : ((N : ℝ) - 1) / (48 * L ^ 2) - 1 ≤ 2 * h := by linarith
    have h2 : ((N : ℝ) - 1) / (96 * L ^ 2) ≤ ((N : ℝ) - 1) / (48 * L ^ 2) - 1 := by
      have e : ((N : ℝ) - 1) / (48 * L ^ 2) - 1 = ((N : ℝ) - 1 - 48 * L ^ 2) / (48 * L ^ 2) := by
        field_simp
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have e2 : ((N : ℝ) - 1) / (192 * L ^ 2) = ((N : ℝ) - 1) / (96 * L ^ 2) / 2 := by
      field_simp
      ring
    rw [e2]
    linarith
  refine ⟨?_, ?_, ?_⟩
  ·
    have h1 : (2 : ℝ) ≤ t := by
      have : (2 : ℝ) ≤ ((N : ℝ) - 1) / (48 * L ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      linarith
    exact_mod_cast h1
  ·
    have h1 : (d : ℝ) ^ 4 ≤ m := by
      have h2 : (d : ℝ) ^ 4 ≤ (3 * L) ^ 4 := pow_le_pow_left₀ hd0.le hdL.le 4
      nlinarith
    have h3 : ((d : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd0.le]
      norm_num
    rw [← h3]
    exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  ·
    have hNe : (N : ℝ) ^ (1 / 2 - ε) * (N : ℝ) ^ (-(1 / 2 - ε)) = 1 := by
      rw [← Real.rpow_add hN0]
      simp
    have hpos : 0 < (N : ℝ) ^ (1 / 2 - ε) := Real.rpow_pos_of_pos hN0 _
    have hpos' : 0 < (N : ℝ) ^ (-(1 / 2 - ε)) := Real.rpow_pos_of_pos hN0 _
    have hp0 : (0 : ℝ) < p := lt_trans hpos hp
    have h1 : 1 / (p : ℝ) ≤ (N : ℝ) ^ (-(1 / 2 - ε)) := by
      rw [div_le_iff₀ hp0]
      nlinarith
    have hsq : ((N : ℝ) ^ (-(1 / 2 - ε))) ^ 2 = (N : ℝ) ^ (2 * ε - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      push_cast
      ring
    have hN12 : (N : ℝ) ^ (2 * ε - 1) * (N : ℝ) = (N : ℝ) ^ (2 * ε) := by
      rw [show (N : ℝ) ^ (2 * ε) = (N : ℝ) ^ (2 * ε - 1 + 1) by ring_nf, Real.rpow_add hN0, Real.rpow_one]
    have hπ : (3 : ℝ) ≤ π := Real.pi_gt_three.le
    have hbig : 1 ≤ π * h * (N : ℝ) ^ (2 * ε - 1) := by
      have h2 : ((N : ℝ) - 1) / (192 * L ^ 2) * (N : ℝ) ^ (2 * ε - 1) ≤ h * (N : ℝ) ^ (2 * ε - 1) :=
        mul_le_mul_of_nonneg_right hh1 (Real.rpow_nonneg hN0.le _)
      have h3 : (N : ℝ) / 2 ≤ (N : ℝ) - 1 := by linarith
      have h4 : (N : ℝ) / 2 / (192 * L ^ 2) * (N : ℝ) ^ (2 * ε - 1) =
          (N : ℝ) ^ (2 * ε) / (384 * L ^ 2) := by
        rw [← hN12]
        field_simp
        ring
      have h5 : (N : ℝ) / 2 / (192 * L ^ 2) ≤ ((N : ℝ) - 1) / (192 * L ^ 2) :=
        div_le_div_of_nonneg_right h3 (by positivity)
      have h6 : (N : ℝ) / 2 / (192 * L ^ 2) * (N : ℝ) ^ (2 * ε - 1) ≤
          ((N : ℝ) - 1) / (192 * L ^ 2) * (N : ℝ) ^ (2 * ε - 1) :=
        mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hN0.le _)
      have h7 : (1 : ℝ) / 3 ≤ (N : ℝ) ^ (2 * ε) / (384 * L ^ 2) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      have h9 : (1 : ℝ) / 3 ≤ h * (N : ℝ) ^ (2 * ε - 1) := by linarith
      calc (1 : ℝ) = 3 * (1 / 3) := by norm_num
        _ ≤ π * (h * (N : ℝ) ^ (2 * ε - 1)) := mul_le_mul hπ h9 (by norm_num) (by positivity)
        _ = π * h * (N : ℝ) ^ (2 * ε - 1) := by ring
    have hh0 : (0 : ℝ) < h := by
      have : (0 : ℝ) < ((N : ℝ) - 1) / (192 * L ^ 2) := div_pos (by linarith) (by positivity)
      linarith
    have h2 : 1 / √(π * (h : ℝ)) ≤ (N : ℝ) ^ (-(1 / 2 - ε)) := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : (1 : ℝ) ≤ ((N : ℝ) ^ (-(1 / 2 - ε)) * √(π * (h : ℝ))) ^ 2 := by
        rw [mul_pow, hsq, Real.sq_sqrt (by positivity)]
        calc (1 : ℝ) ≤ π * h * (N : ℝ) ^ (2 * ε - 1) := hbig
          _ = (N : ℝ) ^ (2 * ε - 1) * (π * h) := by ring
      exact one_le_of_one_le_sq (by positivity) h3
    linarith

end DGS
