module

public import DGS.S06_Fourier.FourierBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

@[expose] public section

open Filter Topology Real

namespace DGS

noncomputable def sDelta (δ : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (1 - δ)⌉₊

def Rn (δ : ℝ) (n : ℕ) : Set (ℕ × ℕ) :=
  {pd | pd.1.Prime ∧ 1 ≤ pd.2 ∧ (pd.2 : ℝ) ≤ (n : ℝ) ^ δ / Real.log n ^ 2 ∧
    ((pd.1 * pd.2 : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ) / Real.log n}

theorem mul_le_sin_quarter {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ π / 4) :
    2 * √2 / π * y ≤ Real.sin y := by
  have hπ := Real.pi_pos
  set t := 4 * y / π with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hπ]; linarith
  have key := strictConcaveOn_sin_Icc.concaveOn.2 (show (0 : ℝ) ∈ Set.Icc 0 π from ⟨le_rfl, hπ.le⟩)
    (show π / 4 ∈ Set.Icc 0 π from ⟨by positivity, by linarith⟩) (show 0 ≤ 1 - t by linarith) ht0
    (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add, Real.sin_pi_div_four] at key
  have hy : t * (π / 4) = y := by rw [ht]; field_simp
  rw [hy] at key
  calc 2 * √2 / π * y = t * (√2 / 2) := by rw [ht]; field_simp; ring
    _ ≤ Real.sin y := key

theorem cos_le_one_sub_four_div {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ π / 2) :
    Real.cos x ≤ 1 - 4 / π ^ 2 * x ^ 2 := by
  have hπ := Real.pi_pos
  have h1 : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    rw [← Real.cos_two_mul_eq_one_sub]; congr 1; ring
  have h2 := mul_le_sin_quarter (y := x / 2) (by linarith) (by linarith)
  have h3 : 0 ≤ 2 * √2 / π * (x / 2) := by positivity
  have h4 : (2 * √2 / π * (x / 2)) ^ 2 ≤ Real.sin (x / 2) ^ 2 := pow_le_pow_left₀ h3 h2 2
  have h5 : (2 * √2 / π * (x / 2)) ^ 2 = 2 / π ^ 2 * x ^ 2 := by
    rw [show (2 * √2 / π * (x / 2)) ^ 2 = √2 ^ 2 * x ^ 2 / π ^ 2 by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [h5] at h4
  have h6 : 4 / π ^ 2 * x ^ 2 = 2 * (2 / π ^ 2 * x ^ 2) := by ring
  rw [h1, h6]
  linarith

theorem tauq_le_exp {q : ℕ} (hq : 2 ≤ q) : tauq q ≤ Real.exp (-4 / (q : ℝ) ^ 2) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hπ := Real.pi_pos
  have h1 : π / q ≤ π / 2 := div_le_div_of_nonneg_left hπ.le (by norm_num) hq'
  have h2 := cos_le_one_sub_four_div (x := π / q) (by positivity) h1
  have h3 : 4 / π ^ 2 * (π / q) ^ 2 = 4 / (q : ℝ) ^ 2 := by field_simp
  unfold tauq
  rw [h3] at h2
  have h4 := Real.add_one_le_exp (-4 / (q : ℝ) ^ 2)
  rw [show -4 / (q : ℝ) ^ 2 = -(4 / (q : ℝ) ^ 2) by ring] at h4 ⊢
  linarith

theorem tauq_rpow_le {q : ℕ} (hq : 2 ≤ q) {a : ℝ} (ha : 0 ≤ a) :
    tauq q ^ a ≤ Real.exp (-4 * a / (q : ℝ) ^ 2) := by
  calc tauq q ^ a ≤ Real.exp (-4 / (q : ℝ) ^ 2) ^ a :=
        Real.rpow_le_rpow (tauq_nonneg hq) (tauq_le_exp hq) ha
    _ = Real.exp (-4 * a / (q : ℝ) ^ 2) := by rw [← Real.exp_mul]; congr 1; ring

theorem fourier_b_estimates {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) {n q m : ℕ} {s : ℝ}
    (hL : 16 ≤ Real.log n) (hq : 2 ≤ q) (hm : 1 ≤ m)
    (hmδ : (m : ℝ) ≤ (n : ℝ) ^ δ / Real.log n ^ 2)
    (hqm : (q : ℝ) * m ≤ (n : ℝ) ^ (1 / 2 - δ) / Real.log n)
    (hs : (n : ℝ) ^ (1 - δ) ≤ s) :
    (q : ℝ) ^ m * tauq q ^ (s / 2) ≤ Real.exp (-((n : ℝ) ^ δ * Real.log n ^ 2)) ∧
    (q : ℝ) ^ (n * m) * tauq q ^ (s ^ 2 / (64 * m)) ≤
      Real.exp (n * Real.log 2 * (1 - Real.log n / 16)) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hL
    linarith
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn0
  have hNpos : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log n := by linarith
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hApos : 0 < (n : ℝ) ^ δ := Real.rpow_pos_of_pos hNpos δ
  have hBpos : 0 < (n : ℝ) ^ (1 - 2 * δ) := Real.rpow_pos_of_pos hNpos _
  have hAB : (n : ℝ) ^ (1 - δ) = (n : ℝ) ^ (1 - 2 * δ) * (n : ℝ) ^ δ := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hA2B : ((n : ℝ) ^ δ) ^ 2 * (n : ℝ) ^ (1 - 2 * δ) = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos,
      show δ * ((2 : ℕ) : ℝ) + (1 - 2 * δ) = 1 by push_cast; ring, Real.rpow_one]
  have hsq : ((n : ℝ) ^ (1 / 2 - δ)) ^ 2 = (n : ℝ) ^ (1 - 2 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le,
      show (1 / 2 - δ) * ((2 : ℕ) : ℝ) = 1 - 2 * δ by push_cast; ring]
  have hd1 : (q : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ) / Real.log n :=
    le_trans (le_mul_of_one_le_right hqpos.le hm1) hqm
  have hd2' : ((q : ℝ) * m) ^ 2 * Real.log n ^ 2 ≤ (n : ℝ) ^ (1 - 2 * δ) := by
    have h := pow_le_pow_left₀ (by positivity) hqm 2
    rw [div_pow, hsq, le_div_iff₀ (by positivity)] at h
    exact h
  have hd2 : (q : ℝ) ^ 2 * Real.log n ^ 2 ≤ (n : ℝ) ^ (1 - 2 * δ) := by
    have h := pow_le_pow_left₀ hqpos.le hd1 2
    rw [div_pow, hsq, le_div_iff₀ (by positivity)] at h
    exact h
  have hd3 : Real.log q ≤ Real.log n := by
    apply Real.log_le_log hqpos
    calc (q : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ) / Real.log n := hd1
      _ ≤ (n : ℝ) ^ (1 / 2 - δ) := div_le_self (by positivity) hL1
      _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = n := Real.rpow_one _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  constructor
  ·
    have hd4 : (m : ℝ) * Real.log q ≤ (n : ℝ) ^ δ * Real.log n ^ 2 := by
      have h1 : (m : ℝ) * Real.log n ^ 2 ≤ (n : ℝ) ^ δ := by
        rwa [le_div_iff₀ (by positivity)] at hmδ
      have h2 : Real.log n ≤ Real.log n ^ 2 := by nlinarith
      have h3 : (1 : ℝ) ≤ Real.log n ^ 2 := by nlinarith
      calc (m : ℝ) * Real.log q ≤ m * Real.log n := by gcongr
        _ ≤ m * Real.log n ^ 2 := by gcongr
        _ ≤ (n : ℝ) ^ δ := h1
        _ ≤ (n : ℝ) ^ δ * Real.log n ^ 2 := le_mul_of_one_le_right hApos.le h3
    have hd5 : (n : ℝ) ^ δ * Real.log n ^ 2 * (q : ℝ) ^ 2 ≤ s := by
      calc (n : ℝ) ^ δ * Real.log n ^ 2 * (q : ℝ) ^ 2 =
            (n : ℝ) ^ δ * ((q : ℝ) ^ 2 * Real.log n ^ 2) := by ring
        _ ≤ (n : ℝ) ^ δ * (n : ℝ) ^ (1 - 2 * δ) := by gcongr
        _ = (n : ℝ) ^ (1 - δ) := by rw [hAB]; ring
        _ ≤ s := hs
    have hτ := tauq_rpow_le hq (a := s / 2) (by positivity)
    have hqexp : Real.exp (m * Real.log q) = (q : ℝ) ^ m := by
      rw [Real.exp_nat_mul, Real.exp_log hqpos]
    calc (q : ℝ) ^ m * tauq q ^ (s / 2) = Real.exp (m * Real.log q) * tauq q ^ (s / 2) := by
          rw [hqexp]
      _ ≤ Real.exp (m * Real.log q) * Real.exp (-4 * (s / 2) / (q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hτ (Real.exp_pos _).le
      _ = Real.exp (m * Real.log q + -4 * (s / 2) / (q : ℝ) ^ 2) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-((n : ℝ) ^ δ * Real.log n ^ 2)) := by
          apply Real.exp_le_exp.2
          have h1 : 2 * ((n : ℝ) ^ δ * Real.log n ^ 2) ≤ 2 * s / (q : ℝ) ^ 2 := by
            rw [le_div_iff₀ (by positivity)]; linarith
          have h2 : -4 * (s / 2) / (q : ℝ) ^ 2 = -(2 * s / (q : ℝ) ^ 2) := by ring
          rw [h2]; linarith
  ·
    have hτ := tauq_rpow_le hq (a := s ^ 2 / (64 * m)) (by positivity)
    have hqexp : Real.exp ((n * m : ℕ) * Real.log q) = (q : ℝ) ^ (n * m) := by
      rw [Real.exp_nat_mul, Real.exp_log hqpos]
    have hkey : Real.log n * ((n : ℝ) * m * Real.log q) * (m * (q : ℝ) ^ 2) ≤ s ^ 2 := by
      have hNs : (n : ℝ) * (n : ℝ) ^ (1 - 2 * δ) ≤ s ^ 2 := by
        have h1 : ((n : ℝ) ^ (1 - δ)) ^ 2 = (n : ℝ) * (n : ℝ) ^ (1 - 2 * δ) := by
          rw [hAB]
          calc ((n : ℝ) ^ (1 - 2 * δ) * (n : ℝ) ^ δ) ^ 2
              = (((n : ℝ) ^ δ) ^ 2 * (n : ℝ) ^ (1 - 2 * δ)) * (n : ℝ) ^ (1 - 2 * δ) := by ring
            _ = (n : ℝ) * (n : ℝ) ^ (1 - 2 * δ) := by rw [hA2B]
        rw [← h1]
        exact pow_le_pow_left₀ (by positivity) hs 2
      have h2 : Real.log n * Real.log q ≤ Real.log n ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_left hd3 (by linarith)
      calc Real.log n * ((n : ℝ) * m * Real.log q) * (m * (q : ℝ) ^ 2)
          = (n : ℝ) * (((q : ℝ) * m) ^ 2 * (Real.log n * Real.log q)) := by ring
        _ ≤ (n : ℝ) * (((q : ℝ) * m) ^ 2 * Real.log n ^ 2) := by gcongr
        _ ≤ (n : ℝ) * (n : ℝ) ^ (1 - 2 * δ) := by gcongr
        _ ≤ s ^ 2 := hNs
    have hK : (n : ℝ) * Real.log 2 ≤ (n : ℝ) * m * Real.log q := by
      have h1 : Real.log 2 ≤ m * Real.log q :=
        le_trans hlogq (le_mul_of_one_le_left (le_trans hlog2.le hlogq) hm1)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
    have hmq : (0 : ℝ) < m * (q : ℝ) ^ 2 := by positivity
    have h1 : -4 * (s ^ 2 / (64 * m)) / (q : ℝ) ^ 2 = -(s ^ 2 / (16 * (m * (q : ℝ) ^ 2))) := by
      field_simp; ring
    have h2 : Real.log n * ((n : ℝ) * m * Real.log q) / 16 ≤ s ^ 2 / (16 * (m * (q : ℝ) ^ 2)) := by
      rw [le_div_iff₀ (by positivity)]
      calc Real.log n * ((n : ℝ) * m * Real.log q) / 16 * (16 * (m * (q : ℝ) ^ 2))
          = Real.log n * ((n : ℝ) * m * Real.log q) * (m * (q : ℝ) ^ 2) := by ring
        _ ≤ s ^ 2 := hkey
    have h3 : ((n * m : ℕ) : ℝ) * Real.log q = (n : ℝ) * m * Real.log q := by push_cast; ring
    have hexp : ((n * m : ℕ) : ℝ) * Real.log q + -4 * (s ^ 2 / (64 * m)) / (q : ℝ) ^ 2 ≤
        n * Real.log 2 * (1 - Real.log n / 16) := by
      rw [h1, h3]
      have e1 : (n : ℝ) * Real.log 2 * (1 - Real.log n / 16) -
            ((n : ℝ) * m * Real.log q + -(s ^ 2 / (16 * (m * (q : ℝ) ^ 2)))) =
          (s ^ 2 / (16 * (m * (q : ℝ) ^ 2)) - Real.log n * ((n : ℝ) * m * Real.log q) / 16) +
            ((n : ℝ) * m * Real.log q - (n : ℝ) * Real.log 2) * (Real.log n / 16 - 1) := by ring
      have h5 : 0 ≤ ((n : ℝ) * m * Real.log q - (n : ℝ) * Real.log 2) * (Real.log n / 16 - 1) :=
        mul_nonneg (sub_nonneg.2 hK) (by linarith)
      have h6 : 0 ≤ s ^ 2 / (16 * (m * (q : ℝ) ^ 2)) - Real.log n * ((n : ℝ) * m * Real.log q) / 16 :=
        sub_nonneg.2 h2
      linarith
    calc (q : ℝ) ^ (n * m) * tauq q ^ (s ^ 2 / (64 * m))
        = Real.exp ((n * m : ℕ) * Real.log q) * tauq q ^ (s ^ 2 / (64 * m)) := by rw [hqexp]
      _ ≤ Real.exp ((n * m : ℕ) * Real.log q) * Real.exp (-4 * (s ^ 2 / (64 * m)) / (q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hτ (Real.exp_pos _).le
      _ = Real.exp ((n * m : ℕ) * Real.log q + -4 * (s ^ 2 / (64 * m)) / (q : ℝ) ^ 2) :=
          (Real.exp_add _ _).symm
      _ ≤ Real.exp (n * Real.log 2 * (1 - Real.log n / 16)) := Real.exp_le_exp.2 hexp

theorem tendsto_eps_fourier {δ : ℝ} (hδ0 : 0 < δ) :
    Tendsto (fun n : ℕ => (Real.exp (n * Real.exp (-((n : ℝ) ^ δ * Real.log n ^ 2))) - 1) +
      Real.exp (n * Real.log 2 * (1 - Real.log n / 16))) atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-((n : ℝ) ^ δ * Real.log n ^ 2)))
      atTop (𝓝 0) := by
    have hlog : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.log n :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
    have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    · exact Eventually.of_forall fun n => by positivity
    · filter_upwards [hlog, hn1] with n hL hn
      have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hNpos : (0 : ℝ) < n := by linarith
      have hA : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow hN hδ0.le
      have h1 : 2 * Real.log n ≤ (n : ℝ) ^ δ * Real.log n ^ 2 := by nlinarith
      have h2 : Real.exp (-((n : ℝ) ^ δ * Real.log n ^ 2)) ≤ Real.exp (-(2 * Real.log n)) :=
        Real.exp_le_exp.2 (by linarith)
      have h3 : Real.exp (2 * Real.log n) = (n : ℝ) ^ 2 := by
        have := Real.exp_nat_mul (Real.log n) 2
        rw [Real.exp_log hNpos] at this
        exact_mod_cast this
      have h4 : Real.exp (-(2 * Real.log n)) = ((n : ℝ) ^ 2)⁻¹ := by rw [Real.exp_neg, h3]
      calc (n : ℝ) * Real.exp (-((n : ℝ) ^ δ * Real.log n ^ 2))
          ≤ (n : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
            rw [← h4]; exact mul_le_mul_of_nonneg_left h2 hNpos.le
        _ = 1 / (n : ℝ) := by field_simp
  have hv : Tendsto (fun n : ℕ => Real.exp (n * Real.log 2 * (1 - Real.log n / 16))) atTop (𝓝 0) := by
    have hlog : ∀ᶠ n : ℕ in atTop, (32 : ℝ) ≤ Real.log n :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 32
    have hw : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * Real.log 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos one_lt_two))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hw
    · exact Eventually.of_forall fun n => (Real.exp_pos _).le
    · filter_upwards [hlog] with n hL
      apply Real.exp_le_exp.2
      have h0 : (0 : ℝ) ≤ n * Real.log 2 :=
        mul_nonneg (Nat.cast_nonneg n) (Real.log_pos one_lt_two).le
      have h := mul_le_mul_of_nonneg_left (show 1 - Real.log n / 16 ≤ -1 by linarith) h0
      linarith
  have h1 : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * Real.exp (-((n : ℝ) ^ δ * Real.log n ^ 2))) - 1)
      atTop (𝓝 0) := by
    have := ((Real.continuous_exp.tendsto 0).comp hu).sub_const 1
    rw [Real.exp_zero, sub_self] at this
    exact this
  simpa using h1.add hv

variable {p : ℕ} [hp : Fact p.Prime]

theorem lem_fourier_b {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop, ∀ (p : ℕ) [Fact p.Prime] (E m : ℕ),
      1 ≤ E → 1 ≤ m → (m : ℝ) ≤ (n : ℝ) ^ δ / Real.log n ^ 2 →
      ((p ^ E * m : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ) / Real.log n →
      ∀ Y : Matrix (Fin n) (Fin m) (ZMod (p ^ E)), IsRobustE p E (sDelta δ n) Y →
      ∀ Z : Matrix (Fin n) (Fin m) (ZMod (p ^ E)),
        prob (fun ω : Pairs n → Bool => modP (p ^ E) (symOf 1 0 ω) * Y = Z) ≤
          (1 + ε n) * (((p : ℝ) ^ (E * n * m))⁻¹ * (antisymm m (p ^ E)).card) := by
  refine ⟨fun n => (Real.exp (n * Real.exp (-((n : ℝ) ^ δ * Real.log n ^ 2))) - 1) +
      Real.exp (n * Real.log 2 * (1 - Real.log n / 16)), tendsto_eps_fourier hδ0, ?_⟩
  have hLev : ∀ᶠ n : ℕ in atTop, (16 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 16
  have hBev : ∀ᶠ n : ℕ in atTop, (16 : ℝ) ≤ (n : ℝ) ^ (1 - 2 * δ) :=
    ((tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 16
  filter_upwards [hLev, hBev] with n hLn hBn
  intro p _ E m hE hm hmδ hqm Y hY Z
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hLn
    linarith
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn0
  have hNpos : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log n := by linarith
  have hq2 : 2 ≤ p ^ E := two_le_pow hE
  have hqm' : ((p ^ E : ℕ) : ℝ) * m ≤ (n : ℝ) ^ (1 / 2 - δ) / Real.log n := by
    have h : ((p ^ E * m : ℕ) : ℝ) = ((p ^ E : ℕ) : ℝ) * m := by push_cast; ring
    rw [← h]; exact hqm
  have hs : (n : ℝ) ^ (1 - δ) ≤ (sDelta δ n : ℝ) := Nat.le_ceil _
  have hs16 : 16 * m ≤ sDelta δ n := by
    have h1 : (m : ℝ) ≤ (n : ℝ) ^ δ := by
      refine hmδ.trans (div_le_self (by positivity) ?_)
      nlinarith
    have h2 : (n : ℝ) ^ (1 - 2 * δ) * (n : ℝ) ^ δ = (n : ℝ) ^ (1 - δ) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    have h3 : ((16 * m : ℕ) : ℝ) ≤ sDelta δ n := by
      push_cast
      calc 16 * (m : ℝ) ≤ 16 * (n : ℝ) ^ δ := by linarith
        _ ≤ (n : ℝ) ^ (1 - 2 * δ) * (n : ℝ) ^ δ :=
            mul_le_mul_of_nonneg_right hBn (by positivity)
        _ = (n : ℝ) ^ (1 - δ) := h2
        _ ≤ sDelta δ n := hs
    exact_mod_cast h3
  have ha := lem_fourier_a hE hm hs16 hY Z
  obtain ⟨hK1, hK2⟩ := fourier_b_estimates hδ0 hδ1 hLn hq2 hm hmδ hqm' hs
  refine ha.trans ?_
  have hpE : (p : ℝ) ^ (E * m) = ((p ^ E : ℕ) : ℝ) ^ m := by push_cast; rw [← pow_mul]
  have hpEnm : (p : ℝ) ^ (E * n * m) = ((p ^ E : ℕ) : ℝ) ^ (n * m) := by
    push_cast; rw [← pow_mul, mul_assoc]
  rw [hpE, hpEnm]
  have hC : (1 : ℝ) ≤ (antisymm m (p ^ E)).card := by
    have : 0 < (antisymm m (p ^ E)).card :=
      Finset.card_pos.2 ⟨0, (mem_antisymm m (p ^ E)).2 (by simp)⟩
    exact_mod_cast this
  have hP : (0 : ℝ) < ((p ^ E : ℕ) : ℝ) ^ (n * m) := by positivity
  have hx0 : 0 ≤ ((p ^ E : ℕ) : ℝ) ^ m * tauq (p ^ E) ^ ((sDelta δ n : ℝ) / 2) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (tauq_nonneg hq2) _)
  have hX : (1 + ((p ^ E : ℕ) : ℝ) ^ m * tauq (p ^ E) ^ ((sDelta δ n : ℝ) / 2)) ^ n ≤
      Real.exp (n * Real.exp (-((n : ℝ) ^ δ * Real.log n ^ 2))) := by
    set x := ((p ^ E : ℕ) : ℝ) ^ m * tauq (p ^ E) ^ ((sDelta δ n : ℝ) / 2)
    calc (1 + x) ^ n ≤ Real.exp x ^ n :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n
      _ = Real.exp (n * x) := (Real.exp_nat_mul x n).symm
      _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hK1 (Nat.cast_nonneg n))
  have hY0 : 0 ≤ Real.exp (n * Real.log 2 * (1 - Real.log n / 16)) := (Real.exp_pos _).le
  set C : ℝ := ((antisymm m (p ^ E)).card : ℝ)
  set P := ((p ^ E : ℕ) : ℝ) ^ (n * m)
  set X0 := Real.exp (n * Real.exp (-((n : ℝ) ^ δ * Real.log n ^ 2)))
  set Y0 := Real.exp (n * Real.log 2 * (1 - Real.log n / 16))
  have h1 : C * (1 + ((p ^ E : ℕ) : ℝ) ^ m * tauq (p ^ E) ^ ((sDelta δ n : ℝ) / 2)) ^ n ≤ C * X0 :=
    mul_le_mul_of_nonneg_left hX (by linarith)
  have h2 : P * tauq (p ^ E) ^ ((sDelta δ n : ℝ) ^ 2 / (64 * m)) ≤ C * Y0 :=
    hK2.trans (le_mul_of_one_le_left hY0 hC)
  calc P⁻¹ * (C * (1 + ((p ^ E : ℕ) : ℝ) ^ m * tauq (p ^ E) ^ ((sDelta δ n : ℝ) / 2)) ^ n +
        P * tauq (p ^ E) ^ ((sDelta δ n : ℝ) ^ 2 / (64 * m)))
      ≤ P⁻¹ * (C * X0 + C * Y0) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (inv_nonneg.2 hP.le)
    _ = (1 + ((X0 - 1) + Y0)) * (P⁻¹ * C) := by ring

end DGS
