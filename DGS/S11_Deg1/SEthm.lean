module

public import DGS.S11_Deg1.SEnumeric
public import DGS.S04_Reduction.Support

@[expose] public section

open Finset Filter Topology Matrix
open scoped Real

namespace DGS

theorem SE_bound1 {p n d k : ℕ} (hp : 0 < p) {μ0 : ℝ} (hμ0 : 0 ≤ μ0) (hμ : μ0 ≤ 0.008 * p)
    (hd : d ≤ n) (hk : k ≤ n) :
    μ0 ^ d * ((1 + 1 / 100) / (p : ℝ)) ^ (n - k) ≤
      (1 + 1 / 100) ^ n * (p : ℝ) ^ k * (1 / (p : ℝ) + 0.008) ^ n := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  set a : ℝ := 1 / (p : ℝ) with ha
  have ha0 : 0 < a := by positivity
  have hpa : (p : ℝ) * a = 1 := by rw [ha]; field_simp
  have e1 : a ^ (n - k) = a ^ n * (p : ℝ) ^ k := by
    have : a ^ n = a ^ (n - k) * a ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
    rw [this, mul_assoc, ← mul_pow, mul_comm a, hpa, one_pow, mul_one]
  have e2 : μ0 ^ d * a ^ n = (μ0 * a) ^ d * a ^ (n - d) := by
    rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' hd]
  have h1 : μ0 * a ≤ a + 0.008 := by
    have : μ0 * a ≤ 0.008 := by
      rw [ha, mul_one_div, div_le_iff₀ hpR]
      exact hμ
    linarith
  have h3 : (a + 0.008) ^ n = (a + 0.008) ^ d * (a + 0.008) ^ (n - d) := by
    rw [← pow_add, Nat.add_sub_cancel' hd]
  have h2 : (μ0 * a) ^ d * a ^ (n - d) ≤ (a + 0.008) ^ n := by
    rw [h3]
    exact mul_le_mul (pow_le_pow_left₀ (mul_nonneg hμ0 ha0.le) h1 d)
      (pow_le_pow_left₀ ha0.le (by linarith) _) (pow_nonneg ha0.le _) (by positivity)
  have h4 : (1 + 1 / 100 : ℝ) ^ (n - k) ≤ (1 + 1 / 100) ^ n :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le n k)
  calc μ0 ^ d * ((1 + 1 / 100) / (p : ℝ)) ^ (n - k)
      = (1 + 1 / 100) ^ (n - k) * (p : ℝ) ^ k * (μ0 ^ d * a ^ n) := by
        rw [div_eq_mul_one_div (1 + 1 / 100 : ℝ) (p : ℝ), ← ha, mul_pow, e1]
        ring
    _ ≤ (1 + 1 / 100) ^ n * (p : ℝ) ^ k * (a + 0.008) ^ n := by
        rw [e2]
        exact mul_le_mul (mul_le_mul_of_nonneg_right h4 (by positivity)) h2
          (mul_nonneg (pow_nonneg (mul_nonneg hμ0 ha0.le) _) (pow_nonneg ha0.le _)) (by positivity)

theorem SE_bound2 {μ0 ζ γ P : ℝ} (hμ0 : 0 ≤ μ0) (hμP : μ0 ≤ P) (hP1 : 1 ≤ P) (hγ : μ0 * ζ = γ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {d M N E : ℕ} (hMd : M ≤ d) (hNM : N ≤ M) (hdE : d - M ≤ E) :
    μ0 ^ d * ζ ^ M ≤ γ ^ N * P ^ E := by
  have e : μ0 ^ d * ζ ^ M = γ ^ M * μ0 ^ (d - M) := by
    rw [← hγ, mul_pow]
    conv_lhs => rw [← Nat.add_sub_cancel' hMd, pow_add]
    ring
  rw [e]
  exact mul_le_mul (pow_le_pow_of_le_one hγ0 hγ1 hNM)
    ((pow_le_pow_left₀ hμ0 hμP _).trans (pow_le_pow_right₀ hP1 hdE)) (pow_nonneg hμ0 _)
    (pow_nonneg hγ0 _)

theorem SE_exponents {n d k s T h : ℕ} (hd : d ≤ n) (hsk : s ≤ k) (hh : h = d / k) (hk0 : 0 < k)
    (hs : h * s ≤ n / T) :
    min (n - k) (h * (k - s)) ≤ d ∧ d - min (n - k) (h * (k - s)) ≤ k + n / T := by
  have h1 : h * k ≤ d := hh ▸ Nat.div_mul_le_self d k
  have h2 : d < h * k + k := hh ▸ Nat.lt_div_mul_add hk0
  have h3 : h * (k - s) = h * k - h * s := Nat.mul_sub h k s
  have h4 : h * s ≤ h * k := Nat.mul_le_mul_left h hsk
  omega

theorem SE_hs_le {n d T : ℕ} (hT : 0 < T) (hd : d ≤ n) : d / T ^ 6 * T ^ 5 ≤ n / T := by
  rw [Nat.le_div_iff_mul_le hT]
  calc d / T ^ 6 * T ^ 5 * T = d / T ^ 6 * T ^ 6 := by ring
    _ ≤ d := Nat.div_mul_le_self d _
    _ ≤ n := hd

set_option maxHeartbeats 1000000 in
theorem prob_badSE_le {n p : ℕ} [Fact p.Prime] (hT : Real.exp 170 ≤ (seT n : ℝ)) (hp23 : 23 ≤ p)
    (hpT : Real.log p ≤ seT n + 1) :
    prob (fun ω : Pairs n → Bool => SuppGood (seidelOf ω) ∧ ∃ (μ : ZMod p) (z : Fin n → ℤ),
      (fun j => ((z j : ℤ) : ZMod p)) ≠ 0 ∧
      (seidelOf ω).map (Int.castRingHom (ZMod p)) *ᵥ (fun j => ((z j : ℤ) : ZMod p)) =
        μ • (fun j => ((z j : ℤ) : ZMod p)) ∧
      ∑ j, ((z j : ℤ) : ℝ) ^ 2 ≤ cSE * n * (p : ℝ) ^ 2) ≤ Real.exp (-(n : ℝ)) := by
  classical
  have hTn : seT n ^ 8 ≤ n := seT_pow_le n
  set T := seT n with hTdef
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpR : (23 : ℝ) ≤ p := by exact_mod_cast hp23
  have hp0 : (0 : ℝ) < p := by linarith
  have hp2 : p ≠ 2 := by omega
  have hT128 : 128 ≤ T := by
    have h1 : (14621 : ℝ) ≤ Real.exp 170 := by
      have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 170)
      norm_num at this ⊢
      linarith
    have : (128 : ℝ) ≤ T := by linarith
    exact_mod_cast this
  have hTR : (128 : ℝ) ≤ T := by exact_mod_cast hT128
  have he30 : Real.exp 30 ≤ (T : ℝ) := (Real.exp_le_exp.2 (by norm_num)).trans hT
  have hk_n : T ^ 6 ≤ n := le_trans (Nat.pow_le_pow_right (by omega) (by norm_num)) hTn
  have hs1 := SE_hs1 (by omega) hp hpT
  have hs2 := SE_hs2 he30 hp hpT
  set A : ℕ := Nat.log 2 p + 1 with hAdef
  have hA : (p : ℝ) < 2 ^ A := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  have hA2 : (A : ℝ) ≤ 2 * ((T : ℝ) + 1) := by
    have h1 : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 hp.ne'
    have h2 : (2 : ℝ) ^ Nat.log 2 p ≤ p := by exact_mod_cast h1
    have h3 : (Nat.log 2 p : ℝ) * Real.log 2 ≤ Real.log p := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) h2
    have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have h4 : (Nat.log 2 p : ℝ) * 0.69 ≤ (Nat.log 2 p : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg _)
    rw [hAdef]
    push_cast
    linarith
  set μ0 : ℝ := gaussMu0 p (1 / (2 * cSE * (p : ℝ) ^ 2)) with hμ0def
  have hσ : 0 < 1 / (2 * cSE * (p : ℝ) ^ 2) := by have := cSE_pos; positivity
  have hμ0pos : 0 < μ0 := gaussMu0_pos hσ
  have hμ0le : μ0 ≤ 0.008 * p := by
    have h1 := (lem_gauss (p := p) cSE_pos (by norm_num [cSE])).2.1
    have h2 := sqrt_two_pi_cSE_le
    calc μ0 ≤ √(2 * π * cSE) * p := h1
      _ ≤ 0.008 * p := mul_le_mul_of_nonneg_right h2 hp0.le
  have hμ0p : μ0 ≤ p := by linarith
  set γ : ℝ := 6464 * √(π * ((T + 1 : ℕ) : ℝ)) * 1.001 / √(((T ^ 5 : ℕ) : ℝ)) with hγdef
  have hγ : γ ≤ 16222 / (T : ℝ) ^ 2 := SE_gamma_le (by omega)
  have hγ0 : 0 ≤ γ := by positivity
  have hγ1 : γ ≤ 1 := by
    refine hγ.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith
  have hζ : μ0 * (6464 * √(π * ((T + 1 : ℕ) : ℝ)) * (1.001 / μ0) / √(((T ^ 5 : ℕ) : ℝ))) = γ := by
    rw [hγdef]
    field_simp
  set B1 : ℝ := (1 + 1 / 100) ^ n * (p : ℝ) ^ (T ^ 6) * (1 / (p : ℝ) + 0.008) ^ n with hB1
  set B2 : ℝ := γ ^ (n / 20 - T ^ 6 - n / T) * (p : ℝ) ^ (T ^ 6 + n / T) with hB2
  set Bd : ℝ := Real.exp ((n : ℝ) / 2) * (B1 + A * (2 ^ n * B2)) with hBd
  set DS := (univ : Finset (Finset (Fin n))).filter (fun D => (n : ℝ) / 20 < D.card) with hDS
  let P : ZMod p → Finset (Fin n) → (Pairs n → Bool) → Prop := fun μ D ω =>
    ∃ y : Fin n → ZMod p, (∀ j, y j ≠ 0 ↔ j ∈ D) ∧
      (seidelOf ω).map (Int.castRingHom (ZMod p)) *ᵥ y = μ • y ∧
      (normSqLift y : ℝ) ≤ cSE * n * (p : ℝ) ^ 2
  have hone : ∀ μ : ZMod p, ∀ D ∈ DS, prob (P μ D) ≤ Bd := by
    intro μ D hD
    have hDn : (n : ℝ) / 20 < D.card := (mem_filter.1 hD).2
    have hdn : D.card ≤ n := by
      have := card_le_univ D
      rwa [Fintype.card_fin] at this
    have hd6 : T ^ 6 ≤ D.card := by
      have h1 : (T : ℝ) ^ 8 ≤ n := by exact_mod_cast hTn
      have h2 : (20 : ℝ) * (T : ℝ) ^ 6 ≤ (T : ℝ) ^ 8 := by
        have h20 : (20 : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
        have : (T : ℝ) ^ 8 = (T : ℝ) ^ 2 * (T : ℝ) ^ 6 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h20 (by positivity)
      have h3 : ((T ^ 6 : ℕ) : ℝ) < D.card := by push_cast; linarith
      exact_mod_cast h3.le
    have hT6 : 0 < T ^ 6 := by positivity
    have hh : 0 < D.card / T ^ 6 := Nat.div_pos hd6 hT6
    have hn20 : n / 20 ≤ D.card := by
      have h1 : n < 20 * D.card := by
        have : (n : ℝ) < 20 * D.card := by linarith
        exact_mod_cast this
      exact Nat.div_le_of_le_mul (by omega)
    obtain ⟨B, hBD, hBk, hBdisj⟩ := exists_blocks D (T ^ 6) (D.card / T ^ 6) (Nat.div_mul_le_self _ _)
    have hmain := prob_eigD_le (p := p) hp2 (l := T + 1) (s := T ^ 5) (k := T ^ 6)
      (h := D.card / T ^ 6) (A := A) (by omega) hs1 hs2 μ D hh B hBD hBk hBdisj hA
    obtain ⟨hMd, hdE⟩ := SE_exponents (n := n) (d := D.card) (k := T ^ 6) (s := T ^ 5) (T := T)
      (h := D.card / T ^ 6) hdn (Nat.pow_le_pow_right (by omega) (by norm_num)) rfl hT6
      (SE_hs_le (by omega) hdn)
    have hNM : n / 20 - T ^ 6 - n / T ≤ min (n - T ^ 6) (D.card / T ^ 6 * (T ^ 6 - T ^ 5)) := by
      omega
    have hX1 := SE_bound1 hp hμ0pos.le hμ0le hdn hk_n
    have hX2 := SE_bound2 hμ0pos.le hμ0p (by linarith) hζ hγ0 hγ1 hMd hNM hdE
    refine hmain.trans ?_
    rw [hBd]
    refine mul_le_mul_of_nonneg_left (add_le_add hX1 ?_) (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX2 (by positivity)) (Nat.cast_nonneg _)
  have hsub : ∀ ω : Pairs n → Bool, (SuppGood (seidelOf ω) ∧ ∃ (μ : ZMod p) (z : Fin n → ℤ),
      (fun j => ((z j : ℤ) : ZMod p)) ≠ 0 ∧
      (seidelOf ω).map (Int.castRingHom (ZMod p)) *ᵥ (fun j => ((z j : ℤ) : ZMod p)) =
        μ • (fun j => ((z j : ℤ) : ZMod p)) ∧
      ∑ j, ((z j : ℤ) : ℝ) ^ 2 ≤ cSE * n * (p : ℝ) ^ 2) →
      ∃ μ ∈ (univ : Finset (ZMod p)), ∃ D ∈ DS, P μ D ω := by
    rintro ω ⟨hS, μ, z, hz0, hz, hle⟩
    set y : Fin n → ZMod p := fun j => ((z j : ℤ) : ZMod p) with hy
    set D := (univ : Finset (Fin n)).filter (fun j => y j ≠ 0) with hD
    have hsupp : (n : ℝ) / 20 < D.card :=
      hS p (Fact.out) hp2 (ZMod p) μ y hz0 hz D
        (fun i hi => by
          by_contra h
          exact hi (mem_filter.2 ⟨mem_univ _, h⟩))
    refine ⟨μ, mem_univ _, D, mem_filter.2 ⟨mem_univ _, hsupp⟩, y, fun j => ?_, hz, ?_⟩
    · simp [hD]
    · have h1 : normSqLift y ≤ ∑ j, z j ^ 2 := normSqLift_le y z (fun j => rfl)
      have h2 : ((normSqLift y : ℤ) : ℝ) ≤ ((∑ j, z j ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith
  have hDS : (DS.card : ℝ) ≤ 2 ^ n := by
    have h1 : DS.card ≤ 2 ^ n := by
      refine (card_filter_le _ _).trans ?_
      rw [card_univ, Fintype.card_finset, Fintype.card_fin]
    exact_mod_cast h1
  have hBd0 : 0 ≤ Bd := by
    rw [hBd, hB1, hB2]
    positivity
  have ht1 := SE_term1 (T := T) (by omega) hTn hp23 hpT
  have ht2 := SE_term2 (A := A) hT hTn hp hpT hA2 hγ0 hγ
  calc prob (fun ω : Pairs n → Bool => SuppGood (seidelOf ω) ∧ ∃ (μ : ZMod p) (z : Fin n → ℤ),
        (fun j => ((z j : ℤ) : ZMod p)) ≠ 0 ∧
        (seidelOf ω).map (Int.castRingHom (ZMod p)) *ᵥ (fun j => ((z j : ℤ) : ZMod p)) =
          μ • (fun j => ((z j : ℤ) : ZMod p)) ∧
        ∑ j, ((z j : ℤ) : ℝ) ^ 2 ≤ cSE * n * (p : ℝ) ^ 2)
      ≤ prob (fun ω => ∃ μ ∈ (univ : Finset (ZMod p)), ∃ D ∈ DS, P μ D ω) := prob_mono hsub
    _ ≤ ∑ μ ∈ (univ : Finset (ZMod p)), prob (fun ω => ∃ D ∈ DS, P μ D ω) :=
        prob_exists_le_sum _ _
    _ ≤ ∑ μ ∈ (univ : Finset (ZMod p)), ∑ D ∈ DS, prob (P μ D) :=
        sum_le_sum fun μ _ => prob_exists_le_sum _ _
    _ ≤ ∑ _μ ∈ (univ : Finset (ZMod p)), ∑ _D ∈ DS, Bd :=
        sum_le_sum fun μ _ => sum_le_sum fun D hD => hone μ D hD
    _ = (p : ℝ) * DS.card * Bd := by
        rw [sum_const, sum_const, card_univ, ZMod.card, nsmul_eq_mul, nsmul_eq_mul]
        ring
    _ ≤ (p : ℝ) * 2 ^ n * Bd := by
        gcongr
    _ = (p : ℝ) * 2 ^ n * Real.exp ((n : ℝ) / 2) * B1 +
          (p : ℝ) * 2 ^ n * Real.exp ((n : ℝ) / 2) * (A * (2 ^ n * B2)) := by
        rw [hBd]
        ring
    _ ≤ Real.exp (-(n : ℝ)) / 2 + Real.exp (-(n : ℝ)) / 2 := add_le_add ht1 ht2
    _ = Real.exp (-(n : ℝ)) := by ring

def GoodSE {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → 23 ≤ p → (p : ℝ) ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 8)) →
    ∀ (μ : ZMod p) (z : Fin n → ℤ), (fun j => ((z j : ℤ) : ZMod p)) ≠ 0 →
      S.map (Int.castRingHom (ZMod p)) *ᵥ (fun j => ((z j : ℤ) : ZMod p)) =
        μ • (fun j => ((z j : ℤ) : ZMod p)) →
      cSE * n * (p : ℝ) ^ 2 < ∑ j, ((z j : ℤ) : ℝ) ^ 2

theorem SE_tail {n : ℕ} (hT : 2 ≤ seT n) :
    (Real.exp ((n : ℝ) ^ ((1 : ℝ) / 8)) + 1) * Real.exp (-(n : ℝ)) ≤ (2 : ℝ) ^ (-(n : ℝ) / 8) := by
  have hTn := seT_pow_le n
  have hlt := rpow_lt_seT_add_one n
  set T := seT n
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hnR : (T : ℝ) ^ 8 ≤ n := by exact_mod_cast hTn
  have h7 : (4 : ℝ) ≤ (T : ℝ) ^ 7 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT2 7
    norm_num at this
    linarith
  have h8 : 2 * (T : ℝ) ≤ (T : ℝ) ^ 8 / 2 := by
    have : (T : ℝ) ^ 8 = T * T ^ 7 := by ring
    nlinarith
  have h256 : (256 : ℝ) ≤ (T : ℝ) ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT2 8
    norm_num at this
    linarith
  have hx : (n : ℝ) ^ ((1 : ℝ) / 8) ≤ n / 2 := by linarith
  have h1 : Real.exp ((n : ℝ) ^ ((1 : ℝ) / 8)) + 1 ≤ 2 * Real.exp ((n : ℝ) ^ ((1 : ℝ) / 8)) := by
    have := Real.one_le_exp (Real.rpow_nonneg (Nat.cast_nonneg n) ((1 : ℝ) / 8))
    linarith
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc (Real.exp ((n : ℝ) ^ ((1 : ℝ) / 8)) + 1) * Real.exp (-(n : ℝ))
      ≤ 2 * Real.exp ((n : ℝ) ^ ((1 : ℝ) / 8)) * Real.exp (-(n : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (Real.log 2 + (n : ℝ) ^ ((1 : ℝ) / 8) + -(n : ℝ)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (Real.log 2 * (-(n : ℝ) / 8)) := by
        apply Real.exp_le_exp.2
        have hl2 := Real.log_two_lt_d9
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have h3 := mul_le_mul_of_nonneg_right hl2.le hn
        linarith

theorem thm_SEplus :
    ∀ᶠ n : ℕ in atTop, probSeidel n (fun S => ¬ GoodSE S) ≤ 2 * (2 : ℝ) ^ (-(n : ℝ) / 8) := by
  have hT : ∀ᶠ n : ℕ in atTop, Real.exp 170 ≤ (seT n : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp tendsto_seT).eventually_ge_atTop _
  filter_upwards [lem_support, hT] with n hsupp hTn
  classical
  set X : ℝ := Real.exp ((n : ℝ) ^ ((1 : ℝ) / 8)) with hX
  set PS := (range (⌊X⌋₊ + 1)).filter (fun p => p.Prime ∧ 23 ≤ p) with hPS
  let Bad : ℕ → (Pairs n → Bool) → Prop := fun p ω => SuppGood (seidelOf ω) ∧
    ∃ (μ : ZMod p) (z : Fin n → ℤ), (fun j => ((z j : ℤ) : ZMod p)) ≠ 0 ∧
      (seidelOf ω).map (Int.castRingHom (ZMod p)) *ᵥ (fun j => ((z j : ℤ) : ZMod p)) =
        μ • (fun j => ((z j : ℤ) : ZMod p)) ∧
      ∑ j, ((z j : ℤ) : ℝ) ^ 2 ≤ cSE * n * (p : ℝ) ^ 2
  have hsub : ∀ ω : Pairs n → Bool, ¬ GoodSE (seidelOf ω) →
      ¬ SuppGood (seidelOf ω) ∨ ∃ p ∈ PS, Bad p ω := by
    intro ω hω
    by_cases hS : SuppGood (seidelOf ω)
    · right
      unfold GoodSE at hω
      push Not at hω
      obtain ⟨p, hp, hp23, hpn, μ, z, hz0, hz, hle⟩ := hω
      refine ⟨p, ?_, hS, μ, z, hz0, hz, hle⟩
      rw [hPS, mem_filter, mem_range]
      refine ⟨?_, hp, hp23⟩
      have : p ≤ ⌊X⌋₊ := Nat.le_floor hpn
      omega
    · exact Or.inl hS
  have hbad : ∀ p ∈ PS, prob (Bad p) ≤ Real.exp (-(n : ℝ)) := by
    intro p hp
    rw [hPS, mem_filter, mem_range] at hp
    have : Fact p.Prime := ⟨hp.2.1⟩
    refine prob_badSE_le hTn hp.2.2 ?_
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
    have hple : (p : ℝ) ≤ X := by
      have h1 : p ≤ ⌊X⌋₊ := by omega
      exact (Nat.le_floor_iff (Real.exp_pos _).le).1 h1
    have h2 : Real.log p ≤ (n : ℝ) ^ ((1 : ℝ) / 8) := (Real.log_le_iff_le_exp hp0).2 hple
    have h3 := rpow_lt_seT_add_one n
    linarith
  have hcard : (PS.card : ℝ) ≤ X + 1 := by
    have h1 : PS.card ≤ ⌊X⌋₊ + 1 := (card_filter_le _ _).trans (card_range _).le
    have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le (Real.exp_pos _).le
    have h3 : (PS.card : ℝ) ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  have hT2 : 2 ≤ seT n := by
    have h1 : (2 : ℝ) ≤ Real.exp 170 := by
      have := Real.add_one_le_exp (170 : ℝ)
      linarith
    have : (2 : ℝ) ≤ seT n := h1.trans hTn
    exact_mod_cast this
  have htail := SE_tail hT2
  calc probSeidel n (fun S => ¬ GoodSE S)
      ≤ prob (fun ω : Pairs n → Bool => ¬ SuppGood (seidelOf ω) ∨ ∃ p ∈ PS, Bad p ω) :=
        prob_mono hsub
    _ ≤ prob (fun ω : Pairs n → Bool => ¬ SuppGood (seidelOf ω)) +
          prob (fun ω => ∃ p ∈ PS, Bad p ω) := prob_or_le _ _
    _ ≤ (2 : ℝ) ^ (-(n : ℝ) / 8) + ∑ p ∈ PS, prob (Bad p) :=
        add_le_add hsupp (prob_exists_le_sum _ _)
    _ ≤ (2 : ℝ) ^ (-(n : ℝ) / 8) + ∑ _p ∈ PS, Real.exp (-(n : ℝ)) :=
        add_le_add le_rfl (sum_le_sum hbad)
    _ = (2 : ℝ) ^ (-(n : ℝ) / 8) + PS.card * Real.exp (-(n : ℝ)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (-(n : ℝ) / 8) + (X + 1) * Real.exp (-(n : ℝ)) := by
        gcongr
    _ ≤ 2 * (2 : ℝ) ^ (-(n : ℝ) / 8) := by
        rw [hX]
        linarith

theorem muMin_gt_of_goodSE {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ} (hS : GoodSE S) {p : ℕ}
    [Fact p.Prime] (hp23 : 23 ≤ p) (hpn : (p : ℝ) ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 8))) {μ : ZMod p}
    {w : Fin n → ZMod p} (hw0 : w ≠ 0) (hw : S.map (Int.castRingHom (ZMod p)) *ᵥ w = μ • w) :
    cSE * n * (p : ℝ) ^ 2 < (muMin w : ℝ) := by
  obtain ⟨c, hc, hmu⟩ := exists_muMin_eq w
  set z : Fin n → ℤ := fun j => (c * w j).valMinAbs with hz
  have hzc : (fun j => ((z j : ℤ) : ZMod p)) = c • w := by
    funext j
    simp [hz, ZMod.coe_valMinAbs]
  have hcw0 : c • w ≠ 0 := smul_ne_zero hc hw0
  have hcw : S.map (Int.castRingHom (ZMod p)) *ᵥ (c • w) = μ • (c • w) := by
    rw [mulVec_smul, hw, smul_comm]
  have h1 := hS p Fact.out hp23 hpn μ z (by rw [hzc]; exact hcw0) (by rw [hzc]; exact hcw)
  have h2 : (∑ j, ((z j : ℤ) : ℝ) ^ 2) = (muMin w : ℝ) := by
    rw [hmu, normSqLift]
    push_cast
    rfl
  rwa [h2] at h1

theorem cor_ACplus {n : ℕ} {S : Matrix (Fin n) (Fin n) ℤ} (hS : GoodSE S) {p : ℕ} [Fact p.Prime]
    (hp23 : 23 ≤ p) (hpn : (p : ℝ) ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 8))) {μ : ZMod p}
    {w : Fin n → ZMod p} (hw0 : w ≠ 0) (hw : S.map (Int.castRingHom (ZMod p)) *ᵥ w = μ • w) :
    rhoG w ≤ 1 / p + Real.exp (-2 * cSE * n) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp2 : p ≠ 2 := by omega
  have h1 := muMin_gt_of_goodSE hS hp23 hpn hw0 hw
  have h3 := lem_dilates_rho hp2 w
  have h4 : Real.exp (-2 * (muMin w : ℝ) / (p : ℝ) ^ 2) ≤ Real.exp (-2 * cSE * n) := by
    apply Real.exp_le_exp.2
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith [h3.1, h3.2]

end DGS
