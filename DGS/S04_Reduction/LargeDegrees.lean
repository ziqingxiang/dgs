module

public import DGS.S04_Reduction.Reduction
public import DGS.S04_Reduction.Budget
public import DGS.External
public import DGS.Core.Components
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

open Matrix Polynomial Filter Topology Real
open scoped ENNReal

namespace DGS

theorem lem_simplespectrum (hTV : TaoVuStatement) :
    Tendsto (fun m : ℕ => probSeidel m (fun S => S.charpoly.discr = 0)) atTop (𝓝 0) :=
  hTV

theorem abeta_le_inv_cube {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {m : ℕ} (T : Matrix (Fin m) (Fin m) ℤ)
    (β : (ZMod p)[X]) {N : ℕ} (hN : 1 ≤ N) (hd : 3 * logb 2 N ≤ (β.natDegree : ℝ)) :
    abeta p T β ≤ ((N : ℝ) ^ 3)⁻¹ := by
  refine (abeta_le hp T β).trans ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) ^ 3 ≤ (2 : ℝ) ^ β.natDegree := by
    have h2 : (2 : ℝ) ^ (3 * logb 2 N) = (N : ℝ) ^ 3 := by
      rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hN0]
      norm_num
    rw [← h2, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hd
  rw [inv_pow]
  exact inv_anti₀ (by positivity) h1

theorem NPi_le_of_large_degree {m N : ℕ} (hN : 1 ≤ N) (PS : Set (ℕ × ℕ))
    (hPS : ∀ x ∈ PS, x.1.Prime ∧ x.1 ≠ 2 ∧ 3 * logb 2 N ≤ (x.2 : ℝ))
    {T : Matrix (Fin m) (Fin m) ℤ} (hT : T.IsSymm) (hT1 : ∀ i j, |T i j| ≤ 1)
    (hΔ : T.charpoly.discr ≠ 0) :
    NPi PS T ≤ ENNReal.ofReal ((m : ℝ) ^ 2 * Real.log (2 * m) / Real.log 2 * ((N : ℝ) ^ 3)⁻¹) := by
  classical
  set C : ℝ := (m : ℝ) ^ 2 * Real.log (2 * m) / Real.log 2 with hC
  have hC0 : 0 ≤ C := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [hC, h0]; simp
    · have : (1 : ℝ) ≤ m := by exact_mod_cast h0
      have hl : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
  rw [NPi]
  refine tsum_le_of_sum_le' (zero_le) fun s => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  set s' := s.filter fun x : (Σ p : ℕ, (ZMod p)[X]) =>
    (x.1, x.2.natDegree) ∈ PS ∧ IsRepeatedFactor x.1 T x.2 with hs'
  have hterm : ∀ x ∈ s', ENNReal.ofReal (abeta x.1 T x.2) ≤ ENNReal.ofReal (((N : ℝ) ^ 3)⁻¹) := by
    intro x hx
    obtain ⟨hp, hp2, hd⟩ := hPS _ (Finset.mem_filter.1 hx).2.1
    have : Fact x.1.Prime := ⟨hp⟩
    exact ENNReal.ofReal_le_ofReal (abeta_le_inv_cube hp2 T x.2 hN hd)
  have hcard : (s'.card : ℝ) ≤ C := by
    refine lem_budget_b hT hT1 hΔ (le_refl 2) s' fun x hx => ?_
    obtain ⟨hcond, hrep⟩ := (Finset.mem_filter.1 hx).2
    obtain ⟨hp, hp2, -⟩ := hPS _ hcond
    refine ⟨hp, ?_, hrep⟩
    have h2 := hp.two_le
    have h3 : 3 ≤ x.1 := by omega
    exact_mod_cast (by omega : 2 < x.1)
  calc ∑ x ∈ s', ENNReal.ofReal (abeta x.1 T x.2)
      ≤ ∑ _x ∈ s', ENNReal.ofReal (((N : ℝ) ^ 3)⁻¹) := Finset.sum_le_sum hterm
    _ = s'.card * ENNReal.ofReal (((N : ℝ) ^ 3)⁻¹) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (((N : ℝ) ^ 3)⁻¹) := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hcard
    _ = ENNReal.ofReal (C * ((N : ℝ) ^ 3)⁻¹) := (ENNReal.ofReal_mul hC0).symm

theorem expectNPi_le {m : ℕ} (PS : Set (ℕ × ℕ)) (G : Set (Matrix (Fin m) (Fin m) ℤ)) {b : ℝ≥0∞}
    (hb : ∀ ω : Pairs m → Bool, seidelOf ω ∈ G → NPi PS (seidelOf ω) ≤ b) : expectNPi PS m G ≤ b := by
  classical
  rw [expectNPi]
  refine ENNReal.div_le_of_le_mul ?_
  calc ∑ ω : Pairs m → Bool, (if seidelOf ω ∈ G then NPi PS (seidelOf ω) else 0)
      ≤ ∑ _ω : Pairs m → Bool, b := Finset.sum_le_sum fun ω _ => by
        split_ifs with h
        · exact hb ω h
        · exact zero_le
    _ = b * (Fintype.card (Pairs m → Bool) : ℝ≥0∞) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

theorem tendsto_log_two_mul_div : Tendsto (fun n : ℕ => Real.log (2 * n) / n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0)) atTop (𝓝 0) :=
    tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 := h1.comp tendsto_natCast_atTop_atTop
  have h3 : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h4 := h3.add h2
  rw [add_zero] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [Function.comp_apply, pow_one, one_mul, add_zero]
  rw [Real.log_mul (by norm_num) hn0, add_div]

theorem thm_largedegrees (hTV : TaoVuStatement) : Thm22 := by
  classical
  unfold Thm22
  set PS : ℕ → Set (ℕ × ℕ) := fun n => {x | x.1.Prime ∧ x.1 ≠ 2 ∧ 3 * logb 2 n ≤ (x.2 : ℝ)} with hPS
  set G : ∀ n, Set (Matrix (Fin n) (Fin n) ℤ) := fun n => {S | S.charpoly.discr ≠ 0} with hGdef
  have hG : Tendsto (fun n => probSeidel n (fun S => S ∉ G n)) atTop (𝓝 0) := by
    refine (lem_simplespectrum hTV).congr fun n => ?_
    exact prob_congr fun ω => by simp [hGdef]
  set u : ℕ → ℝ := fun n => (n : ℝ) ^ 2 * Real.log (2 * n) / Real.log 2 * ((n : ℝ) ^ 3)⁻¹ with hu
  have hu0 : Tendsto u atTop (𝓝 0) := by
    have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have := tendsto_log_two_mul_div.div_const (Real.log 2)
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp only [hu]
    field_simp
  have hbound : ∀ n m : ℕ, 1 ≤ n → m ≤ n → ∀ PSn : Set (ℕ × ℕ),
      (∀ x ∈ PSn, x.1.Prime ∧ x.1 ≠ 2 ∧ 3 * logb 2 n ≤ (x.2 : ℝ)) →
      expectNPi PSn m (G m) ≤ ENNReal.ofReal (u n) := by
    intro n m hn hmn PSn hPSn
    refine expectNPi_le _ _ fun ω hω => (NPi_le_of_large_degree hn PSn hPSn (isSeidel_seidelOf ω).1
      (fun i j => ?_) hω).trans (ENNReal.ofReal_le_ofReal ?_)
    · by_cases hij : i = j
      · subst hij; rw [(isSeidel_seidelOf ω).2.1]; norm_num
      · rcases (isSeidel_seidelOf ω).2.2 i j hij with h1 | h1 <;> rw [h1] <;> norm_num
    ·
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hinv : 0 ≤ ((n : ℝ) ^ 3)⁻¹ := by positivity
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        simp only [Nat.cast_zero, mul_zero, Real.log_zero, zero_div, zero_mul, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        simp only [hu]
        have : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
        positivity
      · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h0
        have hlog : Real.log (2 * m) ≤ Real.log (2 * n) := Real.log_le_log (by linarith) (by linarith)
        have hl0 : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
        simp only [hu]
        gcongr
  have hN : Tendsto (fun n => expectNPi (PS n) n (G n)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => ENNReal.ofReal (u n)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hu0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hbound n n hn le_rfl (PS n) fun x hx => hx
  have hN' : Tendsto (fun n => expectNPi (PS (n + 1)) n (G n)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => ENNReal.ofReal (u (n + 1))) atTop (𝓝 0) := by
      have := hu0.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) fun n => ?_
    exact hbound (n + 1) n (by omega) (by omega) (PS (n + 1)) fun x hx => hx
  have hmain := prop_reduction PS (fun n x hx => ⟨hx.1, hx.2.1⟩) G G hG hG hN hN'
  refine hmain.congr fun n => ?_
  refine prob_congr fun Gr => ?_
  constructor
  · rintro ⟨p, d, ⟨hp, hp2, hd⟩, hE⟩
    exact ⟨p, d, hp, hp2, hd, hE⟩
  · rintro ⟨p, d, hp, hp2, hd, hE⟩
    exact ⟨p, d, ⟨hp, hp2, hd⟩, hE⟩

end DGS
