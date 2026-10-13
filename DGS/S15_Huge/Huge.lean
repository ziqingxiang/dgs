module

public import DGS.S15_Huge.AcInv
public import DGS.S14_NoFactor.NoFactor
public import DGS.S04_Reduction.LargeDegrees

@[expose] public section

open Matrix Polynomial Filter Topology
open scoped ENNReal

namespace DGS

theorem NPi_le_of_huge {n : ℕ} (hn : 3 ≤ n) (PS : Set (ℕ × ℕ))
    (hPS : ∀ x ∈ PS, x.1.Prime ∧ x.1 ≠ 2 ∧ Real.exp ((Real.log n) ^ 6) < x.1)
    {T : Matrix (Fin n) (Fin n) ℤ} (hT : IsSeidel T) (hΔ : T.charpoly.discr ≠ 0)
    (habeta : ∀ (p : ℕ) [Fact p.Prime], Real.exp ((Real.log n) ^ 6) < p → ∀ β : (ZMod p)[X],
      abeta p T β ≤ ((n : ℝ) ^ 3)⁻¹) :
    NPi PS T ≤ ENNReal.ofReal ((n : ℝ) ^ 2 * Real.log (2 * n) * ((n : ℝ) ^ 3)⁻¹) := by
  classical
  set C : ℝ := (n : ℝ) ^ 2 * Real.log (2 * n) with hC
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hC0 : 0 ≤ C := by
    have : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
    positivity
  have hT1 : ∀ i j, |T i j| ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [hT.2.1]
      norm_num
    · rcases hT.2.2 i j hij with h | h <;> rw [h] <;> norm_num
  have hlog1 : 1 ≤ Real.log n := by
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hlog6 : 1 ≤ (Real.log n) ^ 6 := one_le_pow₀ hlog1
  set P := Real.exp ((Real.log n) ^ 6) with hP
  have hP2 : 2 ≤ P := by
    have := Real.add_one_le_exp ((Real.log n) ^ 6)
    linarith
  rw [NPi]
  refine tsum_le_of_sum_le' (zero_le) fun s => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  set s' := s.filter fun x : (Σ p : ℕ, (ZMod p)[X]) =>
    (x.1, x.2.natDegree) ∈ PS ∧ IsRepeatedFactor x.1 T x.2 with hs'
  have hterm : ∀ x ∈ s', ENNReal.ofReal (abeta x.1 T x.2) ≤ ENNReal.ofReal (((n : ℝ) ^ 3)⁻¹) := by
    intro x hx
    obtain ⟨hp, -, hpP⟩ := hPS _ (Finset.mem_filter.1 hx).2.1
    have : Fact x.1.Prime := ⟨hp⟩
    exact ENNReal.ofReal_le_ofReal (habeta x.1 hpP x.2)
  have hcard : (s'.card : ℝ) ≤ C := by
    have h1 := lem_budget_b hT.1 hT1 hΔ hP2 s' fun x hx => by
      obtain ⟨hcond, hrep⟩ := (Finset.mem_filter.1 hx).2
      obtain ⟨hp, -, hpP⟩ := hPS _ hcond
      exact ⟨hp, hpP, hrep⟩
    rw [hP, Real.log_exp] at h1
    exact h1.trans (div_le_self hC0 hlog6)
  calc ∑ x ∈ s', ENNReal.ofReal (abeta x.1 T x.2)
      ≤ ∑ _x ∈ s', ENNReal.ofReal (((n : ℝ) ^ 3)⁻¹) := Finset.sum_le_sum hterm
    _ = s'.card * ENNReal.ofReal (((n : ℝ) ^ 3)⁻¹) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (((n : ℝ) ^ 3)⁻¹) := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hcard
    _ = ENNReal.ofReal (C * ((n : ℝ) ^ 3)⁻¹) := (ENNReal.ofReal_mul hC0).symm

theorem tendsto_prob_not_noSmallFactor :
    Tendsto (fun n : ℕ => probSeidel n (fun S => ¬ NoSmallFactor S)) atTop (𝓝 0) := by
  have hnf := thm_nofactor (1 / 30) (by norm_num) (by norm_num)
  have hlog := eventually_mul_log_pow_le_rpow 1 3 (by norm_num : (0 : ℝ) < 1 / 30)
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) ^ (1 / 9 - 1 / 30 : ℝ) / 9)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 9 - 1 / 30 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    have h4 : Tendsto (fun n : ℕ => -(n : ℝ) ^ (1 / 9 - 1 / 30 : ℝ) / 9) atTop atBot := by
      have h5 := (tendsto_neg_atTop_atBot.comp h3).atBot_div_const (by norm_num : (0 : ℝ) < 9)
      refine h5.congr fun n => ?_
      simp
    exact Real.tendsto_exp_atBot.comp h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
    (Eventually.of_forall fun n => prob_nonneg _) ?_
  filter_upwards [hnf, hlog] with n hn hl
  unfold probSeidel at hn ⊢
  refine le_trans (prob_mono fun ω hω => ?_) hn
  unfold NoSmallFactor at hω
  push Not at hω
  obtain ⟨f, hf, hf1, hfl, hfS⟩ := hω
  rw [one_mul] at hl
  exact ⟨f, hf, hf1, hfl.trans hl, hfS⟩

theorem thm_huge (hTV : TaoVuStatement) : Thm26 := by
  classical
  unfold Thm26
  set PS : ℕ → Set (ℕ × ℕ) := fun n =>
    {x | x.1.Prime ∧ x.1 ≠ 2 ∧ Real.exp ((Real.log n) ^ 6) < x.1 ∧ 1 ≤ x.2} with hPS
  set G : ∀ n, Set (Matrix (Fin n) (Fin n) ℤ) := fun n => {S | S.charpoly.discr ≠ 0 ∧ NoSmallFactor S} with hGdef
  have hG : Tendsto (fun n => probSeidel n (fun S => S ∉ G n)) atTop (𝓝 0) := by
    have h3 := (lem_simplespectrum hTV).add tendsto_prob_not_noSmallFactor
    rw [add_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun n => prob_nonneg _)
      fun n => ?_
    unfold probSeidel
    refine (prob_mono fun ω hω => ?_).trans (prob_or_le _ _)
    simp only [hGdef, Set.mem_ofPred_eq, not_and_or, not_not] at hω
    exact hω
  set u : ℕ → ℝ := fun n => (n : ℝ) ^ 2 * Real.log (2 * n) * ((n : ℝ) ^ 3)⁻¹ with hu
  have hu0 : Tendsto u atTop (𝓝 0) := by
    refine tendsto_log_two_mul_div.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp only [hu]
    field_simp
  have hlim : Tendsto (fun n => ENNReal.ofReal (u n)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hu0
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ PSn : Set (ℕ × ℕ),
      (∀ x ∈ PSn, x.1.Prime ∧ x.1 ≠ 2 ∧ Real.exp ((Real.log n) ^ 6) < x.1) →
      expectNPi PSn n (G n) ≤ ENNReal.ofReal (u n) := by
    filter_upwards [abeta_lt_of_acinv, eventually_ge_atTop 3] with n hab hn3
    intro PSn hPSn
    refine expectNPi_le _ _ fun ω hω => ?_
    exact NPi_le_of_huge hn3 PSn hPSn (isSeidel_seidelOf ω) hω.1
      fun p _ hp β => (hab _ (isSeidel_seidelOf ω) hω.2 p hp β).le
  have hN : Tendsto (fun n => expectNPi (PS n) n (G n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hbound] with n hn
    exact hn (PS n) fun x hx => ⟨hx.1, hx.2.1, hx.2.2.1⟩
  have hN' : Tendsto (fun n => expectNPi (PS (n + 1)) n (G n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hbound, eventually_ge_atTop 1] with n hn hn1
    refine hn (PS (n + 1)) fun x hx => ⟨hx.1, hx.2.1, lt_of_le_of_lt ?_ hx.2.2.1⟩
    apply Real.exp_le_exp.2
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have h1 : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (by push_cast; linarith)
    have h0 : 0 ≤ Real.log n := Real.log_nonneg hn1'
    exact pow_le_pow_left₀ h0 h1 6
  have hmain := prop_reduction PS (fun n x hx => ⟨hx.1, hx.2.1⟩) G G hG hG hN hN'
  refine hmain.congr fun n => ?_
  refine prob_congr fun Gr => ?_
  constructor
  · rintro ⟨p, d, ⟨hp, hp2, hpe, hd⟩, hE⟩
    exact ⟨p, d, hp, hp2, hpe, hd, hE⟩
  · rintro ⟨p, d, hp, hp2, hpe, hd, hE⟩
    exact ⟨p, d, ⟨hp, hp2, hpe, hd⟩, hE⟩

end DGS
