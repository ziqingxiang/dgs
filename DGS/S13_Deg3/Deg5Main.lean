module

public import DGS.S13_Deg3.Deg5

@[expose] public section

open Finset Filter Topology Matrix Polynomial Module
open scoped Real ENNReal

namespace DGS

def PSdeg5 (ε : ℝ) (n : ℕ) : Set (ℕ × ℕ) :=
  {x | x.1.Prime ∧ x.1 ≠ 2 ∧ (n : ℝ) ^ (1 / 2 - ε) < (x.1 : ℝ) ∧
    (x.1 : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧ 5 ≤ x.2 ∧ (x.2 : ℝ) < 3 * Real.logb 2 n}

theorem deg5_abeta_le {ε : ℝ} {N m : ℕ} (hL1 : 1 ≤ Real.logb 2 N)
    (hA : 200 * (Real.logb 2 N) ^ 2 ≤ (N : ℝ) ^ (2 * ε)) (hC : 2 * (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) - 1)
    (hB : 100 * (Real.logb 2 N) ^ 4 ≤ (N : ℝ)) (hD : 2 ≤ (N : ℝ) ^ (1 / 2 - ε)) (h32 : 32 ≤ N)
    (hE : (N : ℝ) ^ (1 / 10 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 8)) (hm : N - 1 ≤ m)
    {T : Matrix (Fin m) (Fin m) ℤ} (hS : SuppGoodS T) {x : Σ p : ℕ, (ZMod p)[X]}
    (hx : (x.1, x.2.natDegree) ∈ PSdeg5 ε N) :
    abeta x.1 T x.2 ≤ (2 * (N : ℝ) ^ (-(1 / 2 - ε))) ^ 5 := by
  obtain ⟨hp, hp2, hpN, hpX, hd5, hdL⟩ := hx
  dsimp only at hp hp2 hpN hpX hd5 hdL
  have : Fact x.1.Prime := ⟨hp⟩
  obtain ⟨ht, hdm, hsum⟩ := deg5_numbers (p := x.1) hL1 hA hC hB hm h32 hd5 hdL hpN
  have hN32 : (32 : ℝ) ≤ N := by exact_mod_cast h32
  have hN0 : (0 : ℝ) < N := by linarith
  have hpm : (x.1 : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) := by
    refine hpX.trans (Real.exp_le_exp.2 (hE.trans ?_))
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hm) (by norm_num)
  have h1 := abeta_le_of_suppGood hS hp2 hpm rfl (by omega) hdm ht
  have hb0 : 0 ≤ 1 / (x.1 : ℝ) + 1 / √(π * ((((m / (4 * (x.2.natDegree + 1)) + 1) + x.2.natDegree - 1) /
      x.2.natDegree / 2 : ℕ) : ℝ)) := by positivity
  have hbase1 : 2 * (N : ℝ) ^ (-(1 / 2 - ε)) ≤ 1 := by
    have e : (N : ℝ) ^ (1 / 2 - ε) * (N : ℝ) ^ (-(1 / 2 - ε)) = 1 := by
      rw [← Real.rpow_add hN0]
      simp
    have h0 : 0 < (N : ℝ) ^ (-(1 / 2 - ε)) := Real.rpow_pos_of_pos hN0 _
    nlinarith
  have hbase0 : 0 ≤ 2 * (N : ℝ) ^ (-(1 / 2 - ε)) := by positivity
  calc abeta x.1 T x.2
      ≤ (1 / (x.1 : ℝ) + 1 / √(π * ((((m / (4 * (x.2.natDegree + 1)) + 1) + x.2.natDegree - 1) /
          x.2.natDegree / 2 : ℕ) : ℝ))) ^ x.2.natDegree := h1
    _ ≤ (2 * (N : ℝ) ^ (-(1 / 2 - ε))) ^ x.2.natDegree := pow_le_pow_left₀ hb0 hsum _
    _ ≤ (2 * (N : ℝ) ^ (-(1 / 2 - ε))) ^ 5 := pow_le_pow_of_le_one hbase0 hbase1 hd5

theorem deg5_count_le {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) {N m : ℕ} (h32 : 32 ≤ N) (hm1 : 1 ≤ m)
    (hmN : m ≤ N) :
    (m : ℝ) ^ 2 * Real.log (2 * m) / Real.log ((N : ℝ) ^ (1 / 2 - ε)) ≤ 3 * (N : ℝ) ^ 2 := by
  have hN32 : (32 : ℝ) ≤ N := by exact_mod_cast h32
  have hN0 : (0 : ℝ) < N := by linarith
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hlogN : Real.log 32 ≤ Real.log N := Real.log_le_log (by norm_num) hN32
  have hl32 : 5 * Real.log 2 = Real.log 32 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN0 : 0 < Real.log N := by linarith
  have hP : Real.log ((N : ℝ) ^ (1 / 2 - ε)) = (1 / 2 - ε) * Real.log N := Real.log_rpow hN0 _
  rw [hP, div_le_iff₀ (by nlinarith)]
  have hlog2m : Real.log (2 * m) ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) hN0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hlog2m0 : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
  have hm2 : (m : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hmN' 2
  calc (m : ℝ) ^ 2 * Real.log (2 * m) ≤ (N : ℝ) ^ 2 * (Real.log 2 + Real.log N) :=
        mul_le_mul hm2 hlog2m hlog2m0 (by positivity)
    _ ≤ 3 * (N : ℝ) ^ 2 * ((1 / 2 - ε) * Real.log N) := by
        have h1 : Real.log 2 + Real.log N ≤ 3 * ((1 / 2 - ε) * Real.log N) := by nlinarith
        nlinarith [sq_nonneg (N : ℝ)]

theorem NPi_deg5_le {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, N - 1 ≤ m → m ≤ N → ∀ T : Matrix (Fin m) (Fin m) ℤ, T.IsSymm →
      (∀ i j, |T i j| ≤ 1) → T.charpoly.discr ≠ 0 → SuppGoodS T →
        NPi (PSdeg5 ε N) T ≤ ENNReal.ofReal (3 * (N : ℝ) ^ 2 * (2 * (N : ℝ) ^ (-(1 / 2 - ε))) ^ 5) := by
  filter_upwards [deg5_eventually hε0 hε] with N hN
  obtain ⟨hL1, hA, hC, hB, hD, h32, hE⟩ := hN
  intro m hm hmN T hT hT1 hΔ hS
  classical
  have hm1 : 1 ≤ m := by omega
  set b : ℝ := (2 * (N : ℝ) ^ (-(1 / 2 - ε))) ^ 5 with hb
  have hb0 : 0 ≤ b := by positivity
  set C : ℝ := (m : ℝ) ^ 2 * Real.log (2 * m) / Real.log ((N : ℝ) ^ (1 / 2 - ε)) with hCdef
  have hC3 : C ≤ 3 * (N : ℝ) ^ 2 := deg5_count_le hε0 hε h32 hm1 hmN
  rw [NPi]
  refine tsum_le_of_sum_le' (zero_le) fun s => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  set s' := s.filter fun x : (Σ p : ℕ, (ZMod p)[X]) =>
    (x.1, x.2.natDegree) ∈ PSdeg5 ε N ∧ IsRepeatedFactor x.1 T x.2 with hs'
  have hterm : ∀ x ∈ s', ENNReal.ofReal (abeta x.1 T x.2) ≤ ENNReal.ofReal b := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal
      (deg5_abeta_le hL1 hA hC hB hD h32 hE hm hS (Finset.mem_filter.1 hx).2.1)
  have hcard : (s'.card : ℝ) ≤ C := by
    refine lem_budget_b hT hT1 hΔ hD s' fun x hx => ?_
    obtain ⟨hcond, hrep⟩ := (Finset.mem_filter.1 hx).2
    exact ⟨hcond.1, hcond.2.2.1, hrep⟩
  have hC0 : 0 ≤ C := le_trans (Nat.cast_nonneg _) hcard
  calc ∑ x ∈ s', ENNReal.ofReal (abeta x.1 T x.2)
      ≤ ∑ _x ∈ s', ENNReal.ofReal b := Finset.sum_le_sum hterm
    _ = s'.card * ENNReal.ofReal b := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal b := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hcard
    _ = ENNReal.ofReal (C * b) := (ENNReal.ofReal_mul hC0).symm
    _ ≤ ENNReal.ofReal (3 * (N : ℝ) ^ 2 * b) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC3 hb0)

theorem tendsto_deg5_bound {ε : ℝ} (hε : ε < 1 / 10) :
    Tendsto (fun N : ℕ => 3 * (N : ℝ) ^ 2 * (2 * (N : ℝ) ^ (-(1 / 2 - ε))) ^ 5) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 - 5 * ε))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have h2 := h1.const_mul 96
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (-(1 / 2 - ε))), ← Real.rpow_mul hN0.le,
    ← Real.rpow_natCast (N : ℝ) 2]
  have e : (N : ℝ) ^ ((2 : ℕ) : ℝ) * (N : ℝ) ^ (-(1 / 2 - ε) * ((5 : ℕ) : ℝ)) =
      (N : ℝ) ^ (-(1 / 2 - 5 * ε)) := by
    rw [← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  calc 96 * (N : ℝ) ^ (-(1 / 2 - 5 * ε))
      = 3 * 2 ^ 5 * ((N : ℝ) ^ ((2 : ℕ) : ℝ) * (N : ℝ) ^ (-(1 / 2 - ε) * ((5 : ℕ) : ℝ))) := by
        rw [e]
        norm_num
    _ = 3 * (N : ℝ) ^ ((2 : ℕ) : ℝ) * (2 ^ 5 * (N : ℝ) ^ (-(1 / 2 - ε) * ((5 : ℕ) : ℝ))) := by ring

theorem prop_deg5 (hTV : TaoVuStatement) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) :
    Tendsto (fun n : ℕ => probG n (fun G => ∃ p d : ℕ, (p, d) ∈ PSdeg5 ε n ∧ E p d G)) atTop (𝓝 0) := by
  classical
  set G : ∀ n, Set (Matrix (Fin n) (Fin n) ℤ) := fun n => {T | T.charpoly.discr ≠ 0 ∧ SuppGoodS T}
    with hGdef
  have hG : Tendsto (fun n => probSeidel n (fun S => S ∉ G n)) atTop (𝓝 0) := by
    have h1 := lem_simplespectrum hTV
    have h2 : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) / 8)) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n : ℕ => -(n : ℝ) / 8) atTop atBot := by
        have := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg (r := -(1 / 8 : ℝ))
          (by norm_num)
        refine this.congr fun n => ?_
        ring
      exact Real.tendsto_exp_atBot.comp h3
    have h4 := h1.add h2
    rw [add_zero] at h4
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h4
      (Eventually.of_forall fun _ => prob_nonneg _) ?_
    filter_upwards [prob_not_suppGoodPM] with n hn
    calc probSeidel n (fun S => S ∉ G n)
        ≤ prob (fun ω : Pairs n → Bool => (seidelOf ω).charpoly.discr = 0 ∨ ¬ SuppGoodPM ω) :=
          prob_mono fun ω h => by
            simp only [hGdef, Set.mem_ofPred_eq, not_and_or, not_not] at h
            exact h
      _ ≤ probSeidel n (fun S => S.charpoly.discr = 0) + prob (fun ω : Pairs n → Bool => ¬ SuppGoodPM ω) :=
          prob_or_le _ _
      _ ≤ probSeidel n (fun S => S.charpoly.discr = 0) + Real.exp (-(n : ℝ) / 8) := add_le_add le_rfl hn
  have hsym : ∀ {m : ℕ} (ω : Pairs m → Bool), (seidelOf ω).IsSymm ∧ ∀ i j, |seidelOf ω i j| ≤ 1 := by
    intro m ω
    refine ⟨(isSeidel_seidelOf ω).1, fun i j => ?_⟩
    by_cases hij : i = j
    · subst hij; rw [(isSeidel_seidelOf ω).2.1]; norm_num
    · rcases (isSeidel_seidelOf ω).2.2 i j hij with h1 | h1 <;> rw [h1] <;> norm_num
  have hev := NPi_deg5_le hε0 hε
  have hu := tendsto_deg5_bound hε
  have hN : Tendsto (fun n => expectNPi (PSdeg5 ε n) n (G n)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (3 * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(1 / 2 - ε))) ^ 5))
        atTop (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hev] with n hn
    exact expectNPi_le _ _ fun ω hω => hn n (by omega) le_rfl _ (hsym ω).1 (hsym ω).2 hω.1 hω.2
  have hN' : Tendsto (fun n => expectNPi (PSdeg5 ε (n + 1)) n (G n)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (3 * ((n + 1 : ℕ) : ℝ) ^ 2 *
        (2 * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 - ε))) ^ 5)) atTop (𝓝 0) := by
      have := hu.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    have hev' := (tendsto_add_atTop_nat 1).eventually hev
    filter_upwards [hev'] with n hn
    exact expectNPi_le _ _ fun ω hω => hn n (by omega) (by omega) _ (hsym ω).1 (hsym ω).2 hω.1 hω.2
  exact prop_reduction (PSdeg5 ε) (fun n x hx => ⟨hx.1, hx.2.1⟩) G G hG hG hN hN'

end DGS
