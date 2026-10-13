module

public import DGS.S13_Deg3.Deg34

@[expose] public section

open Finset Filter Topology Matrix Polynomial Module
open scoped Real ENNReal

namespace DGS

theorem exp_tail_le {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) {n : ℕ} {x : ℝ} (_hx0 : 0 ≤ x) (hx : x ≤ c / 2 * n)
    (hn : 2 * K * n ≤ Real.exp (c * n)) :
    K * n * (Real.exp x + 1) * Real.exp (-2 * c * n) ≤ Real.exp (-(c / 2) * n) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : Real.exp x + 1 ≤ 2 * Real.exp (c / 2 * n) := by
    have h2 : Real.exp x ≤ Real.exp (c / 2 * n) := Real.exp_le_exp.2 hx
    have h3 : 1 ≤ Real.exp (c / 2 * n) := Real.one_le_exp (by positivity)
    linarith
  calc K * n * (Real.exp x + 1) * Real.exp (-2 * c * n)
      ≤ K * n * (2 * Real.exp (c / 2 * n)) * Real.exp (-2 * c * n) := by gcongr
    _ = (2 * K * n) * (Real.exp (c / 2 * n) * Real.exp (-2 * c * n)) := by ring
    _ ≤ Real.exp (c * n) * (Real.exp (c / 2 * n) * Real.exp (-2 * c * n)) := by gcongr
    _ = Real.exp (-(c / 2) * n) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf

theorem div_floor_cube_le {ε : ℝ} (_hε : ε < 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) / ((⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 3 ≤ (n : ℝ) ^ (-(1 / 2 - 3 * ε)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) ^ (1 / 2 - ε) ≤ (⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have h2 : ((n : ℝ) ^ (1 / 2 - ε)) ^ 3 ≤ ((⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 3 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hn0.le _) h1 3
  have h3 : ((n : ℝ) ^ (1 / 2 - ε)) ^ 3 = (n : ℝ) ^ (3 * (1 / 2 - ε)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    ring_nf
  have h4 : (n : ℝ) = (n : ℝ) ^ (-(1 / 2 - 3 * ε)) * (n : ℝ) ^ (3 * (1 / 2 - ε)) := by
    rw [← Real.rpow_add hn0]
    ring_nf
    rw [Real.rpow_one]
  have h5 : 0 < (n : ℝ) ^ (3 * (1 / 2 - ε)) := Real.rpow_pos_of_pos hn0 _
  rw [div_le_iff₀ (by positivity)]
  calc (n : ℝ) = (n : ℝ) ^ (-(1 / 2 - 3 * ε)) * (n : ℝ) ^ (3 * (1 / 2 - ε)) := h4
    _ ≤ (n : ℝ) ^ (-(1 / 2 - 3 * ε)) * ((⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 3 := by
        rw [← h3]
        exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hn0.le _)

theorem tendsto_floor_rpow {ε : ℝ} (hε : ε < 1 / 2) :
    Tendsto (fun n : ℕ => ⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 / 2 - ε)).comp
    tendsto_natCast_atTop_atTop)

theorem floor_rpow_mono {ε : ℝ} (hε : ε < 1 / 2) (n : ℕ) :
    ⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ ≤ ⌊((n + 1 : ℕ) : ℝ) ^ (1 / 2 - ε)⌋₊ := by
  apply Nat.floor_le_floor
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) (by push_cast; linarith) (by linarith)

theorem tendsto_exp_neg_mul {c : ℝ} (hc : 0 < c) : Tendsto (fun n : ℕ => Real.exp (-c * n)) atTop (𝓝 0) := by
  have h3 : Tendsto (fun n : ℕ => -c * (n : ℝ)) atTop atBot :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg (by linarith)
  exact Real.tendsto_exp_atBot.comp h3

theorem ofReal_tendsto {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => ENNReal.ofReal (u n)) atTop (𝓝 0) := by
  simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hu

theorem tendsto_sqrt_nat : Tendsto (fun n : ℕ => Nat.sqrt n) atTop atTop :=
  tendsto_atTop_atTop.2 fun K => ⟨K * K, fun _n hn => Nat.le_sqrt.2 hn⟩

theorem deg34_eventually {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) :
    ∀ᶠ n : ℕ in atTop, 22 ≤ ⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ ∧ 1 ≤ n ∧
      ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ cSEd / 2 * n ∧
      ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 9) ∧
      2 * (1 / 6) * (n : ℝ) ≤ Real.exp (cSEd * n) ∧ 2 ≤ Nat.sqrt n ∧
      3 * (n : ℝ) ≤ Real.exp (cRK / 8 * n) := by
  filter_upwards [(tendsto_floor_rpow (by linarith : ε < 1 / 2)).eventually_ge_atTop 22,
    eventually_ge_atTop 1, eventually_rpow_tenth_succ_le_mul (by have := cSEd_pos; positivity : 0 < cSEd / 2),
    eventually_rpow_tenth_succ_le_ninth, eventually_mul_le_exp (b := cSEd) (K := 2 * (1 / 6)) cSEd_pos
      (by norm_num), tendsto_sqrt_nat.eventually_ge_atTop 2,
    eventually_mul_le_exp (b := cRK / 8) (K := 3) (by have := cRK_pos; positivity) (by norm_num)]
    with n h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem hNm_of {n N : ℕ} (hn1 : 1 ≤ n) (hN : N ≤ n + 1)
    (h4 : ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 9)) :
    (N : ℝ) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 8) := by
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h1 : (N : ℝ) ^ (1 / 10 : ℝ) ≤ ((n : ℝ) + 1) ^ (1 / 10 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hN) (by norm_num)
  have h2 : (n : ℝ) ^ ((1 : ℝ) / 9) ≤ (n : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hn1R (by norm_num)
  linarith

theorem hNc_of {n N : ℕ} {c : ℝ} (hN : N ≤ n + 1) (h3 : ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ c / 2 * n) :
    (N : ℝ) ^ (1 / 10 : ℝ) ≤ c / 2 * n :=
  (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hN) (by norm_num)).trans h3

theorem prop_deg4 {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) :
    Tendsto (fun n : ℕ => probG n (fun G => ∃ p d : ℕ, (p, d) ∈ PSdeg4 ε n ∧ E p d G)) atTop (𝓝 0) := by
  classical
  set G : ∀ n, Set (Matrix (Fin n) (Fin n) ℤ) := fun n => {T | GoodSEd 4 T} with hGdef
  have hG : Tendsto (fun n => probSeidel n (fun S => S ∉ G n)) atTop (𝓝 0) := by
    refine tendsto_prob_zero_of_le (tendsto_exp_neg_mul (c := 1 / 9) (by norm_num)) ?_
    filter_upwards [prop_SEd (d := 4) (by norm_num) le_rfl] with n hn
    refine le_trans (le_of_eq (prob_congr fun ω => by simp [hGdef])) (hn.trans (le_of_eq ?_))
    ring_nf
  set a : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ with ha
  set U : ℕ → ℝ := fun n => (n : ℝ) / 4 / ((a n : ℝ) + 1) ^ 3 + Real.exp (-(cSEd / 2) * n) with hU
  have hU0 : Tendsto U atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) / 4 / ((a n : ℝ) + 1) ^ 3) atTop (𝓝 0) := by
      have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 - 3 * ε)) / 4) atTop (𝓝 0) := by
        have := ((tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1 / 2 - 3 * ε)).comp
          tendsto_natCast_atTop_atTop).div_const 4
        simpa using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Eventually.of_forall fun n => by positivity) ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have := div_floor_cube_le (by linarith : ε < 1 / 2) hn
      simp only [ha]
      rw [div_div, mul_comm, ← div_div]
      exact div_le_div_of_nonneg_right this (by norm_num)
    have := h1.add (tendsto_exp_neg_mul (c := cSEd / 2) (by have := cSEd_pos; positivity))
    rw [add_zero] at this
    exact this
  have hbound : ∀ n N : ℕ, (N = n ∨ N = n + 1) → 22 ≤ ⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ → 1 ≤ n →
      ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ cSEd / 2 * n → ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 9) →
      2 * (1 / 6) * (n : ℝ) ≤ Real.exp (cSEd * n) →
      expectNPi (PSdeg4 ε N) n (G n) ≤ ENNReal.ofReal (U n) := by
    intro n N hN h22 hn1 h3 h4 h5
    have hNle : N ≤ n + 1 := by omega
    have hmN : n ≤ N := by omega
    have haN : a n ≤ ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ := by
      rcases hN with rfl | rfl
      · exact le_rfl
      · exact floor_rpow_mono (by linarith) n
    refine (expectNPi_deg4_bound hε0 hε hmN (h22.trans haN) (hNm_of hn1 hNle h4)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have ht : (n : ℝ) / 8 * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) * Real.exp (-2 * cSEd * n) ≤
        Real.exp (-(cSEd / 2) * n) := by
      have := exp_tail_le (K := 1 / 8) cSEd_pos (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (hNc_of hNle h3) (by nlinarith [Real.exp_pos (cSEd * n)])
      calc (n : ℝ) / 8 * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) * Real.exp (-2 * cSEd * n)
          = 1 / 8 * n * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) * Real.exp (-2 * cSEd * n) := by ring
        _ ≤ _ := this
    have hf : (n : ℝ) / 4 / ((⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 3 ≤ (n : ℝ) / 4 / ((a n : ℝ) + 1) ^ 3 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : (a n : ℝ) ≤ (⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) := by exact_mod_cast haN
      gcongr
    simp only [hU]
    linarith
  have hN : Tendsto (fun n => expectNPi (PSdeg4 ε n) n (G n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (ofReal_tendsto hU0)
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [deg34_eventually hε0 hε] with n hn
    obtain ⟨h22, hn1, h3, h4, h5, -, -⟩ := hn
    exact hbound n n (Or.inl rfl) h22 hn1 h3 h4 h5
  have hN' : Tendsto (fun n => expectNPi (PSdeg4 ε (n + 1)) n (G n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (ofReal_tendsto hU0)
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [deg34_eventually hε0 hε] with n hn
    obtain ⟨h22, hn1, h3, h4, h5, -, -⟩ := hn
    exact hbound n (n + 1) (Or.inr rfl) h22 hn1 h3 h4 h5
  exact prop_reduction (PSdeg4 ε) (fun n x hx => ⟨hx.1, hx.2.1⟩) G G hG hG hN hN'

noncomputable def V3 (s : ℝ) : ℝ := 16 / (3 * Real.log s) + 2 / √s

theorem V3_anti {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) : V3 t ≤ V3 s := by
  unfold V3
  have hL : 0 < Real.log s := Real.log_pos (by linarith)
  have hLst : Real.log s ≤ Real.log t := Real.log_le_log (by linarith) hst
  have hsq : √s ≤ √t := Real.sqrt_le_sqrt hst
  have hsq0 : 0 < √s := Real.sqrt_pos.2 (by linarith)
  gcongr

theorem tendsto_V3 : Tendsto (fun n : ℕ => V3 (Nat.sqrt n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => ((Nat.sqrt n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_sqrt_nat
  have h1 : Tendsto (fun n : ℕ => 16 / (3 * Real.log (Nat.sqrt n))) atTop (𝓝 0) := by
    have := ((Real.tendsto_log_atTop.comp hs).const_mul_atTop (by norm_num : (0 : ℝ) < 3)).const_div_atTop 16
    exact this
  have h2 : Tendsto (fun n : ℕ => 2 / √(Nat.sqrt n : ℝ)) atTop (𝓝 0) := by
    have := (Real.tendsto_sqrt_atTop.comp hs).const_div_atTop 2
    exact this
  have := h1.add h2
  rw [add_zero] at this
  exact this

theorem deg3b_main_le {m s : ℕ} (hs : 2 ≤ s) (hm : (m : ℝ) ≤ 4 * (s : ℝ) ^ 2) :
    (m : ℝ) / 6 * (8 / ((s : ℝ) ^ 2 * Real.log s) + 3 * √(s : ℝ) / (s : ℝ) ^ 3) ≤ V3 s := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hL : 0 < Real.log s := Real.log_pos (by linarith)
  have hsq0 : 0 < √(s : ℝ) := Real.sqrt_pos.2 hs0
  have hsq : √(s : ℝ) * √(s : ℝ) = s := Real.mul_self_sqrt hs0.le
  have hA : 0 ≤ 8 / ((s : ℝ) ^ 2 * Real.log s) + 3 * √(s : ℝ) / (s : ℝ) ^ 3 := by positivity
  calc (m : ℝ) / 6 * (8 / ((s : ℝ) ^ 2 * Real.log s) + 3 * √(s : ℝ) / (s : ℝ) ^ 3)
      ≤ 4 * (s : ℝ) ^ 2 / 6 * (8 / ((s : ℝ) ^ 2 * Real.log s) + 3 * √(s : ℝ) / (s : ℝ) ^ 3) := by
        gcongr
    _ = 16 / (3 * Real.log s) + 2 * (√(s : ℝ) / s) := by
        field_simp
        ring
    _ = V3 s := by
        rw [Real.sqrt_div_self']
        unfold V3
        ring

theorem prop_deg3b {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) :
    Tendsto (fun n : ℕ => probG n (fun G => ∃ p d : ℕ, (p, d) ∈ PSdeg3b ε n ∧ E p d G)) atTop (𝓝 0) := by
  classical
  set G : ∀ n, Set (Matrix (Fin n) (Fin n) ℤ) := fun n => {T | GoodSEd 3 T} with hGdef
  have hG : Tendsto (fun n => probSeidel n (fun S => S ∉ G n)) atTop (𝓝 0) := by
    refine tendsto_prob_zero_of_le (tendsto_exp_neg_mul (c := 1 / 9) (by norm_num)) ?_
    filter_upwards [prop_SEd (d := 3) (by norm_num) (by norm_num)] with n hn
    refine le_trans (le_of_eq (prob_congr fun ω => by simp [hGdef])) (hn.trans (le_of_eq ?_))
    ring_nf
  set U : ℕ → ℝ := fun n => V3 (Nat.sqrt n) + Real.exp (-(cSEd / 2) * n) with hU
  have hU0 : Tendsto U atTop (𝓝 0) := by
    have := tendsto_V3.add (tendsto_exp_neg_mul (c := cSEd / 2) (by have := cSEd_pos; positivity))
    rw [add_zero] at this
    exact this
  have hbound : ∀ n N : ℕ, (N = n ∨ N = n + 1) → 22 ≤ ⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ → 1 ≤ n →
      ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ cSEd / 2 * n → ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 9) →
      2 * (1 / 6) * (n : ℝ) ≤ Real.exp (cSEd * n) → 2 ≤ Nat.sqrt n →
      expectNPi (PSdeg3b ε N) n (G n) ≤ ENNReal.ofReal (U n) := by
    intro n N hN h22 hn1 h3 h4 h5 hs2
    have hNle : N ≤ n + 1 := by omega
    have hmN : n ≤ N := by omega
    have haN : ⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ ≤ ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ := by
      rcases hN with rfl | rfl
      · exact le_rfl
      · exact floor_rpow_mono (by linarith) n
    have hsN : Nat.sqrt n ≤ Nat.sqrt N := Nat.sqrt_le_sqrt hmN
    refine (expectNPi_deg3b_bound hε0 hε hmN (h22.trans haN) (hNm_of hn1 hNle h4) (hs2.trans hsN)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have ht : (n : ℝ) / 6 * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) * Real.exp (-2 * cSEd * n) ≤
        Real.exp (-(cSEd / 2) * n) := by
      have := exp_tail_le (K := 1 / 6) cSEd_pos (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (hNc_of hNle h3) h5
      calc (n : ℝ) / 6 * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) * Real.exp (-2 * cSEd * n)
          = 1 / 6 * n * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) * Real.exp (-2 * cSEd * n) := by ring
        _ ≤ _ := this
    have hm4 : (n : ℝ) ≤ 4 * ((Nat.sqrt N : ℕ) : ℝ) ^ 2 := by
      have h1 := Nat.lt_succ_sqrt N
      have h2 : n < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := lt_of_le_of_lt hmN h1
      have h3 : 1 ≤ Nat.sqrt N := by omega
      have h4 : n ≤ 4 * (Nat.sqrt N * Nat.sqrt N) := by nlinarith
      have h5 : (n : ℝ) ≤ ((4 * (Nat.sqrt N * Nat.sqrt N) : ℕ) : ℝ) := by exact_mod_cast h4
      push_cast at h5
      nlinarith
    have hmain := deg3b_main_le (hs2.trans hsN) hm4
    have hV := V3_anti (s := (Nat.sqrt n : ℝ)) (t := (Nat.sqrt N : ℝ)) (by exact_mod_cast hs2)
      (by exact_mod_cast hsN)
    simp only [hU]
    linarith
  have hN : Tendsto (fun n => expectNPi (PSdeg3b ε n) n (G n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (ofReal_tendsto hU0)
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [deg34_eventually hε0 hε] with n hn
    obtain ⟨h22, hn1, h3, h4, h5, hs2, -⟩ := hn
    exact hbound n n (Or.inl rfl) h22 hn1 h3 h4 h5 hs2
  have hN' : Tendsto (fun n => expectNPi (PSdeg3b ε (n + 1)) n (G n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (ofReal_tendsto hU0)
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [deg34_eventually hε0 hε] with n hn
    obtain ⟨h22, hn1, h3, h4, h5, hs2, -⟩ := hn
    exact hbound n (n + 1) (Or.inr rfl) h22 hn1 h3 h4 h5 hs2
  exact prop_reduction (PSdeg3b ε) (fun n x hx => ⟨hx.1, hx.2.1⟩) G G hG hG hN hN'

theorem prop_deg3s {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) :
    Tendsto (fun n : ℕ => probG n (fun G => ∃ p d : ℕ, (p, d) ∈ PSdeg3s ε n ∧ E p d G)) atTop (𝓝 0) := by
  classical
  set G : ∀ n, Set (Matrix (Fin n) (Fin n) ℤ) := fun n => {T | GoodSEd 3 T} with hGdef
  have hG : Tendsto (fun n => probSeidel n (fun S => S ∉ G n)) atTop (𝓝 0) := by
    refine tendsto_prob_zero_of_le (tendsto_exp_neg_mul (c := 1 / 9) (by norm_num)) ?_
    filter_upwards [prop_SEd (d := 3) (by norm_num) (by norm_num)] with n hn
    refine le_trans (le_of_eq (prob_congr fun ω => by simp [hGdef])) (hn.trans (le_of_eq ?_))
    ring_nf
  set a : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ with ha
  set U : ℕ → ℝ := fun n => 4 / ((a n : ℝ) + 1) ^ 2 + Real.exp (-(cRK / 2) * n) with hU
  have hU0 : Tendsto U atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 4 / ((a n : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => (a n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp (tendsto_floor_rpow (by linarith)))
      have h3 : Tendsto (fun n : ℕ => ((a n : ℝ) + 1) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp h2
      exact h3.const_div_atTop 4
    have := h1.add (tendsto_exp_neg_mul (c := cRK / 2) (by have := cRK_pos; positivity))
    rw [add_zero] at this
    exact this
  have hbound : ∀ n N : ℕ, (N = n ∨ N = n + 1) → 22 ≤ ⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ → 1 ≤ n →
      ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 9) → 3 * (n : ℝ) ≤ Real.exp (cRK / 8 * n) →
      (∀ (p : ℕ) [Fact p.Prime], (n : ℝ) ^ (0.4 : ℝ) ≤ p → (p : ℝ) ≤ 2 * √(n : ℝ) →
        ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], finrank (ZMod p) L = 3 →
        ∀ μ : L, μ ∉ Set.range (algebraMap (ZMod p) L) →
          prob (fun ω : Pairs n → Bool => 1 ≤ geomMult (F := L) 1 (-1) μ ω) ≤
            1 / (p : ℝ) ^ 3 + 1.2 / ((p : ℝ) ^ 3) ^ 2 + Real.exp (-cRK * n)) →
      expectNPi (PSdeg3s ε N) n (G n) ≤ ENNReal.ofReal (U n) := by
    intro n N hN h22 hn1 h4 h7 hR3
    have hNle : N ≤ n + 1 := by omega
    have hmN : n ≤ N := by omega
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have haN : a n ≤ ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ := by
      rcases hN with rfl | rfl
      · exact le_rfl
      · exact floor_rpow_mono (by linarith) n
    have hNm := hNm_of hn1 hNle h4
    have hR3' : ∀ p ∈ (PfinDeg1 ε N).filter (fun p => p * p ≤ N), ∀ [Fact p.Prime],
        ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], finrank (ZMod p) L = 3 →
        ∀ μ : L, μ ∉ Set.range (algebraMap (ZMod p) L) →
          prob (fun ω : Pairs n → Bool => 1 ≤ geomMult (F := L) 1 (-1) μ ω) ≤
            1 / (p : ℝ) ^ 3 + 1.2 / ((p : ℝ) ^ 3) ^ 2 + Real.exp (-cRK * n) := by
      intro p hp _
      have hok := pfinOK_of_sub (d := 3) hε0 hε hmN (h22.trans haN) hNm (Finset.filter_subset _ _) p hp
      refine hR3 p (hok.2.2.2 (by norm_num)) ?_
      have hpp : p * p ≤ N := (Finset.mem_filter.1 hp).2
      have h1 : ((p * p : ℕ) : ℝ) ≤ N := by exact_mod_cast hpp
      have h2 : (N : ℝ) ≤ 4 * n := by
        have : (N : ℝ) ≤ n + 1 := by exact_mod_cast hNle
        linarith
      push_cast at h1
      have h3 : (p : ℝ) ≤ √(4 * (n : ℝ)) := Real.le_sqrt_of_sq_le (by nlinarith)
      rw [Real.sqrt_mul (by norm_num), show √(4 : ℝ) = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h3
      exact h3
    refine (expectNPi_deg3s_bound hε0 hε hmN (h22.trans haN) hNm hR3').trans (ENNReal.ofReal_le_ofReal ?_)
    have hsN : ((Nat.sqrt N : ℕ) : ℝ) ≤ n + 1 := by
      have h1 : Nat.sqrt N ≤ N := Nat.sqrt_le_self N
      have h2 : (Nat.sqrt N : ℝ) ≤ N := by exact_mod_cast h1
      have h3 : (N : ℝ) ≤ n + 1 := by exact_mod_cast hNle
      linarith
    have hs0 : (0 : ℝ) ≤ (Nat.sqrt N : ℕ) := Nat.cast_nonneg _
    have hpoly : ((Nat.sqrt N : ℕ) : ℝ) * (3 + ((Nat.sqrt N : ℕ) : ℝ) ^ 3) ≤ (3 * (n : ℝ)) ^ 4 := by
      have h1 : ((Nat.sqrt N : ℕ) : ℝ) * (3 + ((Nat.sqrt N : ℕ) : ℝ) ^ 3) ≤ (n + 1) * (3 + (n + 1) ^ 3) := by
        gcongr
      have h2 : ((n : ℝ) + 1) * (3 + (n + 1) ^ 3) ≤ (3 * (n : ℝ)) ^ 4 := by
        have e1 : (n : ℝ) + 1 ≤ 2 * n := by linarith
        have e2 : ((n : ℝ) + 1) ^ 3 ≤ (2 * (n : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) e1 3
        have e3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1R
        have e4 : (3 : ℝ) + ((n : ℝ) + 1) ^ 3 ≤ 3 * (n : ℝ) ^ 3 + (2 * (n : ℝ)) ^ 3 := by linarith
        calc ((n : ℝ) + 1) * (3 + (n + 1) ^ 3) ≤ (2 * n) * (3 * (n : ℝ) ^ 3 + (2 * (n : ℝ)) ^ 3) :=
              mul_le_mul e1 e4 (by positivity) (by positivity)
          _ = 22 * (n : ℝ) ^ 4 := by ring
          _ ≤ (3 * (n : ℝ)) ^ 4 := by
              have : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
              nlinarith
      linarith
    have hexp : (3 * (n : ℝ)) ^ 4 ≤ Real.exp (cRK / 2 * n) := by
      calc (3 * (n : ℝ)) ^ 4 ≤ Real.exp (cRK / 8 * n) ^ 4 := pow_le_pow_left₀ (by positivity) h7 4
        _ = Real.exp (cRK / 2 * n) := by rw [← Real.exp_nat_mul]; ring_nf
    have ht : ((Nat.sqrt N : ℕ) : ℝ) * (3 + ((Nat.sqrt N : ℕ) : ℝ) ^ 3) * Real.exp (-cRK * n) ≤
        Real.exp (-(cRK / 2) * n) := by
      calc ((Nat.sqrt N : ℕ) : ℝ) * (3 + ((Nat.sqrt N : ℕ) : ℝ) ^ 3) * Real.exp (-cRK * n)
          ≤ Real.exp (cRK / 2 * n) * Real.exp (-cRK * n) :=
            mul_le_mul_of_nonneg_right (hpoly.trans hexp) (Real.exp_pos _).le
        _ = Real.exp (-(cRK / 2) * n) := by rw [← Real.exp_add]; ring_nf
    have hf : 4 / ((⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 2 ≤ 4 / ((a n : ℝ) + 1) ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have : (a n : ℝ) ≤ (⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) := by exact_mod_cast haN
      gcongr
    simp only [hU]
    linarith
  have hN : Tendsto (fun n => expectNPi (PSdeg3s ε n) n (G n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (ofReal_tendsto hU0)
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [deg34_eventually hε0 hε, thm_rank3] with n hn hR3
    obtain ⟨h22, hn1, -, h4, -, -, h7⟩ := hn
    exact hbound n n (Or.inl rfl) h22 hn1 h4 h7 hR3
  have hN' : Tendsto (fun n => expectNPi (PSdeg3s ε (n + 1)) n (G n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (ofReal_tendsto hU0)
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [deg34_eventually hε0 hε, thm_rank3] with n hn hR3
    obtain ⟨h22, hn1, -, h4, -, -, h7⟩ := hn
    exact hbound n (n + 1) (Or.inr rfl) h22 hn1 h4 h7 hR3
  exact prop_reduction (PSdeg3s ε) (fun n x hx => ⟨hx.1, hx.2.1⟩) G G hG hG hN hN'

theorem prop_deg34 {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) :
    Tendsto (fun n : ℕ => probG n (fun G => ∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧ (d = 3 ∨ d = 4) ∧ E p d G)) atTop (𝓝 0) := by
  have h4 := prop_deg4 hε0 hε
  have h3b := prop_deg3b hε0 hε
  have h3s := prop_deg3s hε0 hε
  have hsum := (h4.add h3b).add h3s
  rw [add_zero, add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => prob_nonneg _) fun n => ?_
  simp only [probG_eq_prob]
  refine (prob_mono fun G hG => ?_).trans ((prob_or_le _ _).trans (add_le_add (prob_or_le _ _) le_rfl))
  obtain ⟨p, d, hp, hp2, h1, h2, hd, hE⟩ := hG
  rcases hd with rfl | rfl
  · by_cases hpp : n < p * p
    · exact Or.inl (Or.inr ⟨p, 3, ⟨hp, hp2, h1, h2, hpp, rfl⟩, hE⟩)
    · exact Or.inr ⟨p, 3, ⟨hp, hp2, h1, h2, not_lt.1 hpp, rfl⟩, hE⟩
  · exact Or.inl (Or.inl ⟨p, 4, ⟨hp, hp2, h1, h2, rfl⟩, hE⟩)

theorem prop_deg3plus (hTV : TaoVuStatement) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) :
    Tendsto (fun n : ℕ => probG n (fun G => ∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧ 3 ≤ d ∧ (d : ℝ) < 3 * Real.logb 2 n ∧ E p d G))
      atTop (𝓝 0) := by
  have h5 := prop_deg5 hTV hε0 hε
  have h34 := prop_deg34 hε0 hε
  have hsum := h5.add h34
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => prob_nonneg _) fun n => ?_
  simp only [probG_eq_prob]
  refine (prob_mono fun G hG => ?_).trans (prob_or_le _ _)
  obtain ⟨p, d, hp, hp2, h1, h2, hd3, hdl, hE⟩ := hG
  by_cases hd5 : 5 ≤ d
  · exact Or.inl ⟨p, d, ⟨hp, hp2, h1, h2, hd5, hdl⟩, hE⟩
  · exact Or.inr ⟨p, d, hp, hp2, h1, h2, by omega, hE⟩

end DGS
