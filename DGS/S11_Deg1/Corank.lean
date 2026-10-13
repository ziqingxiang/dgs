module

public import DGS.S03_Prelim.Apriori

@[expose] public section

open Finset

namespace DGS

section Exposure

variable {m : ℕ}

def succPairs (ω : Pairs m → Bool) (ξ : Fin m → Bool) : Pairs (m + 1) → Bool :=
  (pairsSuccEquiv m).symm (ω, ξ)

@[simp] theorem pairsSuccEquiv_succPairs (ω : Pairs m → Bool) (ξ : Fin m → Bool) :
    pairsSuccEquiv m (succPairs ω ξ) = (ω, ξ) :=
  (pairsSuccEquiv m).apply_symm_apply _

theorem prob_succPairs (P : (Pairs (m + 1) → Bool) → Prop) :
    prob P = prob (fun x : (Pairs m → Bool) × (Fin m → Bool) => P (succPairs x.1 x.2)) :=
  (prob_equiv (pairsSuccEquiv m).symm P).symm

theorem expect_succPairs (X : (Pairs (m + 1) → Bool) → ℝ) :
    expect X = expect (fun ω : Pairs m → Bool => expect (fun ξ : Fin m → Bool => X (succPairs ω ξ))) := by
  rw [← expect_equiv (pairsSuccEquiv m).symm X, expect_prod]
  rfl

def EaccRec (E : ∀ m, (Pairs m → Bool) → Prop) (m0 : ℕ) : ∀ m, (Pairs m → Bool) → Prop
  | 0 => fun _ => True
  | m + 1 => fun ω' => EaccRec E m0 m (pairsSuccEquiv m ω').1 ∧ (m0 ≤ m → E m (pairsSuccEquiv m ω').1)

theorem EaccRec_succPairs (E : ∀ m, (Pairs m → Bool) → Prop) (m0 : ℕ) (ω : Pairs m → Bool)
    (ξ : Fin m → Bool) :
    EaccRec E m0 (m + 1) (succPairs ω ξ) ↔ EaccRec E m0 m ω ∧ (m0 ≤ m → E m ω) := by
  simp only [EaccRec, pairsSuccEquiv_succPairs]

theorem prob_not_EaccRec_le (E : ∀ m, (Pairs m → Bool) → Prop) (m0 : ℕ) :
    ∀ n, prob (fun ω : Pairs n → Bool => ¬ EaccRec E m0 n ω) ≤
      ∑ j ∈ Ico m0 n, prob (fun ω : Pairs j → Bool => ¬ E j ω)
  | 0 => by
    simp only [EaccRec, not_true_eq_false, Ico_eq_empty_of_le (Nat.zero_le _), sum_empty]
    exact le_of_eq prob_false
  | n + 1 => by
    rw [prob_succPairs]
    simp only [EaccRec_succPairs, not_and_or]
    refine (prob_or_le _ _).trans ?_
    rw [prob_fst (Ω' := Fin n → Bool) (fun ω : Pairs n → Bool => ¬ EaccRec E m0 n ω)]
    have ih := prob_not_EaccRec_le E m0 n
    by_cases hn : m0 ≤ n
    · rw [sum_Ico_succ_top hn]
      have h2 : prob (fun x : (Pairs n → Bool) × (Fin n → Bool) => ¬(m0 ≤ n → E n x.1)) =
          prob (fun ω : Pairs n → Bool => ¬ E n ω) := by
        rw [← prob_fst (Ω' := Fin n → Bool) (fun ω : Pairs n → Bool => ¬ E n ω)]
        exact prob_congr fun x => by simp [hn]
      rw [h2]
      linarith
    · have h2 : prob (fun x : (Pairs n → Bool) × (Fin n → Bool) => ¬(m0 ≤ n → E n x.1)) = 0 := by
        rw [prob_congr (Q := fun _ => False) fun x => by simp [hn]]
        exact prob_false
      have h3 : Ico m0 (n + 1) = Ico m0 n := by
        rw [Ico_eq_empty_of_le (by omega), Ico_eq_empty_of_le (by omega)]
      rw [h2, h3]
      linarith

end Exposure

noncomputable def potV (r : ℕ) : ℝ := if 2 ≤ r then (10 : ℝ) ^ (r - 2) else 0

theorem potV_nonneg (r : ℕ) : 0 ≤ potV r := by
  unfold potV
  split_ifs <;> positivity

theorem potV_le_pow (r : ℕ) : potV r ≤ (10 : ℝ) ^ r := by
  unfold potV
  split_ifs
  · exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le r 2)
  · positivity

theorem indicator_two_le_potV (r : ℕ) : (if 2 ≤ r then (1 : ℝ) else 0) ≤ potV r := by
  unfold potV
  split_ifs
  · exact one_le_pow₀ (by norm_num)
  · exact le_rfl

theorem expect_le_of_le_indicator {Ω : Type*} [Fintype Ω] [Nonempty Ω] {X : Ω → ℝ} {P : Ω → Prop}
    {c d : ℝ} (_hc : 0 ≤ c) (h : ∀ ω, X ω ≤ c * @ite ℝ (P ω) (Classical.dec _) 1 0 + d) :
    expect X ≤ c * prob P + d := by
  refine (expect_mono h).trans (le_of_eq ?_)
  rw [expect_add, expect_const_mul, expect_indicator', expect_const]

theorem expect_indicator_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    expect (fun ω => @ite ℝ (P ω) (Classical.dec _) 1 0) ≤ 1 := by
  rw [expect_indicator']
  exact prob_le_one _

theorem corank_numbers {q ϖ : ℝ} (hq : 23 ≤ q) (hϖ0 : 0 ≤ ϖ) (hϖ : ϖ ≤ 1 / 100000) :
    q⁻¹ + ϖ + (0.1 + 10 * ((q ^ 2)⁻¹ + ϖ)) ≤ 0.163 ∧
    (q⁻¹ + ϖ) ^ 2 / (1 - (q⁻¹ + ϖ + (0.1 + 10 * ((q ^ 2)⁻¹ + ϖ)))) ≤ 1.2 / q ^ 2 + ϖ := by
  have hq0 : 0 < q := by linarith
  set x := q⁻¹ with hx
  have hx0 : 0 < x := inv_pos.2 hq0
  have hx1 : x ≤ 1 / 23 := by
    rw [hx, one_div]
    exact inv_anti₀ (by norm_num) hq
  have hq2 : (q ^ 2)⁻¹ = x ^ 2 := by rw [hx, inv_pow]
  rw [hq2]
  have hϑ : x + ϖ + (0.1 + 10 * (x ^ 2 + ϖ)) ≤ 0.163 := by nlinarith
  refine ⟨hϑ, ?_⟩
  have hden : 0.837 ≤ 1 - (x + ϖ + (0.1 + 10 * (x ^ 2 + ϖ))) := by linarith
  rw [div_le_iff₀ (by linarith), show 1.2 / q ^ 2 = 1.2 * x ^ 2 by rw [hx, inv_pow, div_eq_mul_inv]]
  have h1 : (x + ϖ) ^ 2 ≤ x ^ 2 + 0.1 * ϖ := by nlinarith
  have h2 : 0 ≤ 1.2 * x ^ 2 + ϖ := by positivity
  nlinarith

theorem corank_potential {q ϖ : ℝ} (hq : 23 ≤ q) (hϖ0 : 0 ≤ ϖ) (hϖ : ϖ ≤ 1 / 100000)
    (r : ∀ m, (Pairs m → Bool) → ℕ) (E : ∀ m, (Pairs m → Bool) → Prop) {m0 n : ℕ}
    (hstep1 : ∀ m (ω : Pairs m → Bool) (ξ : Fin m → Bool), r (m + 1) (succPairs ω ξ) ≤ r m ω + 1)
    (hstep2 : ∀ m (ω : Pairs m → Bool) (ξ : Fin m → Bool), r m ω ≤ r (m + 1) (succPairs ω ξ) + 1)
    (ht0 : ∀ m, m0 ≤ m → m < n → ∀ ω, E m ω → r m ω = 0 →
      prob (fun ξ : Fin m → Bool => 1 ≤ r (m + 1) (succPairs ω ξ)) ≤ q⁻¹ + ϖ)
    (ht1 : ∀ m, m0 ≤ m → m < n → ∀ ω, E m ω → 1 ≤ r m ω →
      prob (fun ξ : Fin m → Bool => r m ω ≤ r (m + 1) (succPairs ω ξ)) ≤ (q ^ r m ω)⁻¹ + ϖ)
    (hC : ∀ m, expect (fun ω : Pairs m → Bool => (10 : ℝ) ^ r m ω) ≤ C0) :
    (∀ m, m0 ≤ m → m ≤ n → prob (fun ω : Pairs m → Bool => 2 ≤ r m ω ∧ EaccRec E m0 m ω) ≤
        1.2 / q ^ 2 + ϖ + C0 * (0.163 : ℝ) ^ (((m : ℝ) - m0 - 1) / 2)) ∧
    (m0 < n → prob (fun ω : Pairs n → Bool => 1 ≤ r n ω) ≤ 1 / q + 1.2 / q ^ 2 + 2 * ϖ +
        C0 * (0.163 : ℝ) ^ (((n : ℝ) - m0 - 2) / 2) +
        prob (fun ω : Pairs n → Bool => ¬ EaccRec E m0 n ω)) := by
  classical
  have hq0 : 0 < q := by linarith
  obtain ⟨hϑ, hA⟩ := corank_numbers hq hϖ0 hϖ
  set θ1 : ℝ := q⁻¹ + ϖ with hθ1
  set κ : ℝ := 0.1 + 10 * ((q ^ 2)⁻¹ + ϖ) with hκ
  have hθ1_0 : 0 ≤ θ1 := by positivity
  have hκ0 : 0 ≤ κ := by positivity
  set ρ : ℝ := 0.163 with hρ
  set A : ℝ := θ1 ^ 2 / (1 - (θ1 + κ)) with hAdef
  have hA0 : 0 ≤ A := div_nonneg (sq_nonneg _) (by rw [hρ] at hϑ; linarith)
  set v : ℕ → ℝ := fun m => expect (fun ω : Pairs m → Bool =>
    potV (r m ω) * @ite ℝ (EaccRec E m0 m ω) (Classical.dec _) 1 0) with hv
  set a : ℕ → ℝ := fun m => prob (fun ω : Pairs m → Bool => 1 ≤ r m ω ∧ EaccRec E m0 m ω) with ha
  have hS1a : ∀ m, m0 ≤ m → m < n → ∀ ω, E m ω →
      expect (fun ξ : Fin m → Bool => potV (r (m + 1) (succPairs ω ξ))) ≤
        θ1 * @ite ℝ (r m ω = 1) (Classical.dec _) 1 0 + κ * potV (r m ω) := by
    intro m hm0 hmn ω hE
    obtain hR | hR | hR | hR : r m ω = 0 ∨ r m ω = 1 ∨ r m ω = 2 ∨ 3 ≤ r m ω := by omega
    ·
      have h0 : ∀ ξ, potV (r (m + 1) (succPairs ω ξ)) = 0 := by
        intro ξ
        have := hstep1 m ω ξ
        rw [hR] at this
        unfold potV
        rw [ite_eq_right (by omega)]
      simp only [h0, expect_const]
      rw [hR, show potV 0 = 0 by simp [potV]]
      simp
    ·
      have hb := ht1 m hm0 hmn ω hE (by omega)
      rw [hR, pow_one] at hb
      have h1 : ∀ ξ, potV (r (m + 1) (succPairs ω ξ)) ≤
          1 * @ite ℝ (1 ≤ r (m + 1) (succPairs ω ξ)) (Classical.dec _) 1 0 + 0 := by
        intro ξ
        have := hstep1 m ω ξ
        rw [hR] at this
        unfold potV
        by_cases h2 : 2 ≤ r (m + 1) (succPairs ω ξ)
        · rw [ite_eq_left h2, ite_eq_left (by omega), show r (m + 1) (succPairs ω ξ) - 2 = 0 by omega]
          simp
        · rw [ite_eq_right h2]
          split_ifs <;> norm_num
      refine (expect_le_of_le_indicator zero_le_one h1).trans ?_
      rw [hR, ite_eq_left rfl, show potV 1 = 0 by simp [potV]]
      linarith
    ·
      have hb := ht1 m hm0 hmn ω hE (by omega)
      rw [hR] at hb
      have h1 : ∀ ξ, potV (r (m + 1) (succPairs ω ξ)) ≤
          10 * @ite ℝ (2 ≤ r (m + 1) (succPairs ω ξ)) (Classical.dec _) 1 0 + 0 := by
        intro ξ
        have := hstep1 m ω ξ
        rw [hR] at this
        unfold potV
        by_cases h2 : 2 ≤ r (m + 1) (succPairs ω ξ)
        · rw [ite_eq_left h2, ite_eq_left h2]
          have h3 : r (m + 1) (succPairs ω ξ) - 2 ≤ 1 := by omega
          have : (10 : ℝ) ^ (r (m + 1) (succPairs ω ξ) - 2) ≤ 10 ^ 1 :=
            pow_le_pow_right₀ (by norm_num) h3
          linarith
        · rw [ite_eq_right h2, ite_eq_right h2]
          norm_num
      refine (expect_le_of_le_indicator (by norm_num) h1).trans ?_
      rw [hR, ite_eq_right (by norm_num), show potV 2 = 1 by simp [potV]]
      have : (10 : ℝ) * ((q ^ 2)⁻¹ + ϖ) ≤ κ := by rw [hκ]; linarith
      nlinarith
    ·
      obtain ⟨k, hk⟩ : ∃ k, r m ω = k + 3 := ⟨r m ω - 3, by omega⟩
      have hb := ht1 m hm0 hmn ω hE (by omega)
      have hVR : potV (r m ω) = (10 : ℝ) ^ (k + 1) := by
        unfold potV
        rw [ite_eq_left (by omega), show r m ω - 2 = k + 1 by omega]
      have h1 : ∀ ξ, potV (r (m + 1) (succPairs ω ξ)) ≤
          (10 : ℝ) ^ (k + 2) * @ite ℝ (r m ω ≤ r (m + 1) (succPairs ω ξ)) (Classical.dec _) 1 0 +
            (10 : ℝ) ^ k := by
        intro ξ
        have hs1 := hstep1 m ω ξ
        have hs2 := hstep2 m ω ξ
        unfold potV
        rw [ite_eq_left (by omega)]
        by_cases h2 : r m ω ≤ r (m + 1) (succPairs ω ξ)
        · rw [ite_eq_left h2]
          have : (10 : ℝ) ^ (r (m + 1) (succPairs ω ξ) - 2) ≤ 10 ^ (k + 2) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have : (0 : ℝ) ≤ 10 ^ k := by positivity
          linarith
        · rw [ite_eq_right h2, show r (m + 1) (succPairs ω ξ) - 2 = k by omega]
          simp
      refine (expect_le_of_le_indicator (by positivity) h1).trans ?_
      rw [ite_eq_right (by omega), hVR]
      have hqR : (q ^ r m ω)⁻¹ ≤ (q ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega))
      have hp1 : prob (fun ξ : Fin m → Bool => r m ω ≤ r (m + 1) (succPairs ω ξ)) ≤ (q ^ 2)⁻¹ + ϖ := by
        linarith
      have e1 : (10 : ℝ) ^ (k + 2) = 10 * 10 ^ (k + 1) := by ring
      have e2 : (10 : ℝ) ^ k * 10 = 10 ^ (k + 1) := by ring
      have h10 : (0 : ℝ) ≤ 10 ^ (k + 1) := by positivity
      rw [e1]
      nlinarith
  have hS1b : ∀ m, m0 ≤ m → m < n → ∀ ω, E m ω →
      prob (fun ξ : Fin m → Bool => 1 ≤ r (m + 1) (succPairs ω ξ)) ≤
        θ1 + @ite ℝ (2 ≤ r m ω) (Classical.dec _) 1 0 := by
    intro m hm0 hmn ω hE
    rcases Nat.lt_or_ge (r m ω) 2 with h | h
    · rw [ite_eq_right (by omega), add_zero]
      rcases Nat.eq_zero_or_pos (r m ω) with h0 | h0
      · exact ht0 m hm0 hmn ω hE h0
      · have hb := ht1 m hm0 hmn ω hE h0
        have h1 : r m ω = 1 := by omega
        rw [h1, pow_one] at hb
        simpa [h1] using hb
    · rw [ite_eq_left h]
      linarith [prob_le_one (fun ξ : Fin m → Bool => 1 ≤ r (m + 1) (succPairs ω ξ))]
  have hv_step : ∀ m, m0 ≤ m → m < n → v (m + 1) ≤ θ1 * a m + κ * v m := by
    intro m hm0 hmn
    have e1 : v (m + 1) = expect (fun ω : Pairs m → Bool => expect (fun ξ : Fin m → Bool =>
        potV (r (m + 1) (succPairs ω ξ)) *
          @ite ℝ (EaccRec E m0 (m + 1) (succPairs ω ξ)) (Classical.dec _) 1 0)) :=
      expect_succPairs _
    have hpt : ∀ ω : Pairs m → Bool, expect (fun ξ : Fin m → Bool =>
        potV (r (m + 1) (succPairs ω ξ)) *
          @ite ℝ (EaccRec E m0 (m + 1) (succPairs ω ξ)) (Classical.dec _) 1 0) ≤
        θ1 * @ite ℝ (1 ≤ r m ω ∧ EaccRec E m0 m ω) (Classical.dec _) 1 0 +
          κ * (potV (r m ω) * @ite ℝ (EaccRec E m0 m ω) (Classical.dec _) 1 0) := by
      intro ω
      by_cases hacc : EaccRec E m0 m ω ∧ E m ω
      · have hcongr : ∀ ξ, potV (r (m + 1) (succPairs ω ξ)) *
            @ite ℝ (EaccRec E m0 (m + 1) (succPairs ω ξ)) (Classical.dec _) 1 0 =
            potV (r (m + 1) (succPairs ω ξ)) := by
          intro ξ
          rw [ite_eq_left ((EaccRec_succPairs E m0 ω ξ).2 ⟨hacc.1, fun _ => hacc.2⟩), mul_one]
        simp only [hcongr]
        refine (hS1a m hm0 hmn ω hacc.2).trans ?_
        rw [ite_eq_left hacc.1, mul_one]
        gcongr
        by_cases h1 : r m ω = 1
        · rw [ite_eq_left h1, ite_eq_left ⟨by omega, hacc.1⟩]
        · rw [ite_eq_right h1]
          split_ifs <;> norm_num
      · have hcongr : ∀ ξ, potV (r (m + 1) (succPairs ω ξ)) *
            @ite ℝ (EaccRec E m0 (m + 1) (succPairs ω ξ)) (Classical.dec _) 1 0 = 0 := by
          intro ξ
          rw [ite_eq_right, mul_zero]
          rw [EaccRec_succPairs]
          exact fun h => hacc ⟨h.1, h.2 hm0⟩
        simp only [hcongr, expect_const]
        have := potV_nonneg (r m ω)
        positivity
    rw [e1]
    refine (expect_mono hpt).trans (le_of_eq ?_)
    rw [expect_add, expect_const_mul, expect_const_mul, expect_indicator']
  have ha_step : ∀ m, m0 ≤ m → m < n → a (m + 1) ≤ θ1 + v m := by
    intro m hm0 hmn
    have e1 : a (m + 1) = expect (fun ω : Pairs m → Bool => expect (fun ξ : Fin m → Bool =>
        @ite ℝ (1 ≤ r (m + 1) (succPairs ω ξ) ∧ EaccRec E m0 (m + 1) (succPairs ω ξ))
          (Classical.dec _) 1 0)) := by
      show prob (fun ω : Pairs (m + 1) → Bool => 1 ≤ r (m + 1) ω ∧ EaccRec E m0 (m + 1) ω) = _
      rw [← expect_indicator', expect_succPairs]
    have hpt : ∀ ω : Pairs m → Bool, expect (fun ξ : Fin m → Bool =>
        @ite ℝ (1 ≤ r (m + 1) (succPairs ω ξ) ∧ EaccRec E m0 (m + 1) (succPairs ω ξ))
          (Classical.dec _) 1 0) ≤
        θ1 * 1 + 1 * (potV (r m ω) * @ite ℝ (EaccRec E m0 m ω) (Classical.dec _) 1 0) := by
      intro ω
      by_cases hacc : EaccRec E m0 m ω ∧ E m ω
      · have hcongr : ∀ ξ, @ite ℝ (1 ≤ r (m + 1) (succPairs ω ξ) ∧
            EaccRec E m0 (m + 1) (succPairs ω ξ)) (Classical.dec _) 1 0 =
            @ite ℝ (1 ≤ r (m + 1) (succPairs ω ξ)) (Classical.dec _) 1 0 := by
          intro ξ
          have : EaccRec E m0 (m + 1) (succPairs ω ξ) :=
            (EaccRec_succPairs E m0 ω ξ).2 ⟨hacc.1, fun _ => hacc.2⟩
          by_cases h1 : 1 ≤ r (m + 1) (succPairs ω ξ)
          · rw [ite_eq_left ⟨h1, this⟩, ite_eq_left h1]
          · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1]
        simp only [hcongr]
        rw [expect_indicator']
        refine (hS1b m hm0 hmn ω hacc.2).trans ?_
        rw [ite_eq_left hacc.1, mul_one, mul_one, one_mul]
        have := indicator_two_le_potV (r m ω)
        have h2 : @ite ℝ (2 ≤ r m ω) (Classical.dec _) 1 0 = if 2 ≤ r m ω then (1 : ℝ) else 0 := by
          congr
        linarith
      · have hcongr : ∀ ξ, @ite ℝ (1 ≤ r (m + 1) (succPairs ω ξ) ∧
            EaccRec E m0 (m + 1) (succPairs ω ξ)) (Classical.dec _) 1 0 = 0 := by
          intro ξ
          rw [ite_eq_right]
          rw [EaccRec_succPairs]
          exact fun h => hacc ⟨h.2.1, h.2.2 hm0⟩
        simp only [hcongr, expect_const]
        have := potV_nonneg (r m ω)
        positivity
    rw [e1]
    refine (expect_mono hpt).trans (le_of_eq ?_)
    rw [expect_add, expect_const, expect_const_mul]
    simp only [mul_one, one_mul]
    rfl
  have hv_le : ∀ m, v m ≤ C0 := by
    intro m
    refine (expect_mono fun ω => ?_).trans (hC m)
    have h1 := potV_le_pow (r m ω)
    have h2 := potV_nonneg (r m ω)
    split_ifs <;> nlinarith
  have hρ0 : (0 : ℝ) < ρ := by norm_num
  have hρ1 : ρ ≤ 1 := by norm_num
  have hsol : ∀ k, m0 + k + 1 ≤ n →
      v (m0 + k) ≤ A + C0 * ρ ^ (((k : ℝ) - 1) / 2) ∧
      v (m0 + k + 1) ≤ A + C0 * ρ ^ (((k : ℝ) + 1 - 1) / 2) := by
    have hC0 : 0 ≤ C0 := le_trans (expect_nonneg fun _ => by positivity) (hC 0)
    intro k
    induction k with
    | zero =>
      intro _
      have h1 : (1 : ℝ) ≤ ρ ^ ((((0 : ℕ) : ℝ) - 1) / 2) := by
        apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ0 hρ1
        norm_num
      have h2 : ρ ^ ((((0 : ℕ) : ℝ) + 1 - 1) / 2) = 1 := by norm_num
      refine ⟨?_, ?_⟩
      · have := hv_le (m0 + 0)
        nlinarith
      · rw [h2]
        have := hv_le (m0 + 0 + 1)
        linarith
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      refine ⟨by simpa [add_assoc] using h2, ?_⟩
      have hv1 := hv_step (m0 + k + 1) (by omega) (by omega)
      have ha1 := ha_step (m0 + k) (by omega) (by omega)
      have e : m0 + (k + 1) + 1 = m0 + k + 1 + 1 := by ring
      rw [e]
      have hρk : ρ ^ (((k : ℝ) - 1) / 2) * ρ = ρ ^ ((((k + 1 : ℕ) : ℝ) + 1 - 1) / 2) := by
        rw [← Real.rpow_add_one hρ0.ne']
        congr 1
        push_cast
        ring
      have hρk' : ρ ^ ((((k : ℝ) + 1 - 1) / 2)) = ρ ^ (((k : ℝ) - 1) / 2) * ρ ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hρ0]
        congr 1
        ring
      have hsq : ρ ^ ((1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by norm_num)
      have hρpos : 0 ≤ ρ ^ (((k : ℝ) - 1) / 2) := (Real.rpow_pos_of_pos hρ0 _).le
      have hC0 : 0 ≤ C0 := le_trans (expect_nonneg fun _ => by positivity) (hC 0)
      have hfix : θ1 ^ 2 + (θ1 + κ) * A = A := by
        rw [hAdef]
        have : 1 - (θ1 + κ) ≠ 0 := by rw [hρ] at hϑ; linarith
        field_simp
        ring
      have hρ' : θ1 + κ * ρ ^ ((1 : ℝ) / 2) ≤ ρ :=
        calc θ1 + κ * ρ ^ ((1 : ℝ) / 2) ≤ θ1 + κ * 1 :=
              add_le_add_right (mul_le_mul_of_nonneg_left hsq hκ0) θ1
          _ = θ1 + κ := by rw [mul_one]
          _ ≤ ρ := hϑ
      rw [← hρk]
      rw [hρk'] at h2
      calc v (m0 + k + 1 + 1) ≤ θ1 * a (m0 + k + 1) + κ * v (m0 + k + 1) := hv1
        _ ≤ θ1 * (θ1 + v (m0 + k)) + κ * v (m0 + k + 1) := by gcongr
        _ ≤ θ1 * (θ1 + (A + C0 * ρ ^ (((k : ℝ) - 1) / 2))) +
              κ * (A + C0 * (ρ ^ (((k : ℝ) - 1) / 2) * ρ ^ ((1 : ℝ) / 2))) := by gcongr
        _ = (θ1 ^ 2 + (θ1 + κ) * A) +
              C0 * ρ ^ (((k : ℝ) - 1) / 2) * (θ1 + κ * ρ ^ ((1 : ℝ) / 2)) := by ring
        _ ≤ A + C0 * ρ ^ (((k : ℝ) - 1) / 2) * ρ := by
            rw [hfix]
            gcongr
        _ = A + C0 * (ρ ^ (((k : ℝ) - 1) / 2) * ρ) := by ring
  have hprob2 : ∀ m, prob (fun ω : Pairs m → Bool => 2 ≤ r m ω ∧ EaccRec E m0 m ω) ≤ v m := by
    intro m
    rw [← expect_indicator']
    refine expect_mono fun ω => ?_
    have h1 := indicator_two_le_potV (r m ω)
    by_cases h : 2 ≤ r m ω ∧ EaccRec E m0 m ω
    · rw [ite_eq_left h, ite_eq_left h.2, mul_one]
      rw [ite_eq_left h.1] at h1
      exact h1
    · rw [ite_eq_right h]
      have := potV_nonneg (r m ω)
      split_ifs <;> nlinarith
  have hAq : A ≤ 1.2 / q ^ 2 + ϖ := hA
  refine ⟨fun m hm0 hmn => ?_, fun hn => ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm0
    have hexp : (((m0 + k : ℕ) : ℝ) - m0 - 1) / 2 = ((k : ℝ) - 1) / 2 := by push_cast; ring
    rw [hexp]
    rcases Nat.lt_or_ge (m0 + k) n with hlt | hge
    · have := (hsol k (by omega)).1
      linarith [hprob2 (m0 + k)]
    ·
      have hk : n = m0 + k := le_antisymm hge hmn
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        have h1 : (1 : ℝ) ≤ ρ ^ ((((0 : ℕ) : ℝ) - 1) / 2) :=
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ0 hρ1 (by norm_num)
        have hC0 : 0 ≤ C0 := le_trans (expect_nonneg fun _ => by positivity) (hC 0)
        have := hv_le (m0 + 0)
        have := hprob2 (m0 + 0)
        nlinarith
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have := (hsol j (by omega)).2
        have e : m0 + (j + 1) = m0 + j + 1 := by ring
        rw [e]
        have e2 : (((j + 1 : ℕ) : ℝ) - 1) / 2 = ((j : ℝ) + 1 - 1) / 2 := by push_cast; ring
        rw [e2]
        linarith [hprob2 (m0 + j + 1)]
  ·
    obtain ⟨k, hk⟩ : ∃ k, n = m0 + k + 1 := ⟨n - m0 - 1, by omega⟩
    have h1 : prob (fun ω : Pairs n → Bool => 1 ≤ r n ω) ≤
        a n + prob (fun ω : Pairs n → Bool => ¬ EaccRec E m0 n ω) := by
      refine (prob_mono fun ω h => ?_).trans (prob_or_le _ _)
      by_cases hacc : EaccRec E m0 n ω
      · exact Or.inl ⟨h, hacc⟩
      · exact Or.inr hacc
    have h2 : a n ≤ θ1 + v (m0 + k) := by
      rw [hk]
      exact ha_step (m0 + k) (by omega) (by omega)
    have h3 := (hsol k (by omega)).1
    have hexp : ((n : ℝ) - m0 - 2) / 2 = ((k : ℝ) - 1) / 2 := by rw [hk]; push_cast; ring
    rw [hexp]
    rw [hθ1] at h2
    have : (1 : ℝ) / q = q⁻¹ := one_div q
    linarith

section Concrete

variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
theorem shiftedMat_succPairs {m : ℕ} (μ : F) (ω : Pairs m → Bool) (ξ : Fin m → Bool) :
    shiftedMat 1 (-1) μ (succPairs ω ξ) = border (shiftedMat 1 (-1) μ ω) (twoValued (1 : F) (-1) ξ) (-μ) := by
  rw [shiftedMat_succ, pairsSuccEquiv_succPairs]
  congr 1
  funext i
  simp [twoValued]

omit [Fintype F] in
theorem geomMult_succPairs {m : ℕ} (μ : F) (ω : Pairs m → Bool) (ξ : Fin m → Bool) :
    geomMult 1 (-1) μ (succPairs ω ξ) ≤ geomMult 1 (-1) μ ω + 1 ∧
    geomMult 1 (-1) μ ω ≤ geomMult 1 (-1) μ (succPairs ω ξ) + 1 ∧
    (geomMult 1 (-1) μ ω ≤ geomMult 1 (-1) μ (succPairs ω ξ) ↔
      ∀ k ∈ LinearMap.ker (shiftedMat 1 (-1) μ ω).mulVecLin, twoValued (1 : F) (-1) ξ ⬝ᵥ k = 0) := by
  unfold geomMult
  rw [shiftedMat_succPairs]
  exact lem_border_corank (shiftedMat_transpose μ ω)

theorem lem_corank (hF2 : (1 : F) ≠ -1) (hq : 23 ≤ Fintype.card F) (μ : F) {n : ℕ} (hn : 4 ≤ n)
    {ϖ : ℝ} (hϖ0 : 0 ≤ ϖ) (hϖ : ϖ ≤ 1 / 100000) (E : ∀ m, (Pairs m → Bool) → Prop)
    (hi : ∀ m, (3 * n + 3) / 4 ≤ m → m < n → ∀ ω, E m ω → geomMult 1 (-1) μ ω = 0 →
      prob (fun ξ : Fin m → Bool => geomMult 1 (-1) μ (succPairs ω ξ) = 1) ≤
        (Fintype.card F : ℝ)⁻¹ + ϖ)
    (hii : ∀ m, (3 * n + 3) / 4 ≤ m → m < n → ∀ ω, E m ω → 1 ≤ geomMult 1 (-1) μ ω →
      prob (fun ξ : Fin m → Bool => ∀ k ∈ LinearMap.ker (shiftedMat 1 (-1) μ ω).mulVecLin,
        twoValued (1 : F) (-1) ξ ⬝ᵥ k = 0) ≤ ((Fintype.card F : ℝ) ^ geomMult 1 (-1) μ ω)⁻¹ + ϖ) :
    (∀ m, (3 * n + 3) / 4 ≤ m → m ≤ n → prob (fun ω : Pairs m → Bool =>
        2 ≤ geomMult 1 (-1) μ ω ∧ EaccRec E ((3 * n + 3) / 4) m ω) ≤
        1.2 / (Fintype.card F : ℝ) ^ 2 + ϖ +
          C0 * (0.163 : ℝ) ^ (((m : ℝ) - ((3 * n + 3) / 4 : ℕ) - 1) / 2)) ∧
    prob (fun ω : Pairs n → Bool => 1 ≤ geomMult 1 (-1) μ ω) ≤
      1 / (Fintype.card F : ℝ) + 1.2 / (Fintype.card F : ℝ) ^ 2 + 2 * ϖ +
        C0 * (0.163 : ℝ) ^ (((n : ℝ) - ((3 * n + 3) / 4 : ℕ) - 2) / 2) +
        prob (fun ω : Pairs n → Bool => ¬ EaccRec E ((3 * n + 3) / 4) n ω) := by
  have hqR : (23 : ℝ) ≤ Fintype.card F := by exact_mod_cast hq
  have hab : ((1 : ℤ) : F) ≠ ((-1 : ℤ) : F) := by
    push_cast
    exact hF2
  have h := corank_potential hqR hϖ0 hϖ (fun m ω => geomMult (F := F) 1 (-1) μ ω) E
    (m0 := (3 * n + 3) / 4) (n := n)
    (fun m ω ξ => (geomMult_succPairs μ ω ξ).1) (fun m ω ξ => (geomMult_succPairs μ ω ξ).2.1)
    (fun m hm0 hmn ω hE h0 => by
      refine le_trans (le_of_eq (prob_congr fun ξ => ?_)) (hi m hm0 hmn ω hE h0)
      have := (geomMult_succPairs μ ω ξ).1
      rw [h0] at this
      constructor
      · intro h
        omega
      · intro h
        omega)
    (fun m hm0 hmn ω hE h1 => by
      refine le_trans (le_of_eq (prob_congr fun ξ => ?_)) (hii m hm0 hmn ω hE h1)
      exact (geomMult_succPairs μ ω ξ).2.2)
    (fun m => (lem_apriori hab μ m).2.2)
  exact ⟨h.1, h.2 (by omega)⟩

end Concrete

end DGS
