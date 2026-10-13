module

public import DGS.S11_Deg1.Ptrue

@[expose] public section

open Finset Matrix Polynomial Filter Topology
open scoped Real

namespace DGS

section OnePair

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

def EvPT (b0 b1 : ZMod p) (ω : Pairs m → Bool) (x : SignPair m) : Prop :=
  IsUnit (QAm b0 b1 (modP p (seidelOf ω))).det ∧ ∃ a0 a1 : ZMod p, (a0 ≠ 0 ∨ a1 ≠ 0) ∧
    (muMin (fun j : {j // uPair p x j = 0} =>
      ((PAm a0 a1 (modP p (seidelOf ω)) * (QAm b0 b1 (modP p (seidelOf ω)))⁻¹) *ᵥ uPair p x) j) : ℝ) ≤
        cPT * m * (p : ℝ) ^ 2

theorem prob_EvPT_le (hV : Real.exp 200 ≤ (ptV m : ℝ)) (hm : 100000 ≤ m) (hp23 : 23 ≤ p)
    (hpX : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (hPS : prob (fun ω : Pairs m → Bool => ¬ GoodPS m ω) ≤ Real.exp (-(m : ℝ))) (b0 b1 : ZMod p) :
    prob (fun y : (Pairs m → Bool) × SignPair m => EvPT b0 b1 y.1 y.2) ≤
      2 * Real.exp (-(m : ℝ) / 50) + Real.exp (-(m : ℝ)) + (p : ℝ) ^ 2 * Real.exp (-(m : ℝ) / 30) +
        Real.exp (-(m : ℝ) / 2) := by
  classical
  have hm0 : 0 < m := by omega
  set adm : SignPair m → Prop :=
    fun x => 2 * m ≤ 5 * (suppU x).card ∧ 5 * (suppU x).card ≤ 3 * m with hadm
  set Small : (Pairs m → Bool) → SignPair m → Prop := fun ω x =>
    2 * m ≤ 5 * (suppU x).card ∧ 5 * (suppU x).card ≤ 3 * m ∧
      ∃ a0 a1 : ZMod p, (a0 ≠ 0 ∨ a1 ≠ 0) ∧ 100 * (univ.filter fun j => uPair p x j = 0 ∧
        ((PAm a0 a1 (modP p (seidelOf ω)) * (QAm b0 b1 (modP p (seidelOf ω)))⁻¹) *ᵥ uPair p x) j ≠ 0).card
          < m with hSmall
  have hsub : ∀ y : (Pairs m → Bool) × SignPair m, EvPT b0 b1 y.1 y.2 →
      ¬ adm y.2 ∨ (¬ GoodPS m y.1 ∨ ((GoodPS m y.1 ∧ IsUnit (QAm b0 b1 (modP p (seidelOf y.1))).det ∧
        Small y.1 y.2) ∨ (adm y.2 ∧ PsiEv b0 b1 (suppU y.2) (uPair p y.2) (cPT * m * (p : ℝ) ^ 2) y.1))) := by
    rintro ⟨ω, x⟩ ⟨hQ, a0, a1, ha, hmu⟩
    by_cases hx : adm x
    · right
      by_cases hG : GoodPS m ω
      · right
        by_cases hsm : 100 * (univ.filter fun j => uPair p x j = 0 ∧
            ((PAm a0 a1 (modP p (seidelOf ω)) * (QAm b0 b1 (modP p (seidelOf ω)))⁻¹) *ᵥ uPair p x) j ≠ 0).card
              < m
        · left
          exact ⟨hG, hQ, hx.1, hx.2, a0, a1, ha, hsm⟩
        · right
          exact ⟨hx, psiEv_of_short hQ ha x hmu hsm⟩
      · left
        exact hG
    · left
      exact hx
  have h1 : prob (fun y : (Pairs m → Bool) × SignPair m => ¬ adm y.2) ≤ 2 * Real.exp (-(m : ℝ) / 50) := by
    rw [prob_snd (Ω := Pairs m → Bool) (fun x => ¬ adm x)]
    exact prob_suppU_bad_le hm0
  have h2 : prob (fun y : (Pairs m → Bool) × SignPair m => ¬ GoodPS m y.1) ≤ Real.exp (-(m : ℝ)) := by
    rw [prob_fst (Ω' := SignPair m) (fun ω => ¬ GoodPS m ω)]
    exact hPS
  have h3 : prob (fun y : (Pairs m → Bool) × SignPair m => GoodPS m y.1 ∧
      IsUnit (QAm b0 b1 (modP p (seidelOf y.1))).det ∧ Small y.1 y.2) ≤
      (p : ℝ) ^ 2 * Real.exp (-(m : ℝ) / 30) := by
    refine prob_le_of_forall_fst (fun ω => ?_) (by positivity)
    by_cases hω : GoodPS m ω ∧ IsUnit (QAm b0 b1 (modP p (seidelOf ω))).det
    · exact (prob_mono fun x hx => hx.2.2).trans (lem_pencilsupp_supp hω.1 hp23 hpX hω.2)
    · rw [prob_congr (Q := fun _ => False) fun x => ⟨fun h => hω ⟨h.1, h.2.1⟩, False.elim⟩, prob_false]
      positivity
  have h4 : prob (fun y : (Pairs m → Bool) × SignPair m =>
      adm y.2 ∧ PsiEv b0 b1 (suppU y.2) (uPair p y.2) (cPT * m * (p : ℝ) ^ 2) y.1) ≤
      Real.exp (-(m : ℝ) / 2) := by
    refine prob_le_of_forall_snd (fun x => ?_) (by positivity)
    by_cases hx : adm x
    · exact (prob_mono fun ω hω => hω.2).trans (psi_le hV hm hp23 hpX b0 b1 (suppU x) hx.2 (uPair p x))
    · rw [prob_congr (Q := fun _ => False) fun ω => ⟨fun h => hx h.1, False.elim⟩, prob_false]
      positivity
  calc prob (fun y : (Pairs m → Bool) × SignPair m => EvPT b0 b1 y.1 y.2)
      ≤ prob (fun y : (Pairs m → Bool) × SignPair m => ¬ adm y.2 ∨ (¬ GoodPS m y.1 ∨
          ((GoodPS m y.1 ∧ IsUnit (QAm b0 b1 (modP p (seidelOf y.1))).det ∧ Small y.1 y.2) ∨
            (adm y.2 ∧ PsiEv b0 b1 (suppU y.2) (uPair p y.2) (cPT * m * (p : ℝ) ^ 2) y.1)))) :=
        prob_mono hsub
    _ ≤ _ := (prob_or_le _ _).trans (add_le_add le_rfl ((prob_or_le _ _).trans
          (add_le_add le_rfl (prob_or_le _ _))))
    _ ≤ 2 * Real.exp (-(m : ℝ) / 50) + (Real.exp (-(m : ℝ)) + ((p : ℝ) ^ 2 * Real.exp (-(m : ℝ) / 30) +
          Real.exp (-(m : ℝ) / 2))) := add_le_add h1 (add_le_add h2 (add_le_add h3 h4))
    _ = _ := by ring

theorem expect_prob_eq {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (P : Ω × Ω' → Prop) :
    expect (fun ω => prob (fun ω' => P (ω, ω'))) = prob P := by
  rw [prob_prod_eq_avg P]
  rfl

theorem prob_bad_p_le (hV : Real.exp 200 ≤ (ptV m : ℝ)) (hm : 100000 ≤ m) (hp23 : 23 ≤ p)
    (hpX : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (hPS : prob (fun ω : Pairs m → Bool => ¬ GoodPS m ω) ≤ Real.exp (-(m : ℝ))) :
    prob (fun ω : Pairs m → Bool => ∃ b : ZMod p × ZMod p,
      Real.exp (-(m : ℝ) / 100) < prob (fun x : SignPair m => EvPT b.1 b.2 ω x)) ≤
      (p : ℝ) ^ 2 * ((2 * Real.exp (-(m : ℝ) / 50) + Real.exp (-(m : ℝ)) +
        (p : ℝ) ^ 2 * Real.exp (-(m : ℝ) / 30) + Real.exp (-(m : ℝ) / 2)) / Real.exp (-(m : ℝ) / 100)) := by
  classical
  set B : ℝ := (2 * Real.exp (-(m : ℝ) / 50) + Real.exp (-(m : ℝ)) +
    (p : ℝ) ^ 2 * Real.exp (-(m : ℝ) / 30) + Real.exp (-(m : ℝ) / 2)) / Real.exp (-(m : ℝ) / 100) with hB
  have hb : ∀ b : ZMod p × ZMod p, prob (fun ω : Pairs m → Bool =>
      Real.exp (-(m : ℝ) / 100) < prob (fun x : SignPair m => EvPT b.1 b.2 ω x)) ≤ B := by
    intro b
    refine (prob_mono fun ω h => le_of_lt h).trans ?_
    refine (prob_ge_le_expect_div _ (fun ω => prob_nonneg _) (Real.exp_pos _)).trans ?_
    rw [expect_prob_eq (fun y : (Pairs m → Bool) × SignPair m => EvPT b.1 b.2 y.1 y.2)]
    exact div_le_div_of_nonneg_right (prob_EvPT_le hV hm hp23 hpX hPS b.1 b.2) (Real.exp_pos _).le
  calc prob (fun ω : Pairs m → Bool => ∃ b : ZMod p × ZMod p,
        Real.exp (-(m : ℝ) / 100) < prob (fun x : SignPair m => EvPT b.1 b.2 ω x))
      ≤ ∑ b : ZMod p × ZMod p, prob (fun ω : Pairs m → Bool =>
          Real.exp (-(m : ℝ) / 100) < prob (fun x : SignPair m => EvPT b.1 b.2 ω x)) :=
        prob_exists_le_sum_fintype _
    _ ≤ ∑ _b : ZMod p × ZMod p, B := sum_le_sum fun b _ => hb b
    _ = (p : ℝ) ^ 2 * B := by
        rw [sum_const, card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
        push_cast
        ring

end OnePair

theorem goodPT_of {m : ℕ} (hcm : 1 ≤ cPT * m) {ω : Pairs m → Bool}
    (h : ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) →
      ∀ b0 b1 : ZMod p, prob (fun x : SignPair m => EvPT b0 b1 ω x) ≤ Real.exp (-(m : ℝ) / 100)) :
    GoodPT (seidelOf ω) := by
  intro p _ hp23 hpX Q P hQm hQd hQdet hP0 hPd
  have hp2 : p ≠ 2 := by omega
  set A := modP p (seidelOf ω) with hA
  have hQ' : aeval A Q = QAm (Q.coeff 0) (Q.coeff 1) A := aeval_monic_two A hQm hQd
  have hP' : aeval A P = PAm (P.coeff 0) (P.coeff 1) A := aeval_deg_le_one A hPd
  have ha := coeff_ne_zero_of_ne_zero hPd hP0
  rw [hQ'] at hQdet
  rw [hP', hQ']
  set B := PAm (P.coeff 0) (P.coeff 1) A * (QAm (Q.coeff 0) (Q.coeff 1) A)⁻¹ with hBdef
  have hB : B.IsSymm := isSymm_PQinv _ _ _ _ (modP_seidel_isSymm ω) hQdet
  have hprob : prob (fun x : SignPair m =>
      (muMin (fun j : {j // uPair p x j = 0} => (B *ᵥ uPair p x) j) : ℝ) ≤ cPT * m * (p : ℝ) ^ 2) ≤
      Real.exp (-(m : ℝ) / 100) :=
    (prob_mono fun x hx => ⟨hQdet, P.coeff 0, P.coeff 1, ha, hx⟩).trans
      (h p hp23 hpX (Q.coeff 0) (Q.coeff 1))
  have hsq := lem_squaring_bound hp2 B hB one_ne_zero cPT_pos (cPT_le.trans (by norm_num)) hprob
  have e : Real.exp (-(cPT * m) / 2) ^ 2 = Real.exp (-(cPT * m)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have h2 : 2 * Real.exp (-2 * cPT * m) ≤ Real.exp (-(cPT * m)) := by
    have h3 : (2 : ℝ) ≤ Real.exp (cPT * m) := by
      have := Real.add_one_le_exp (cPT * m)
      linarith
    calc 2 * Real.exp (-2 * cPT * m) ≤ Real.exp (cPT * m) * Real.exp (-2 * cPT * m) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = Real.exp (-(cPT * m)) := by rw [← Real.exp_add]; ring_nf
  have h4 : ‖quadSum B 1‖ ^ 2 ≤ Real.exp (-(cPT * m) / 2) ^ 2 := by rw [e]; exact hsq.trans h2
  have h5 := norm_nonneg (quadSum B 1)
  have h6 := Real.exp_pos (-(cPT * m) / 2)
  nlinarith

theorem ptrue_numeric {m : ℕ} {X : ℝ} (hX1 : 1 ≤ X) (hXm : Real.log X ≤ m / 4000) (hm : 100000 ≤ m) :
    (X + 1) * (X ^ 2 * ((2 * Real.exp (-(m : ℝ) / 50) + Real.exp (-(m : ℝ)) + X ^ 2 * Real.exp (-(m : ℝ) / 30) +
      Real.exp (-(m : ℝ) / 2)) / Real.exp (-(m : ℝ) / 100))) ≤ Real.exp (-(m : ℝ) / 200) := by
  have hmR : (100000 : ℝ) ≤ m := by exact_mod_cast hm
  have hX0 : 0 < X := by linarith
  have hXe : X ≤ Real.exp (m / 4000) := by
    rw [← Real.exp_log hX0]
    exact Real.exp_le_exp.2 hXm
  have e1 : Real.exp (-(m : ℝ)) ≤ Real.exp (-(m : ℝ) / 50) := Real.exp_le_exp.2 (by linarith)
  have e2 : Real.exp (-(m : ℝ) / 30) ≤ Real.exp (-(m : ℝ) / 50) := Real.exp_le_exp.2 (by linarith)
  have e3 : Real.exp (-(m : ℝ) / 2) ≤ Real.exp (-(m : ℝ) / 50) := Real.exp_le_exp.2 (by linarith)
  have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX1
  have hbr : 2 * Real.exp (-(m : ℝ) / 50) + Real.exp (-(m : ℝ)) + X ^ 2 * Real.exp (-(m : ℝ) / 30) +
      Real.exp (-(m : ℝ) / 2) ≤ 5 * X ^ 2 * Real.exp (-(m : ℝ) / 50) := by
    have h50 := Real.exp_pos (-(m : ℝ) / 50)
    have : X ^ 2 * Real.exp (-(m : ℝ) / 30) ≤ X ^ 2 * Real.exp (-(m : ℝ) / 50) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    nlinarith
  have hdiv : Real.exp (-(m : ℝ) / 50) / Real.exp (-(m : ℝ) / 100) = Real.exp (-(m : ℝ) / 100) := by
    rw [← Real.exp_sub]
    ring_nf
  have hX5 : X ^ 5 ≤ Real.exp (5 * (m / 4000)) := by
    calc X ^ 5 ≤ Real.exp (m / 4000) ^ 5 := pow_le_pow_left₀ hX0.le hXe 5
      _ = Real.exp (5 * (m / 4000)) := by rw [← Real.exp_nat_mul]; norm_num
  have h10 : (10 : ℝ) ≤ Real.exp (3 * (m : ℝ) / 800) := by
    have := Real.add_one_le_exp (3 * (m : ℝ) / 800)
    linarith
  calc (X + 1) * (X ^ 2 * ((2 * Real.exp (-(m : ℝ) / 50) + Real.exp (-(m : ℝ)) +
        X ^ 2 * Real.exp (-(m : ℝ) / 30) + Real.exp (-(m : ℝ) / 2)) / Real.exp (-(m : ℝ) / 100)))
      ≤ (2 * X) * (X ^ 2 * (5 * X ^ 2 * Real.exp (-(m : ℝ) / 50) / Real.exp (-(m : ℝ) / 100))) := by
        gcongr
        linarith
    _ = 10 * X ^ 5 * (Real.exp (-(m : ℝ) / 50) / Real.exp (-(m : ℝ) / 100)) := by ring
    _ = 10 * X ^ 5 * Real.exp (-(m : ℝ) / 100) := by rw [hdiv]
    _ ≤ Real.exp (3 * (m : ℝ) / 800) * Real.exp (5 * (m / 4000)) * Real.exp (-(m : ℝ) / 100) := by
        gcongr
    _ = Real.exp (-(m : ℝ) / 200) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf

theorem prop_Ptrue :
    ∀ᶠ m : ℕ in atTop, probSeidel m (fun T => ¬ GoodPT T) ≤ Real.exp (-(m : ℝ) / 200) := by
  have hV : ∀ᶠ m : ℕ in atTop, Real.exp 200 ≤ (ptV m : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp tendsto_ptV).eventually_ge_atTop _
  have hc : ∀ᶠ m : ℕ in atTop, 1 ≤ cPT * m := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1 / cPT)] with m hm
    have := cPT_pos
    rw [div_le_iff₀ this] at hm
    linarith
  filter_upwards [lem_pencilsupp, hV, hc, eventually_ge_atTop 100000] with m hPS hVm hcm hm
  classical
  set X : ℝ := Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) with hX
  set PS := (range (⌊X⌋₊ + 1)).filter (fun p => p.Prime ∧ 23 ≤ p) with hPSdef
  let Bad : ℕ → (Pairs m → Bool) → Prop := fun p ω => ∃ hF : Fact p.Prime, ∃ b : ZMod p × ZMod p,
    Real.exp (-(m : ℝ) / 100) < prob (fun x : SignPair m => @EvPT p hF m b.1 b.2 ω x)
  have hsub : ∀ ω : Pairs m → Bool, ¬ GoodPT (seidelOf ω) → ∃ p ∈ PS, Bad p ω := by
    intro ω hω
    by_contra hno
    push Not at hno
    apply hω
    refine goodPT_of hcm fun p hF hp23 hpX b0 b1 => ?_
    have hp : p ∈ PS := by
      rw [hPSdef, mem_filter, mem_range]
      refine ⟨?_, hF.out, hp23⟩
      have : p ≤ ⌊X⌋₊ := Nat.le_floor hpX
      omega
    have h1 := hno p hp
    simp only [Bad, not_exists, not_lt] at h1
    exact h1 hF (b0, b1)
  set Bnd : ℝ := X ^ 2 * ((2 * Real.exp (-(m : ℝ) / 50) + Real.exp (-(m : ℝ)) +
    X ^ 2 * Real.exp (-(m : ℝ) / 30) + Real.exp (-(m : ℝ) / 2)) / Real.exp (-(m : ℝ) / 100)) with hBnd
  have hbad : ∀ p ∈ PS, prob (Bad p) ≤ Bnd := by
    intro p hp
    rw [hPSdef, mem_filter, mem_range] at hp
    have : Fact p.Prime := ⟨hp.2.1⟩
    have hpX : (p : ℝ) ≤ X := by
      have h1 : p ≤ ⌊X⌋₊ := by omega
      exact (Nat.le_floor_iff (Real.exp_pos _).le).1 h1
    have h1 : prob (Bad p) ≤ prob (fun ω : Pairs m → Bool => ∃ b : ZMod p × ZMod p,
        Real.exp (-(m : ℝ) / 100) < prob (fun x : SignPair m => EvPT b.1 b.2 ω x)) :=
      prob_mono fun ω ⟨_, h⟩ => h
    refine h1.trans ((prob_bad_p_le hVm hm hp.2.2 hpX hPS).trans ?_)
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    have hp2 : (p : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hp0 hpX 2
    rw [hBnd]
    gcongr
  have hcard : (PS.card : ℝ) ≤ X + 1 := by
    have h1 : PS.card ≤ ⌊X⌋₊ + 1 := (card_filter_le _ _).trans (card_range _).le
    have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le (Real.exp_pos _).le
    have h3 : (PS.card : ℝ) ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  have hX1 : 1 ≤ X := Real.one_le_exp (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hXm : Real.log X ≤ m / 4000 := by
    rw [hX, Real.log_exp]
    have hV3 : 3 ≤ ptV m := by
      have he : (3 : ℝ) ≤ Real.exp 200 := by have := Real.add_one_le_exp (200 : ℝ); linarith
      have h' : (3 : ℝ) ≤ (ptV m : ℝ) := he.trans hVm
      exact_mod_cast h'
    have h1 : (m : ℝ) ^ ((1 : ℝ) / 8) ≤ 2 * (ptV m : ℝ) ^ 2 := by
      have := log_le_ptV (m := m) (p := 1) hV3 (by norm_num) (by
        rw [Nat.cast_one]
        exact Real.one_le_exp (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have h2 : (m : ℝ) ^ ((1 : ℝ) / 8) = ((m : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
        norm_num
      have h3 := rpow_lt_ptV_add_one m
      have h0 : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_nonneg (Nat.cast_nonneg m) _
      have hV' : (3 : ℝ) ≤ ptV m := by exact_mod_cast hV3
      rw [h2]
      nlinarith
    have h4 : 8000 * (ptV m : ℝ) ^ 2 ≤ m := by
      have h5 : ((ptV m ^ 16 : ℕ) : ℝ) ≤ m := by exact_mod_cast ptV_pow_le m
      push_cast at h5
      have he : (8000 : ℝ) ≤ Real.exp 200 := by
        have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 200)
        norm_num at this
        linarith
      have h6 : (8000 : ℝ) ≤ (ptV m : ℝ) := he.trans hVm
      have h7 : (ptV m : ℝ) ^ 2 * 8000 ≤ (ptV m : ℝ) ^ 2 * (ptV m : ℝ) ^ 14 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc (8000 : ℝ) ≤ (ptV m : ℝ) := h6
          _ ≤ (ptV m : ℝ) ^ 14 := by
              have : (1 : ℝ) ≤ ptV m := by linarith
              exact le_self_pow₀ this (by norm_num)
      have e : (ptV m : ℝ) ^ 2 * (ptV m : ℝ) ^ 14 = (ptV m : ℝ) ^ 16 := by ring
      linarith
    linarith
  have hnum := ptrue_numeric hX1 hXm hm
  have hBnd0 : 0 ≤ Bnd := by positivity
  calc probSeidel m (fun T => ¬ GoodPT T)
      = prob (fun ω : Pairs m → Bool => ¬ GoodPT (seidelOf ω)) := rfl
    _ ≤ prob (fun ω : Pairs m → Bool => ∃ p ∈ PS, Bad p ω) := prob_mono hsub
    _ ≤ ∑ p ∈ PS, prob (Bad p) := prob_exists_le_sum _ _
    _ ≤ ∑ _p ∈ PS, Bnd := sum_le_sum hbad
    _ = PS.card * Bnd := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (X + 1) * Bnd := by gcongr
    _ ≤ Real.exp (-(m : ℝ) / 200) := hnum

theorem thm_rankp :
    ∀ᶠ n : ℕ in atTop, ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p →
      (p : ℝ) ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 9)) → ∀ μ : ZMod p,
        prob (fun ω : Pairs n → Bool => 2 ≤ geomMult 1 (-1) μ ω) ≤
          1.2 / (p : ℝ) ^ 2 + Real.exp (-cRK * n) ∧
        prob (fun ω : Pairs n → Bool => 1 ≤ geomMult 1 (-1) μ ω) ≤
          1 / p + 1.2 / (p : ℝ) ^ 2 + Real.exp (-cRK * n) :=
  thm_rankp_of prop_Ptrue

theorem prop_isocond :
    ∀ᶠ n : ℕ in atTop, ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p →
      (p : ℝ) ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 9)) →
        ∑ μ : ZMod p, prob (fun ω : Pairs n → Bool => (X - C μ) ^ 2 ∣ (modP p (seidelOf ω)).charpoly) ≤
          3.5 / p + Real.exp (-cRK * n) :=
  prop_isocond_of prop_Ptrue

theorem prop_deg1 {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    Tendsto (fun n : ℕ => probG n (fun G => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ) ∧ (p : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧ E p 1 G))
      atTop (𝓝 0) :=
  prop_deg1_of prop_Ptrue hε0 hε

end DGS
