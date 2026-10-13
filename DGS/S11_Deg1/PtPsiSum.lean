module

public import DGS.S11_Deg1.PtPsi

@[expose] public section

open Finset Matrix Module
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

theorem clsG_eq_one_iff (ℓ g : Fin 2 → ZMod p) : clsG ℓ g = 1 ↔ ℓ ⬝ᵥ g ≠ 0 := by
  unfold clsG
  split_ifs with h1 h2
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩

theorem prod_wtB_eq (σ : ℝ) (ℓ : Fin 2 → ZMod p) (U : Finset (Fin m)) (w : Fin m → Fin 2 → ZMod p) :
    ∏ j, wtB σ (decide (j ∈ U)) ℓ (w j) =
      Real.exp (-σ * (normSqLift (fun j : {j // j ∉ U} => ℓ ⬝ᵥ w j) : ℝ)) := by
  classical
  rw [normSqLift]
  push_cast
  rw [mul_sum, Real.exp_sum]
  have e : ∀ j, wtB σ (decide (j ∈ U)) ℓ (w j) =
      if j ∈ U then 1 else gaussW σ (ℓ ⬝ᵥ w j).valMinAbs := by
    intro j
    unfold wtB
    by_cases hj : j ∈ U <;> simp [hj]
  simp_rw [e]
  rw [prod_ite, prod_const_one, one_mul,
    prod_subtype (univ.filter fun j => j ∉ U) (p := fun j => j ∉ U) (by simp)
      (fun j => gaussW σ (ℓ ⬝ᵥ w j).valMinAbs)]
  rfl

theorem prob_Psi_le {l s k : ℕ} (H : BDHyp p 2 l s) (hsk : s ≤ k) (hk : 0 < k) (hkm : k ≤ m)
    (hm200 : 200 ≤ m) {σ : ℝ} (hσ : 0 < σ) (R2 : ℝ) (U : Finset (Fin m)) (b0 b1 : ZMod p)
    (u : Fin m → ZMod p) (hMB : ∀ n, m ≤ 100 * n → m / 200 ≤ (k - s) * (n / k))
    {A : ℕ} (hA : 1 < 2 ^ A * ((1 + 1 / 100) / (p : ℝ) ^ 2))
    (hγ : gam0 l s ≤ 0.02) (hβ : gam0 l s + 1.21 * muP p σ / p ≤ 1) :
    prob (fun ω : Pairs m → Bool => ∃ ℓ : Fin 2 → ZMod p, ℓ ≠ 0 ∧ ∃ w : Fin m → Fin 2 → ZMod p,
        pairSys ω b0 b1 u w ∧ m ≤ 100 * (univ.filter fun j => j ∉ U ∧ ℓ ⬝ᵥ w j ≠ 0).card ∧
        (normSqLift (fun j : {j // j ∉ U} => ℓ ⬝ᵥ w j) : ℝ) ≤ R2) ≤
      (p : ℝ) ^ 2 * (Real.exp (σ * R2) *
        ((∏ j : Fin m, (if j ∈ U then (p : ℝ) ^ 2 else p * (1 + muP p σ))) *
          ((1 + 1 / 100) / (p : ℝ) ^ 2) ^ (m - k) +
        3 ^ m * (A * (2 ^ m * ((p : ℝ) ^ 2) ^ (4 * k + s * (m / k)) * 1.23 ^ m *
          (gam0 l s + 1.21 * muP p σ / p) ^ (m / 200))))) := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hμ := muP_pos (p := p) σ
  set r0 : ℝ := (1 + 1 / 100) / (p : ℝ) ^ 2 with hr0
  set β := gam0 l s + 1.21 * muP p σ / p with hβdef
  have hβ0 : 0 ≤ β := by
    have : 0 ≤ gam0 l s := by unfold gam0; positivity
    positivity
  set LB : ℝ := A * (2 ^ m * ((p : ℝ) ^ 2) ^ (4 * k + s * (m / k)) * 1.23 ^ m * β ^ (m / 200)) with hLB
  have hLB0 : 0 ≤ LB := by positivity
  set W : ℝ := ∏ j : Fin m, (if j ∈ U then (p : ℝ) ^ 2 else p * (1 + muP p σ)) with hW
  have hW0 : 0 ≤ W := prod_nonneg fun j _ => by split_ifs <;> positivity
  set Bnd : ℝ := Real.exp (σ * R2) * (W * r0 ^ (m - k) + 3 ^ m * LB) with hBnd
  have hBnd0 : 0 ≤ Bnd := by positivity
  have hℓbound : ∀ ℓ : Fin 2 → ZMod p, prob (fun ω : Pairs m → Bool => ℓ ≠ 0 ∧
      ∃ w : Fin m → Fin 2 → ZMod p, pairSys ω b0 b1 u w ∧
        m ≤ 100 * (univ.filter fun j => j ∉ U ∧ ℓ ⬝ᵥ w j ≠ 0).card ∧
        (normSqLift (fun j : {j // j ∉ U} => ℓ ⬝ᵥ w j) : ℝ) ≤ R2) ≤ Bnd := by
    intro ℓ
    by_cases hℓ : ℓ = 0
    · rw [prob_congr (Q := fun _ => False) fun ω => ⟨fun h => h.1 hℓ, False.elim⟩, prob_false]
      exact hBnd0
    set big : (Fin m → Fin 2 → ZMod p) → Prop :=
      fun w => m ≤ 100 * (univ.filter fun j => j ∉ U ∧ ℓ ⬝ᵥ w j ≠ 0).card with hbigdef
    set short : (Fin m → Fin 2 → ZMod p) → Prop :=
      fun w => (normSqLift (fun j : {j // j ∉ U} => ℓ ⬝ᵥ w j) : ℝ) ≤ R2 with hshort
    set F : (Fin m → Fin 2 → ZMod p) → ℝ := fun w =>
      Real.exp (σ * R2) * (if big w then prob (fun ω : Pairs m → Bool => pairSys ω b0 b1 u w) else 0)
      with hF
    have hF0 : ∀ w, 0 ≤ F w := fun w => by
      simp only [hF]
      split_ifs
      · exact mul_nonneg (Real.exp_pos _).le (prob_nonneg _)
      · rw [mul_zero]
    have h1 : prob (fun ω : Pairs m → Bool => ℓ ≠ 0 ∧ ∃ w : Fin m → Fin 2 → ZMod p,
        pairSys ω b0 b1 u w ∧ big w ∧ short w) ≤
        ∑ w : Fin m → Fin 2 → ZMod p, (∏ j, wtB σ (decide (j ∈ U)) ℓ (w j)) * F w := by
      refine (prob_mono fun ω h => h.2).trans ((prob_exists_le_sum_fintype _).trans ?_)
      refine sum_le_sum fun w _ => ?_
      by_cases hw : big w ∧ short w
      · have hwt : 1 ≤ Real.exp (σ * R2) * ∏ j, wtB σ (decide (j ∈ U)) ℓ (w j) := by
          rw [prod_wtB_eq, ← Real.exp_add]
          apply Real.one_le_exp
          have := hw.2
          simp only [hshort] at this
          nlinarith
        have hP := prob_nonneg (fun ω : Pairs m → Bool => pairSys ω b0 b1 u w)
        calc prob (fun ω : Pairs m → Bool => pairSys ω b0 b1 u w ∧ big w ∧ short w)
            ≤ prob (fun ω : Pairs m → Bool => pairSys ω b0 b1 u w) := prob_mono fun ω h => h.1
          _ ≤ (Real.exp (σ * R2) * ∏ j, wtB σ (decide (j ∈ U)) ℓ (w j)) *
                prob (fun ω : Pairs m → Bool => pairSys ω b0 b1 u w) := le_mul_of_one_le_left hP hwt
          _ = (∏ j, wtB σ (decide (j ∈ U)) ℓ (w j)) * F w := by
              simp only [hF, ite_eq_left hw.1]
              ring
      · rw [prob_congr (Q := fun _ => False) fun ω => ⟨fun h => hw h.2, False.elim⟩, prob_false]
        exact mul_nonneg (prod_nonneg fun j _ => wtB_nonneg _ _ _ _) (hF0 w)
    have hpat : ∀ cls : Fin m → Fin 3, ∃ Hf : (Fin m → Fin 2 → ZMod p) → ℝ, (∀ w, 0 ≤ Hf w) ∧
        (m ≤ 100 * (Dcls U cls 1).card →
          ∀ w, prob (fun ω : Pairs m → Bool => pairSys ω b0 b1 u w) ≤ Hf w) ∧
        (∏ j, massOf p σ (cls j) (decide (j ∈ U))) *
          pexp (fun j => lawOf σ ℓ (cls j) (decide (j ∈ U))) Hf ≤
          (∏ j, massOf p σ (cls j) (decide (j ∈ U))) * r0 ^ (m - k) +
            (if m ≤ 100 * (Dcls U cls 1).card then LB else 0) := by
      intro cls
      by_cases hbig : m ≤ 100 * (Dcls U cls 1).card
      · obtain ⟨Hf, h1, h2, h3⟩ := pattern_bound H hsk hk hkm hm200 hσ ℓ hℓ U b0 b1 u cls hbig hMB hA hγ hβ
        exact ⟨Hf, h1, fun _ => h2, by rw [ite_eq_left hbig]; exact h3⟩
      · refine ⟨fun _ => 0, fun _ => le_rfl, fun h => absurd h hbig, ?_⟩
        rw [ite_eq_right hbig, add_zero]
        have h0 : pexp (fun j => lawOf σ ℓ (cls j) (decide (j ∈ U))) (fun _ => (0 : ℝ)) = 0 := by
          unfold pexp
          simp
        rw [h0, mul_zero]
        exact mul_nonneg (prod_nonneg fun j _ => (massOf_pos σ _ _).le) (by positivity)
    choose Hf hHf0 hHfsys hHfp using hpat
    have hH : ∀ (cls : Fin m → Fin 3) (w : Fin m → Fin 2 → ZMod p), (∀ j, clsG ℓ (w j) = cls j) →
        F w ≤ Real.exp (σ * R2) * Hf cls w := by
      intro cls w hw
      simp only [hF]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      split_ifs with hbw
      · have hset : (univ.filter fun j => j ∉ U ∧ ℓ ⬝ᵥ w j ≠ 0) = Dcls U cls 1 := by
          ext j
          rw [mem_filter, mem_Dcls_one, ← clsG_eq_one_iff, hw j]
          simp
        have hbc : m ≤ 100 * (Dcls U cls 1).card := by
          have := hbw
          simp only [hbigdef] at this
          rwa [hset] at this
        exact hHfsys cls hbc w
      · exact hHf0 cls w
    have h2 := sum_wt_le σ ℓ U F hF0 (fun cls w => Real.exp (σ * R2) * Hf cls w) hH
    have h3 : ∑ cls : Fin m → Fin 3, (∏ j, massOf p σ (cls j) (decide (j ∈ U))) *
        pexp (fun j => lawOf σ ℓ (cls j) (decide (j ∈ U))) (fun w => Real.exp (σ * R2) * Hf cls w) ≤
        Bnd := by
      simp_rw [pexp_const_mul]
      have hsum : ∑ cls : Fin m → Fin 3, (∏ j, massOf p σ (cls j) (decide (j ∈ U))) =
          W := by
        rw [sum_prod_massOf]
        refine prod_congr rfl fun j _ => ?_
        rw [sum_massOf]
        by_cases hj : j ∈ U <;> simp [hj]
      calc ∑ cls : Fin m → Fin 3, (∏ j, massOf p σ (cls j) (decide (j ∈ U))) *
            (Real.exp (σ * R2) * pexp (fun j => lawOf σ ℓ (cls j) (decide (j ∈ U))) (Hf cls))
          = Real.exp (σ * R2) * ∑ cls : Fin m → Fin 3, (∏ j, massOf p σ (cls j) (decide (j ∈ U))) *
              pexp (fun j => lawOf σ ℓ (cls j) (decide (j ∈ U))) (Hf cls) := by
            rw [mul_sum]
            exact sum_congr rfl fun cls _ => by ring
        _ ≤ Real.exp (σ * R2) * ∑ cls : Fin m → Fin 3, ((∏ j, massOf p σ (cls j) (decide (j ∈ U))) *
              r0 ^ (m - k) + LB) := by
            gcongr with cls
            refine (hHfp cls).trans (add_le_add le_rfl ?_)
            split_ifs
            · exact le_rfl
            · exact hLB0
        _ = Bnd := by
            rw [sum_add_distrib, ← sum_mul, hsum, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin, nsmul_eq_mul, hBnd]
            push_cast
            ring
    have hbs : ∀ ω : Pairs m → Bool, (ℓ ≠ 0 ∧ ∃ w : Fin m → Fin 2 → ZMod p, pairSys ω b0 b1 u w ∧
        m ≤ 100 * (univ.filter fun j => j ∉ U ∧ ℓ ⬝ᵥ w j ≠ 0).card ∧
        (normSqLift (fun j : {j // j ∉ U} => ℓ ⬝ᵥ w j) : ℝ) ≤ R2) ↔
        (ℓ ≠ 0 ∧ ∃ w : Fin m → Fin 2 → ZMod p, pairSys ω b0 b1 u w ∧ big w ∧ short w) :=
      fun ω => Iff.rfl
    rw [prob_congr hbs]
    exact h1.trans (h2.trans h3)
  calc prob (fun ω : Pairs m → Bool => ∃ ℓ : Fin 2 → ZMod p, ℓ ≠ 0 ∧ ∃ w : Fin m → Fin 2 → ZMod p,
        pairSys ω b0 b1 u w ∧ m ≤ 100 * (univ.filter fun j => j ∉ U ∧ ℓ ⬝ᵥ w j ≠ 0).card ∧
        (normSqLift (fun j : {j // j ∉ U} => ℓ ⬝ᵥ w j) : ℝ) ≤ R2)
      ≤ ∑ ℓ : Fin 2 → ZMod p, prob (fun ω : Pairs m → Bool => ℓ ≠ 0 ∧
          ∃ w : Fin m → Fin 2 → ZMod p, pairSys ω b0 b1 u w ∧
            m ≤ 100 * (univ.filter fun j => j ∉ U ∧ ℓ ⬝ᵥ w j ≠ 0).card ∧
            (normSqLift (fun j : {j // j ∉ U} => ℓ ⬝ᵥ w j) : ℝ) ≤ R2) :=
        prob_exists_le_sum_fintype _
    _ ≤ ∑ _ℓ : Fin 2 → ZMod p, Bnd := sum_le_sum fun ℓ _ => hℓbound ℓ
    _ = (p : ℝ) ^ 2 * Bnd := by
        rw [sum_const, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end DGS
