module

public import DGS.S12_Deg2.SEdBlocks

@[expose] public section

open Finset Matrix Module
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

theorem clsSd_eq_one_iff (g : Fin (n + 1) → ZMod p) : clsSd g = 1 ↔ g 0 ≠ 0 := by
  unfold clsSd
  split_ifs with h1 h2
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩

omit [Fact (Nat.Prime p)] in
theorem prod_wtSd_eq (σ : ℝ) (w : Fin m → Fin (n + 1) → ZMod p) :
    ∏ j, wtSd σ (w j) = Real.exp (-σ * (normSqLift (fun j => w j 0) : ℝ)) := by
  rw [normSqLift]
  push_cast
  rw [mul_sum, Real.exp_sum]
  rfl

theorem prob_krySys_short_le {l s k : ℕ} (hn : 1 ≤ n) (H : BDHyp p (n + 1) l s) (hsk : s ≤ k) (hk : 0 < k)
    (hm40 : 40 ≤ m) {σ : ℝ} (hσ : 0 < σ) (R2 : ℝ) (b : Fin (n + 1) → ZMod p)
    (hMB : ∀ q, m ≤ 20 * q → m / 40 ≤ (k - s) * (q / k))
    {A : ℕ} (hA : 1 < 2 ^ A * ((1 + 1 / 100) / (p : ℝ) ^ (n + 1)))
    (hγ : gam0 l s ≤ 0.02) (hβ : gam0 l s + 1.21 * muP p σ / p ≤ 1) :
    prob (fun ω : Pairs m → Bool => ∃ w : Fin m → Fin (n + 1) → ZMod p, krySys ω b w ∧
        m ≤ 20 * (univ.filter fun j => w j 0 ≠ 0).card ∧ (normSqLift (fun j => w j 0) : ℝ) ≤ R2) ≤
      Real.exp (σ * R2) * (((p : ℝ) ^ n * (1 + muP p σ)) ^ m *
          ((1 + 1 / 100) / (p : ℝ) ^ (n + 1)) ^ (m - k) +
        3 ^ m * (A * (2 ^ m * ((p : ℝ) ^ (n + 1)) ^ (3 * k + s * (m / k)) * 1.23 ^ m *
          (gam0 l s + 1.21 * muP p σ / p) ^ (m / 40)))) := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hμ := muP_pos (p := p) σ
  set r0 : ℝ := (1 + 1 / 100) / (p : ℝ) ^ (n + 1) with hr0
  set β := gam0 l s + 1.21 * muP p σ / p with hβdef
  have hβ0 : 0 ≤ β := by
    have : 0 ≤ gam0 l s := by unfold gam0; positivity
    positivity
  set LB : ℝ := A * (2 ^ m * ((p : ℝ) ^ (n + 1)) ^ (3 * k + s * (m / k)) * 1.23 ^ m * β ^ (m / 40)) with hLB
  have hLB0 : 0 ≤ LB := by positivity
  set W : ℝ := ((p : ℝ) ^ n * (1 + muP p σ)) ^ m with hW
  set big : (Fin m → Fin (n + 1) → ZMod p) → Prop :=
    fun w => m ≤ 20 * (univ.filter fun j => w j 0 ≠ 0).card with hbigdef
  set short : (Fin m → Fin (n + 1) → ZMod p) → Prop :=
    fun w => (normSqLift (fun j => w j 0) : ℝ) ≤ R2 with hshort
  set F : (Fin m → Fin (n + 1) → ZMod p) → ℝ := fun w =>
    Real.exp (σ * R2) * (if big w then prob (fun ω : Pairs m → Bool => krySys ω b w) else 0) with hF
  have hF0 : ∀ w, 0 ≤ F w := fun w => by
    simp only [hF]
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (prob_nonneg _)
    · rw [mul_zero]
  have h1 : prob (fun ω : Pairs m → Bool => ∃ w : Fin m → Fin (n + 1) → ZMod p,
      krySys ω b w ∧ big w ∧ short w) ≤
      ∑ w : Fin m → Fin (n + 1) → ZMod p, (∏ j, wtSd σ (w j)) * F w := by
    refine (prob_exists_le_sum_fintype _).trans ?_
    refine sum_le_sum fun w _ => ?_
    by_cases hw : big w ∧ short w
    · have hwt : 1 ≤ Real.exp (σ * R2) * ∏ j, wtSd σ (w j) := by
        rw [prod_wtSd_eq, ← Real.exp_add]
        apply Real.one_le_exp
        have := hw.2
        simp only [hshort] at this
        nlinarith
      have hP := prob_nonneg (fun ω : Pairs m → Bool => krySys ω b w)
      calc prob (fun ω : Pairs m → Bool => krySys ω b w ∧ big w ∧ short w)
          ≤ prob (fun ω : Pairs m → Bool => krySys ω b w) := prob_mono fun ω h => h.1
        _ ≤ (Real.exp (σ * R2) * ∏ j, wtSd σ (w j)) *
              prob (fun ω : Pairs m → Bool => krySys ω b w) := le_mul_of_one_le_left hP hwt
        _ = (∏ j, wtSd σ (w j)) * F w := by
            simp only [hF, ite_eq_left hw.1]
            ring
    · rw [prob_congr (Q := fun _ => False) fun ω => ⟨fun h => hw h.2, False.elim⟩, prob_false]
      exact mul_nonneg (prod_nonneg fun j _ => wtSd_nonneg _ _) (hF0 w)
  have hpat : ∀ cls : Fin m → Fin 3, ∃ Hf : (Fin m → Fin (n + 1) → ZMod p) → ℝ, (∀ w, 0 ≤ Hf w) ∧
      (m ≤ 20 * (DSd cls 0).card → ∀ w, prob (fun ω : Pairs m → Bool => krySys ω b w) ≤ Hf w) ∧
      (∏ j, massSd p n σ (cls j)) * pexp (fun j => lawSd σ (cls j)) Hf ≤
        (∏ j, massSd p n σ (cls j)) * r0 ^ (m - k) +
          (if m ≤ 20 * (DSd cls 0).card then LB else 0) := by
    intro cls
    by_cases hbig : m ≤ 20 * (DSd cls 0).card
    · obtain ⟨Hf, h1, h2, h3⟩ := pattern_bound_d hn H hsk hk hm40 hσ b cls hbig hMB hA hγ hβ
      exact ⟨Hf, h1, fun _ => h2, by rw [ite_eq_left hbig]; exact h3⟩
    · refine ⟨fun _ => 0, fun _ => le_rfl, fun h => absurd h hbig, ?_⟩
      rw [ite_eq_right hbig, add_zero]
      have h0 : pexp (fun j => lawSd (p := p) (n := n) σ (cls j)) (fun _ => (0 : ℝ)) = 0 := by
        unfold pexp
        simp
      rw [h0, mul_zero]
      exact mul_nonneg (prod_nonneg fun j _ => (massSd_pos hn σ _).le) (by positivity)
  choose Hf hHf0 hHfsys hHfp using hpat
  have hH : ∀ (cls : Fin m → Fin 3) (w : Fin m → Fin (n + 1) → ZMod p), (∀ j, clsSd (w j) = cls j) →
      F w ≤ Real.exp (σ * R2) * Hf cls w := by
    intro cls w hw
    simp only [hF]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    split_ifs with hbw
    · have hset : (univ.filter fun j => w j 0 ≠ 0) = DSd cls 0 := by
        ext j
        rw [mem_filter, mem_DSd, ← clsSd_eq_one_iff, hw j]
        simp [bcSd]
      have hbc : m ≤ 20 * (DSd cls 0).card := by
        have := hbw
        simp only [hbigdef] at this
        rwa [hset] at this
      exact hHfsys cls hbc w
    · exact hHf0 cls w
  have h2 := sum_wtSd_le hn σ F hF0 (fun cls w => Real.exp (σ * R2) * Hf cls w) hH
  have h3 : ∑ cls : Fin m → Fin 3, (∏ j, massSd p n σ (cls j)) *
      pexp (fun j => lawSd σ (cls j)) (fun w => Real.exp (σ * R2) * Hf cls w) ≤
      Real.exp (σ * R2) * (W * r0 ^ (m - k) + 3 ^ m * LB) := by
    simp_rw [pexp_const_mul]
    calc ∑ cls : Fin m → Fin 3, (∏ j, massSd p n σ (cls j)) *
          (Real.exp (σ * R2) * pexp (fun j => lawSd σ (cls j)) (Hf cls))
        = Real.exp (σ * R2) * ∑ cls : Fin m → Fin 3, (∏ j, massSd p n σ (cls j)) *
            pexp (fun j => lawSd σ (cls j)) (Hf cls) := by
          rw [mul_sum]
          exact sum_congr rfl fun cls _ => by ring
      _ ≤ Real.exp (σ * R2) * ∑ cls : Fin m → Fin 3, ((∏ j, massSd p n σ (cls j)) *
            r0 ^ (m - k) + LB) := by
          gcongr with cls
          refine (hHfp cls).trans (add_le_add le_rfl ?_)
          split_ifs
          · exact le_rfl
          · exact hLB0
      _ = Real.exp (σ * R2) * (W * r0 ^ (m - k) + 3 ^ m * LB) := by
          rw [sum_add_distrib, ← sum_mul, sum_prod_massSd, sum_const, card_univ, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hbs : ∀ ω : Pairs m → Bool, (∃ w : Fin m → Fin (n + 1) → ZMod p, krySys ω b w ∧
      m ≤ 20 * (univ.filter fun j => w j 0 ≠ 0).card ∧ (normSqLift (fun j => w j 0) : ℝ) ≤ R2) ↔
      (∃ w : Fin m → Fin (n + 1) → ZMod p, krySys ω b w ∧ big w ∧ short w) :=
    fun ω => Iff.rfl
  rw [prob_congr hbs]
  exact h1.trans (h2.trans h3)

end DGS
