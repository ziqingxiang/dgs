module

public import DGS.S11_Deg1.PencilSuppU
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

@[expose] public section

open Finset

namespace DGS

def countT {m : ℕ} (d : Fin m → Bool) : ℕ := (univ.filter fun j => d j = true).card

theorem countT_cast {m : ℕ} (d : Fin m → Bool) :
    (countT d : ℝ) = ∑ j, (if d j = true then (1 : ℝ) else 0) := by
  rw [countT, ← sum_boole]

theorem prob_count_ge_le {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 ≤ a) :
    prob (fun d : Fin m → Bool => (m : ℝ) / 2 + a ≤ countT d) ≤ Real.exp (-2 * a ^ 2 / m) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set lam : ℝ := 4 * a / m with hlam
  have hlam0 : 0 ≤ lam := by positivity
  set g : Bool → ℝ := fun b => Real.exp (lam * ((if b = true then 1 else 0) - 1 / 2)) with hg
  have hprod : ∀ d : Fin m → Bool, ∏ j, g (d j) = Real.exp (lam * ((countT d : ℝ) - m / 2)) := by
    intro d
    have e : (countT d : ℝ) - m / 2 = ∑ j : Fin m, ((if d j = true then (1 : ℝ) else 0) - 1 / 2) := by
      rw [sum_sub_distrib, countT_cast, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [e, mul_sum, Real.exp_sum]
  have hind : ∀ d : Fin m → Bool, (if (m : ℝ) / 2 + a ≤ countT d then (1 : ℝ) else 0) ≤
      Real.exp (-(lam * a)) * ∏ j, g (d j) := by
    intro d
    rw [hprod, ← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp
      nlinarith
    · exact (Real.exp_pos _).le
  have hsum : ∑ d : Fin m → Bool, ∏ j, g (d j) = (2 * Real.cosh (lam / 2)) ^ m := by
    rw [← Fintype.prod_sum (fun (_ : Fin m) (b : Bool) => g b), prod_const, card_univ, Fintype.card_fin,
      Fintype.sum_bool]
    congr 1
    simp only [hg, ite_true, Bool.false_eq_true, ite_false]
    rw [Real.cosh_eq]
    ring_nf
  have hcard : (Fintype.card (Fin m → Bool) : ℝ) = 2 ^ m := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast
    ring
  calc prob (fun d : Fin m → Bool => (m : ℝ) / 2 + a ≤ countT d)
      = expect (fun d : Fin m → Bool => if (m : ℝ) / 2 + a ≤ countT d then (1 : ℝ) else 0) :=
        (expect_indicator _).symm
    _ ≤ expect (fun d : Fin m → Bool => Real.exp (-(lam * a)) * ∏ j, g (d j)) := expect_mono hind
    _ = Real.exp (-(lam * a)) * ((2 * Real.cosh (lam / 2)) ^ m / 2 ^ m) := by
        rw [expect_const_mul]
        congr 1
        unfold expect
        rw [hsum, hcard]
    _ = Real.exp (-(lam * a)) * Real.cosh (lam / 2) ^ m := by
        rw [mul_pow]
        congr 1
        field_simp
    _ ≤ Real.exp (-(lam * a)) * Real.exp ((lam / 2) ^ 2 / 2) ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) m)
          (Real.exp_pos _).le
    _ = Real.exp (-2 * a ^ 2 / m) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        rw [hlam]
        field_simp
        ring

theorem prob_count_le_le {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 ≤ a) :
    prob (fun d : Fin m → Bool => (countT d : ℝ) ≤ (m : ℝ) / 2 - a) ≤ Real.exp (-2 * a ^ 2 / m) := by
  classical
  have hneg : ∀ d : Fin m → Bool, (countT (fun j => !d j) : ℝ) = m - countT d := by
    intro d
    have h1 : countT (fun j => !d j) + countT d = m := by
      have h2 := card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (fun j => d j = true)
      rw [card_univ, Fintype.card_fin] at h2
      have e1 : countT (fun j => !d j) = (univ.filter fun j => ¬ (d j = true)).card := by
        unfold countT
        congr 1
      rw [e1, add_comm]
      exact h2
    have : ((countT (fun j => !d j) + countT d : ℕ) : ℝ) = m := by exact_mod_cast h1
    push_cast at this
    linarith
  have e : prob (fun d : Fin m → Bool => (countT d : ℝ) ≤ (m : ℝ) / 2 - a) =
      prob (fun d : Fin m → Bool => (m : ℝ) / 2 + a ≤ countT d) := by
    rw [← prob_equiv (Equiv.mk (fun d : Fin m → Bool => fun j => !d j) (fun d j => !d j)
      (fun d => by funext j; simp) (fun d => by funext j; simp))]
    refine prob_congr fun d => ?_
    simp only [Equiv.coe_fn_mk]
    rw [hneg]
    constructor <;> intro h <;> linarith
  rw [e]
  exact prob_count_ge_le hm ha

theorem prob_suppU_bad_le {m : ℕ} (hm : 0 < m) :
    prob (fun x : SignPair m => ¬ (2 * m ≤ 5 * (suppU x).card ∧ 5 * (suppU x).card ≤ 3 * m)) ≤
      2 * Real.exp (-(m : ℝ) / 50) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← prob_equiv pairDiffEquiv.symm]
  have e : ∀ y : (Fin m → Bool) × (Fin m → Bool),
      ¬ (2 * m ≤ 5 * (suppU (pairDiffEquiv.symm y)).card ∧ 5 * (suppU (pairDiffEquiv.symm y)).card ≤ 3 * m) ↔
      ¬ (2 * m ≤ 5 * countT y.2 ∧ 5 * countT y.2 ≤ 3 * m) := by
    rintro ⟨ξ, d⟩
    rw [suppU_pairDiff]
    rfl
  rw [prob_congr e, prob_snd (Ω := Fin m → Bool)
    (fun d : Fin m → Bool => ¬ (2 * m ≤ 5 * countT d ∧ 5 * countT d ≤ 3 * m))]
  have hsub : ∀ d : Fin m → Bool, ¬ (2 * m ≤ 5 * countT d ∧ 5 * countT d ≤ 3 * m) →
      (m : ℝ) / 2 + m / 10 ≤ countT d ∨ (countT d : ℝ) ≤ (m : ℝ) / 2 - m / 10 := by
    intro d h
    rw [not_and_or] at h
    rcases h with h | h
    · right
      have : 5 * countT d < 2 * m := by omega
      have h' : ((5 * countT d : ℕ) : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      linarith
    · left
      have : 3 * m < 5 * countT d := by omega
      have h' : ((3 * m : ℕ) : ℝ) < ((5 * countT d : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      linarith
  have ha : (0 : ℝ) ≤ m / 10 := by positivity
  have hexp : Real.exp (-2 * ((m : ℝ) / 10) ^ 2 / m) = Real.exp (-(m : ℝ) / 50) := by
    congr 1
    field_simp
    ring
  calc prob (fun d : Fin m → Bool => ¬ (2 * m ≤ 5 * countT d ∧ 5 * countT d ≤ 3 * m))
      ≤ prob (fun d : Fin m → Bool => (m : ℝ) / 2 + m / 10 ≤ countT d ∨
          (countT d : ℝ) ≤ (m : ℝ) / 2 - m / 10) := prob_mono hsub
    _ ≤ prob (fun d : Fin m → Bool => (m : ℝ) / 2 + m / 10 ≤ countT d) +
          prob (fun d : Fin m → Bool => (countT d : ℝ) ≤ (m : ℝ) / 2 - m / 10) := prob_or_le _ _
    _ ≤ Real.exp (-(m : ℝ) / 50) + Real.exp (-(m : ℝ) / 50) := by
        rw [← hexp]
        exact add_le_add (prob_count_ge_le hm ha) (prob_count_le_le hm ha)
    _ = 2 * Real.exp (-(m : ℝ) / 50) := by ring

end DGS
