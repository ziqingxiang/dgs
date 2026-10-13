module

public import DGS.ExtDefs
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

open Matrix Finset Polynomial

namespace DGS

section MainAngles

variable {n : ℕ}

theorem det_diagonal_sub_vecMulVec (m a : Fin n → ℝ) (hm : ∀ i, m i ≠ 0) :
    (diagonal m - vecMulVec a a).det = (∏ i, m i) * (1 - ∑ i, a i ^ 2 / m i) := by
  set u : Fin n → ℝ := fun i => -(a i / m i) with hu
  have h1 : diagonal m - vecMulVec a a = diagonal m * (1 + replicateCol Unit u * replicateRow Unit a) := by
    rw [← vecMulVec_eq, Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, sub_eq_add_neg]
    congr 1
    ext i j
    simp only [Matrix.neg_apply, vecMulVec_apply, mulVec_diagonal, hu]
    field_simp [hm i]
  rw [h1, det_mul, det_diagonal, det_one_add_replicateCol_mul_replicateRow]
  congr 1
  rw [sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  simp only [hu]
  ring

theorem sum_sq_eq_of_resolvent_eq {d a b : Fin n → ℝ}
    (h : ∀ x : ℝ, (∀ i, x + d i ≠ 0) → ∑ i, a i ^ 2 / (x + d i) = ∑ i, b i ^ 2 / (x + d i)) (lam : ℝ) :
    ∑ i ∈ univ.filter (fun i => d i = lam), a i ^ 2 = ∑ i ∈ univ.filter (fun i => d i = lam), b i ^ 2 := by
  classical
  set S : Finset ℝ := univ.image d with hS
  set γ : ℝ → ℝ := fun μ => ∑ i ∈ univ.filter (fun i => d i = μ), (a i ^ 2 - b i ^ 2) with hγ
  suffices hγ0 : γ lam = 0 by
    simp only [hγ, sum_sub_distrib] at hγ0
    linarith
  by_cases hlam : lam ∈ S
  swap
  · simp only [hγ]
    refine sum_eq_zero fun i hi => ?_
    exfalso
    exact hlam (mem_image.2 ⟨i, mem_univ _, (mem_filter.1 hi).2⟩)
  set P : ℝ[X] := ∑ μ ∈ S, C (γ μ) * ∏ ν ∈ S.erase μ, (X + C ν) with hP
  have hroot : ∀ x : ℝ, (∀ μ ∈ S, x + μ ≠ 0) → P.eval x = 0 := by
    intro x hx
    have hx' : ∀ i, x + d i ≠ 0 := fun i => hx _ (mem_image_of_mem _ (mem_univ i))
    have h1 := h x hx'
    have h2 : ∑ i, (a i ^ 2 - b i ^ 2) / (x + d i) = 0 := by
      rw [← sub_eq_zero] at h1
      rw [← h1, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => sub_div _ _ _
    have h3 : ∑ μ ∈ S, γ μ / (x + μ) = 0 := by
      rw [← h2, ← sum_fiberwise_of_maps_to (g := d) (t := S) (fun i _ => mem_image_of_mem _ (mem_univ i))]
      refine sum_congr rfl fun μ _ => ?_
      simp only [hγ, sum_div]
      refine sum_congr rfl fun i hi => ?_
      rw [(mem_filter.1 hi).2]
    have h4 : P.eval x = (∏ ν ∈ S, (x + ν)) * ∑ μ ∈ S, γ μ / (x + μ) := by
      rw [hP, eval_finsetSum, mul_sum]
      refine sum_congr rfl fun μ hμ => ?_
      rw [eval_mul, eval_C, eval_prod]
      simp only [eval_add, eval_X, eval_C]
      rw [← mul_prod_erase S (fun ν => x + ν) hμ]
      field_simp [hx μ hμ]
    rw [h4, h3, mul_zero]
  have hP0 : P = 0 := by
    refine eq_zero_of_infinite_isRoot P ?_
    have hfin : ({x : ℝ | ∃ μ ∈ S, x + μ = 0} : Set ℝ).Finite := by
      refine (S.finite_toSet.image (fun μ => -μ)).subset ?_
      rintro x ⟨μ, hμ, hxμ⟩
      exact ⟨μ, hμ, by linarith⟩
    refine (hfin.infinite_compl).mono fun x hx => ?_
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and] at hx
    exact hroot x hx
  have h5 : P.eval (-lam) = γ lam * ∏ ν ∈ S.erase lam, (-lam + ν) := by
    rw [hP, eval_finsetSum, sum_eq_single lam]
    · rw [eval_mul, eval_C, eval_prod]
      simp only [eval_add, eval_X, eval_C]
    · intro μ hμ hμlam
      rw [eval_mul, eval_prod]
      simp only [eval_add, eval_X, eval_C]
      have : ∏ ν ∈ S.erase μ, (-lam + ν) = 0 :=
        prod_eq_zero (mem_erase.2 ⟨Ne.symm hμlam, hlam⟩) (by ring)
      rw [this, mul_zero]
    · intro h'
      exact absurd hlam h'
  have h6 : ∏ ν ∈ S.erase lam, (-lam + ν) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro ν hν
    have := (mem_erase.1 hν).1
    intro h0
    apply this
    linarith
  rw [hP0, eval_zero] at h5
  exact (mul_eq_zero.1 h5.symm).resolve_right h6

end MainAngles

end DGS
