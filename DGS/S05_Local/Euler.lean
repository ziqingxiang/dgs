module

public import DGS.Core.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.MatrixPolynomialAlgebra

@[expose] public section

open Matrix Polynomial

namespace DGS

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def psiPoly (A : Matrix (Fin n) (Fin n) R) : R[X] :=
  ∑ i, ∑ j, (charmatrix A).adjugate i j

noncomputable def tauF (A : Matrix (Fin n) (Fin n) R) (g : R[X]) : R :=
  (g %ₘ A.charpoly).coeff (n - 1)

variable [Nontrivial R]

theorem adjugate_charmatrix_coeff (A : Matrix (Fin n) (Fin n) R) (hn : 1 ≤ n) (i j : Fin n) :
    ((charmatrix A).adjugate i j).natDegree ≤ n - 1 ∧
      ((charmatrix A).adjugate i j).coeff (n - 1) = if i = j then 1 else 0 := by
  have : Nontrivial (Matrix (Fin n) (Fin n) R) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  set P := matPolyEquiv (charmatrix A).adjugate with hP
  have h1 : P * (X - C A) = A.charpoly.map (algebraMap R (Matrix (Fin n) (Fin n) R)) := by
    have := congrArg matPolyEquiv (adjugate_mul (charmatrix A))
    rw [map_mul, matPolyEquiv_charmatrix] at this
    rw [hP, this]
    exact matPolyEquiv_smul_one _
  have hinj : Function.Injective (algebraMap R (Matrix (Fin n) (Fin n) R)) := by
    intro a b hab
    have := congrFun (congrFun hab ⟨0, hn⟩) ⟨0, hn⟩
    simpa [Matrix.algebraMap_matrix_apply] using this
  have hRdeg : (A.charpoly.map (algebraMap R (Matrix (Fin n) (Fin n) R))).natDegree = n := by
    rw [natDegree_map_eq_of_injective hinj, charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hRlc : (A.charpoly.map (algebraMap R (Matrix (Fin n) (Fin n) R))).leadingCoeff = 1 := by
    rw [leadingCoeff_map_of_injective hinj, (charpoly_monic A).leadingCoeff, map_one]
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    have := congrArg natDegree h1
    rw [natDegree_zero, hRdeg] at this
    omega
  have hlc : P.leadingCoeff * (X - C A).leadingCoeff ≠ 0 := by
    rw [leadingCoeff_X_sub_C, mul_one]
    exact leadingCoeff_ne_zero.2 hP0
  have hdeg : P.natDegree = n - 1 := by
    have := congrArg natDegree h1
    rw [natDegree_mul' hlc, natDegree_X_sub_C, hRdeg] at this
    omega
  have hlead : P.leadingCoeff = 1 := by
    have := congrArg leadingCoeff h1
    rw [leadingCoeff_mul' hlc, leadingCoeff_X_sub_C, mul_one, hRlc] at this
    exact this
  constructor
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    have : P.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact_mod_cast hk)
    have h2 := congrFun (congrFun this i) j
    rwa [hP, matPolyEquiv_coeff_apply] at h2
  · have h2 : P.coeff (n - 1) = 1 := by rw [← hdeg]; exact hlead
    have h3 := congrFun (congrFun h2 i) j
    rw [hP, matPolyEquiv_coeff_apply] at h3
    rw [h3, Matrix.one_apply]

omit [Nontrivial R] in
theorem exists_charmatrix_mul_pow (A : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    ∃ S : Matrix (Fin n) (Fin n) R[X], (X : R[X]) ^ k • (1 : Matrix (Fin n) (Fin n) R[X]) -
      (A ^ k).map C = charmatrix A * S := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨S, hS⟩ := ih
    refine ⟨(X : R[X]) • S + (A ^ k).map C, ?_⟩
    have hch : charmatrix A = (X : R[X]) • (1 : Matrix (Fin n) (Fin n) R[X]) - A.map C := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    have hmap : (A ^ (k + 1)).map C = A.map C * (A ^ k).map C := by
      rw [pow_succ', Matrix.map_mul]
    rw [mul_add, Matrix.mul_smul, ← hS, hmap, hch]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_smul, ← pow_succ']
    abel

omit [Nontrivial R] in
theorem exists_charmatrix_mul (A : Matrix (Fin n) (Fin n) R) (h : R[X]) :
    ∃ S : Matrix (Fin n) (Fin n) R[X], h • (1 : Matrix (Fin n) (Fin n) R[X]) -
      (aeval A h).map C = charmatrix A * S := by
  induction h using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨S, hS⟩ := hp
    obtain ⟨S', hS'⟩ := hq
    refine ⟨S + S', ?_⟩
    rw [mul_add, ← hS, ← hS', add_smul, map_add, Matrix.map_add _ (fun a b => map_add C a b)]
    abel
  | monomial k a =>
    obtain ⟨S, hS⟩ := exists_charmatrix_mul_pow A k
    refine ⟨a • S, ?_⟩
    have h1 : (monomial k a : R[X]) = C a * X ^ k := by rw [C_mul_X_pow_eq_monomial]
    have h2 : aeval A (monomial k a) = a • A ^ k := by
      rw [aeval_monomial, Algebra.smul_def]
    rw [h2, Matrix.mul_smul, ← hS, h1]
    ext i j : 1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.one_apply,
      Polynomial.smul_eq_C_mul, map_mul]
    split_ifs <;> ring

theorem ones_dot_aeval_eq_tauF (A : Matrix (Fin n) (Fin n) R) (hn : 1 ≤ n) (h : R[X]) :
    ones n R ⬝ᵥ (aeval A h *ᵥ ones n R) = tauF A (h * psiPoly A) := by
  obtain ⟨S, hS⟩ := exists_charmatrix_mul A h
  have h1 : h • (charmatrix A).adjugate - (charmatrix A).adjugate * (aeval A h).map C =
      A.charpoly • S := by
    have : (charmatrix A).adjugate * (h • (1 : Matrix (Fin n) (Fin n) R[X]) - (aeval A h).map C) =
        A.charpoly • S := by
      rw [hS, ← Matrix.mul_assoc, adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      rfl
    rw [← this, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  set T : R[X] := ∑ i, ∑ j, ((charmatrix A).adjugate * (aeval A h).map C) i j with hT
  have h2 : h * psiPoly A - T = A.charpoly * ∑ i, ∑ j, S i j := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) R[X] => ∑ i, ∑ j, M i j) h1
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_sub_distrib] at this
    rw [psiPoly, hT, Finset.mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum]
    exact this
  have hdegT : T.natDegree ≤ n - 1 := by
    refine (natDegree_sum_le_of_forall_le _ _ fun i _ => ?_)
    refine (natDegree_sum_le_of_forall_le _ _ fun j _ => ?_)
    rw [Matrix.mul_apply]
    refine (natDegree_sum_le_of_forall_le _ _ fun k _ => ?_)
    refine natDegree_mul_le.trans ?_
    rw [Matrix.map_apply, natDegree_C, add_zero]
    exact (adjugate_charmatrix_coeff A hn i k).1
  have hmod : (h * psiPoly A) %ₘ A.charpoly = T := by
    rw [modByMonic_eq_of_dvd_sub (charpoly_monic A) ⟨_, h2⟩, (modByMonic_eq_self_iff (charpoly_monic A)).2]
    rw [degree_eq_natDegree (charpoly_monic A).ne_zero, charpoly_natDegree_eq_dim, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_le_of_natDegree_le hdegT) ?_
    exact_mod_cast (by omega : n - 1 < n)
  rw [tauF, hmod, hT, finsetSum_coeff]
  simp only [finsetSum_coeff, Matrix.mul_apply, Matrix.map_apply, coeff_mul_C]
  simp only [(adjugate_charmatrix_coeff A hn _ _).2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp [dotProduct, mulVec, ones]

theorem lem_form (A : Matrix (Fin n) (Fin n) R) (hA : A.IsSymm) (hn : 1 ≤ n) (f g : R[X]) :
    (aeval A f *ᵥ ones n R) ⬝ᵥ (aeval A g *ᵥ ones n R) = tauF A (f * g * psiPoly A) := by
  have hsym : (aeval A f)ᵀ = aeval A f := by
    rw [aeval_eq_sum_range, Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.transpose_smul, Matrix.transpose_pow, hA.eq]
  calc (aeval A f *ᵥ ones n R) ⬝ᵥ (aeval A g *ᵥ ones n R)
      = ones n R ⬝ᵥ (aeval A f *ᵥ (aeval A g *ᵥ ones n R)) := by
        rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
    _ = ones n R ⬝ᵥ (aeval A (f * g) *ᵥ ones n R) := by rw [mulVec_mulVec, map_mul]
    _ = tauF A (f * g * psiPoly A) := ones_dot_aeval_eq_tauF A hn (f * g)

end DGS
