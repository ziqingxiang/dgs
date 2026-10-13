module

public import DGS.S11_Deg1.PtNum
public import DGS.S11_Deg1.PtHoeff

@[expose] public section

open Finset Matrix Polynomial
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

theorem aeval_monic_two (A : Matrix (Fin m) (Fin m) (ZMod p)) {Q : (ZMod p)[X]} (hQm : Q.Monic)
    (hQd : Q.natDegree = 2) : aeval A Q = QAm (Q.coeff 0) (Q.coeff 1) A := by
  conv_lhs => rw [hQm.as_sum, hQd]
  simp only [map_add, map_pow, aeval_X, map_mul, aeval_C, sum_range_succ, sum_range_zero,
    zero_add, pow_zero, pow_one, mul_one, Algebra.algebraMap_eq_smul_one, QAm, smul_mul_assoc, one_mul]
  rw [sq]
  abel

theorem aeval_deg_le_one (A : Matrix (Fin m) (Fin m) (ZMod p)) {P : (ZMod p)[X]} (hPd : P.natDegree ≤ 1) :
    aeval A P = PAm (P.coeff 0) (P.coeff 1) A := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hPd]
  simp only [map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, PAm, smul_mul_assoc,
    one_mul]

theorem coeff_ne_zero_of_ne_zero {P : (ZMod p)[X]} (hPd : P.natDegree ≤ 1) (hP0 : P ≠ 0) :
    P.coeff 0 ≠ 0 ∨ P.coeff 1 ≠ 0 := by
  by_contra h
  push Not at h
  apply hP0
  rw [eq_X_add_C_of_natDegree_le_one hPd, h.1, h.2]
  simp

omit [Fact (Nat.Prime p)] in
theorem modP_seidel_isSymm (ω : Pairs m → Bool) : (modP p (seidelOf ω)).IsSymm := by
  have h : (seidelOf ω).IsSymm := Matrix.IsSymm.ext fun i j => symOf_comm _ _ _ j i
  unfold modP
  rw [Matrix.IsSymm, ← Matrix.transpose_map, h.eq]

theorem QAm_transpose (b0 b1 : ZMod p) (A : Matrix (Fin m) (Fin m) (ZMod p)) (hA : A.IsSymm) :
    (QAm b0 b1 A)ᵀ = QAm b0 b1 A := by
  unfold QAm
  rw [transpose_add, transpose_add, transpose_mul, transpose_smul, transpose_smul, transpose_one, hA.eq]

theorem PAm_transpose (a0 a1 : ZMod p) (A : Matrix (Fin m) (Fin m) (ZMod p)) (hA : A.IsSymm) :
    (PAm a0 a1 A)ᵀ = PAm a0 a1 A := by
  unfold PAm
  rw [transpose_add, transpose_smul, transpose_smul, transpose_one, hA.eq]

theorem PAm_mul_QAm_inv (b0 b1 a0 a1 : ZMod p) (A : Matrix (Fin m) (Fin m) (ZMod p))
    (hQ : IsUnit (QAm b0 b1 A).det) :
    (QAm b0 b1 A)⁻¹ * PAm a0 a1 A = PAm a0 a1 A * (QAm b0 b1 A)⁻¹ := by
  have hc := (commute_QAm_PAm b0 b1 a0 a1 A).eq
  calc (QAm b0 b1 A)⁻¹ * PAm a0 a1 A = (QAm b0 b1 A)⁻¹ * PAm a0 a1 A * (QAm b0 b1 A * (QAm b0 b1 A)⁻¹) := by
        rw [mul_nonsing_inv _ hQ, mul_one]
    _ = (QAm b0 b1 A)⁻¹ * (QAm b0 b1 A * PAm a0 a1 A) * (QAm b0 b1 A)⁻¹ := by
        rw [hc]; simp only [Matrix.mul_assoc]
    _ = PAm a0 a1 A * (QAm b0 b1 A)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hQ, Matrix.one_mul]

theorem isSymm_PQinv (b0 b1 a0 a1 : ZMod p) {A : Matrix (Fin m) (Fin m) (ZMod p)} (hA : A.IsSymm)
    (hQ : IsUnit (QAm b0 b1 A).det) : (PAm a0 a1 A * (QAm b0 b1 A)⁻¹).IsSymm := by
  rw [Matrix.IsSymm, transpose_mul, transpose_nonsing_inv, QAm_transpose b0 b1 A hA,
    PAm_transpose a0 a1 A hA, PAm_mul_QAm_inv b0 b1 a0 a1 A hQ]

def PsiEv (b0 b1 : ZMod p) (U : Finset (Fin m)) (u : Fin m → ZMod p) (R2 : ℝ) (ω : Pairs m → Bool) : Prop :=
  ∃ ℓ : Fin 2 → ZMod p, ℓ ≠ 0 ∧ ∃ w : Fin m → Fin 2 → ZMod p,
    pairSys ω b0 b1 u w ∧ m ≤ 100 * (univ.filter fun j => j ∉ U ∧ ℓ ⬝ᵥ w j ≠ 0).card ∧
    (normSqLift (fun j : {j // j ∉ U} => ℓ ⬝ᵥ w j) : ℝ) ≤ R2

omit [Fact (Nat.Prime p)] in
theorem normSqLift_congr_subtype {P P' : Fin m → Prop} [DecidablePred P] [DecidablePred P']
    (h : ∀ j, P j ↔ P' j) (f : Fin m → ZMod p) :
    normSqLift (fun j : {j // P j} => f j) = normSqLift (fun j : {j // P' j} => f j) := by
  unfold normSqLift
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight h) _ _ fun j => rfl

theorem psiEv_of_short {ω : Pairs m → Bool} {b0 b1 a0 a1 : ZMod p}
    (hQ : IsUnit (QAm b0 b1 (modP p (seidelOf ω))).det) (ha : a0 ≠ 0 ∨ a1 ≠ 0) (x : SignPair m) {R2 : ℝ}
    (hshort : (muMin (fun j : {j // uPair p x j = 0} =>
      ((PAm a0 a1 (modP p (seidelOf ω)) * (QAm b0 b1 (modP p (seidelOf ω)))⁻¹) *ᵥ uPair p x) j) : ℝ) ≤ R2)
    (hbig : ¬ 100 * (univ.filter fun j => uPair p x j = 0 ∧
      ((PAm a0 a1 (modP p (seidelOf ω)) * (QAm b0 b1 (modP p (seidelOf ω)))⁻¹) *ᵥ uPair p x) j ≠ 0).card < m) :
    PsiEv b0 b1 (suppU x) (uPair p x) R2 ω := by
  classical
  set A := modP p (seidelOf ω) with hA
  set Qm := QAm b0 b1 A with hQm
  set C := PAm a0 a1 A * Qm⁻¹ with hC
  set u := uPair p x with hu
  set v := Qm⁻¹ *ᵥ u with hv
  set v' := A *ᵥ v with hv'
  obtain ⟨c, hc0, hc⟩ := exists_muMin_eq (fun j : {j // uPair p x j = 0} => (C *ᵥ u) j)
  set w : Fin m → Fin 2 → ZMod p := fun j => ![v j, v' j] with hw
  set ℓ : Fin 2 → ZMod p := ![c * a0, c * a1] with hℓ
  have hQv : Qm *ᵥ v = u := by rw [hv, mulVec_mulVec, mul_nonsing_inv _ hQ, one_mulVec]
  have hCu : C *ᵥ u = a1 • v' + a0 • v := by
    rw [hC, ← mulVec_mulVec, ← hv, PAm, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
  have hℓw : ∀ j, ℓ ⬝ᵥ w j = c * (C *ᵥ u) j := by
    intro j
    rw [hCu, dot_two]
    simp only [hℓ, hw, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hTv : ∀ (f : Fin m → ZMod p) (i : Fin m), ∑ j, ((seidelOf ω i j : ℤ) : ZMod p) * f j = (A *ᵥ f) i := by
    intro f i
    simp [hA, modP, mulVec, dotProduct]
  refine ⟨ℓ, ?_, w, ?_, ?_, ?_⟩
  ·
    intro h0
    have h1 : c * a0 = 0 := by have := congrFun h0 0; simpa [hℓ] using this
    have h2 : c * a1 = 0 := by have := congrFun h0 1; simpa [hℓ] using this
    rcases ha with ha | ha
    · exact ha ((mul_eq_zero.1 h1).resolve_left hc0)
    · exact ha ((mul_eq_zero.1 h2).resolve_left hc0)
  ·
    intro i
    have h1 : (A * A) *ᵥ v = u - b1 • v' - b0 • v := by
      have h2 : Qm *ᵥ v = (A * A) *ᵥ v + b1 • (A *ᵥ v) + b0 • v := by
        rw [hQm, QAm, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
      rw [hQv] at h2
      rw [h2, hv']
      abel
    have hAv' : A *ᵥ v' = (A * A) *ᵥ v := by rw [hv', mulVec_mulVec]
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
    fin_cases t
    · change ∑ j, ((seidelOf ω i j : ℤ) : ZMod p) * v j = v' i
      rw [hTv v i]
    · change ∑ j, ((seidelOf ω i j : ℤ) : ZMod p) * v' j = u i - b1 * v' i - b0 * v i
      rw [hTv v' i, hAv', h1]
      simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ·
    push Not at hbig
    have hset : (univ.filter fun j => uPair p x j = 0 ∧ (C *ᵥ u) j ≠ 0) =
        univ.filter fun j => j ∉ suppU x ∧ ℓ ⬝ᵥ w j ≠ 0 := by
      ext j
      rw [mem_filter, mem_filter, uPair_eq_zero_iff_not_mem, hℓw j]
      simp [hc0]
    rw [← hset]
    exact hbig
  ·
    have e1 : normSqLift (fun j : {j // j ∉ suppU x} => ℓ ⬝ᵥ w j) =
        normSqLift (fun j : {j // uPair p x j = 0} => c * (C *ᵥ u) j) := by
      rw [normSqLift_congr_subtype (P' := fun j => uPair p x j = 0)
        (fun j => (uPair_eq_zero_iff_not_mem x j).symm) (fun j => ℓ ⬝ᵥ w j)]
      unfold normSqLift
      exact Finset.sum_congr rfl fun j _ => by
        show (ℓ ⬝ᵥ w (j : Fin m)).valMinAbs ^ 2 = (c * (C *ᵥ u) (j : Fin m)).valMinAbs ^ 2
        rw [hℓw j]
    rw [e1, ← hc]
    exact hshort

end DGS
