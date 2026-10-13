module

public import DGS.S10_Tools.Squaring
public import DGS.S03_Prelim.Border

@[expose] public section

open Matrix Polynomial

namespace DGS

noncomputable def cPT : ℝ := Real.exp (-1500)

theorem cPT_pos : 0 < cPT := Real.exp_pos _

theorem cPT_le : cPT ≤ 1 / 100000 := by
  unfold cPT
  have h1 : Real.exp (-1500) ≤ Real.exp (-17) := Real.exp_le_exp.2 (by norm_num)
  have h2 : (100000 : ℝ) ≤ Real.exp 17 := by
    have h3 : Real.exp 17 = Real.exp 1 ^ 17 := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    rw [h3]
    calc (100000 : ℝ) ≤ 2 ^ 17 := by norm_num
      _ ≤ Real.exp 1 ^ 17 := pow_le_pow_left₀ (by norm_num) h4 17
  have h5 : Real.exp (-17) = (Real.exp 17)⁻¹ := Real.exp_neg 17
  calc Real.exp (-1500) ≤ Real.exp (-17) := h1
    _ = (Real.exp 17)⁻¹ := h5
    _ ≤ (100000 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
    _ = 1 / 100000 := by norm_num

def GoodPT {m : ℕ} (T : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) →
    ∀ Q P : (ZMod p)[X], Q.Monic → Q.natDegree = 2 → IsUnit (aeval (modP p T) Q).det →
      P ≠ 0 → P.natDegree ≤ 1 →
        ‖quadSum (aeval (modP p T) P * (aeval (modP p T) Q)⁻¹) 1‖ ≤ Real.exp (-(cPT * m) / 2)

section Resolvent

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

theorem quadSum_smul (B : Matrix (Fin m) (Fin m) (ZMod p)) (t : ZMod p) :
    quadSum (t • B) 1 = quadSum B t := by
  unfold quadSum
  congr 1
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, one_mul]

theorem quadSum_add_smul (B B' : Matrix (Fin m) (Fin m) (ZMod p)) (t t' : ZMod p) :
    quadSum (t • B + t' • B') 1 = ((2 : ℂ) ^ m)⁻¹ * ∑ ξ : Fin m → Bool,
      ZMod.stdAddChar (t * (sgnP p ξ ⬝ᵥ (B *ᵥ sgnP p ξ)) + t' * (sgnP p ξ ⬝ᵥ (B' *ᵥ sgnP p ξ))) := by
  unfold quadSum
  congr 1
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, one_mul]

theorem aeval_X_sub_C (A : Matrix (Fin m) (Fin m) (ZMod p)) (μ : ZMod p) :
    aeval A (X - C μ) = A - μ • 1 := by
  rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

theorem quadSum_pencil_le {T : Matrix (Fin m) (Fin m) ℤ} (hT : GoodPT T) (hp23 : 23 ≤ p)
    (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) (μ : ZMod p)
    (hdet : IsUnit (modP p T - μ • 1).det) {t1 t2 : ZMod p} (ht : t1 ≠ 0 ∨ t2 ≠ 0) :
    ‖quadSum (t1 • (modP p T - μ • 1)⁻¹ + t2 • ((modP p T - μ • 1)⁻¹ * (modP p T - μ • 1)⁻¹)) 1‖ ≤
      Real.exp (-(cPT * m) / 2) := by
  set L := modP p T - μ • 1 with hL
  set Q : (ZMod p)[X] := (X - C μ) ^ 2 with hQ
  set P : (ZMod p)[X] := C t1 * (X - C μ) + C t2 with hP
  have hQm : Q.Monic := (monic_X_sub_C μ).pow 2
  have hQd : Q.natDegree = 2 := by rw [hQ, natDegree_pow, natDegree_X_sub_C]
  have hQL : aeval (modP p T) Q = L * L := by rw [hQ, map_pow, aeval_X_sub_C, sq]
  have hPL : aeval (modP p T) P = t1 • L + t2 • 1 := by
    rw [hP, map_add, map_mul, aeval_C, aeval_C, aeval_X_sub_C, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_one_mul]
  have hQdet : IsUnit (aeval (modP p T) Q).det := by
    rw [hQL, det_mul]
    exact hdet.mul hdet
  have hP0 : P ≠ 0 := by
    intro h0
    have h2 : t2 = 0 := by
      have := congrArg (Polynomial.eval μ) h0
      simpa [hP] using this
    rw [hP, h2, C_0, add_zero] at h0
    have h1 : C t1 = 0 := (mul_eq_zero.1 h0).resolve_right (X_sub_C_ne_zero μ)
    rw [C_eq_zero] at h1
    rcases ht with ht | ht
    · exact ht h1
    · exact ht h2
  have hPd : P.natDegree ≤ 1 := by
    rw [hP]
    refine (natDegree_add_le _ _).trans (max_le ?_ (by rw [natDegree_C]; omega))
    exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_sub_C])
  have h := hT p hp23 hpm Q P hQm hQd hQdet hP0 hPd
  have hLinv : L * L⁻¹ = 1 := mul_nonsing_inv L hdet
  have e : aeval (modP p T) P * (aeval (modP p T) Q)⁻¹ = t1 • L⁻¹ + t2 • (L⁻¹ * L⁻¹) := by
    rw [hPL, hQL, Matrix.mul_inv_rev, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← mul_assoc, hLinv,
      one_mul]
  rwa [e] at h

theorem quadSum_resolvent_le {T : Matrix (Fin m) (Fin m) ℤ} (hT : GoodPT T) (hp23 : 23 ≤ p)
    (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) (μ : ZMod p)
    (hdet : IsUnit (modP p T - μ • 1).det) {t : ZMod p} (ht : t ≠ 0) :
    ‖quadSum (modP p T - μ • 1)⁻¹ t‖ ≤ Real.exp (-(cPT * m) / 2) := by
  have h := quadSum_pencil_le hT hp23 hpm μ hdet (t1 := t) (t2 := 0) (Or.inl ht)
  rwa [zero_smul, add_zero, quadSum_smul] at h

end Resolvent

end DGS
