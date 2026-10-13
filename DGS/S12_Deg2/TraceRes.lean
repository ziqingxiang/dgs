module

public import DGS.S11_Deg1.FourierInv
public import DGS.S03_Prelim.SimpleSubmodules

@[expose] public section

open Matrix Polynomial Module Finset

namespace DGS

section TraceIdentity

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {m : ℕ}

variable (K) in
noncomputable def trMat (B : Matrix (Fin m) (Fin m) L) : Matrix (Fin m) (Fin m) K :=
  B.map (Algebra.trace K L)

@[simp] theorem trMat_apply (B : Matrix (Fin m) (Fin m) L) (i j : Fin m) :
    trMat K B i j = Algebra.trace K L (B i j) := rfl

theorem trMat_add (B B' : Matrix (Fin m) (Fin m) L) : trMat K (B + B') = trMat K B + trMat K B' := by
  ext i j
  simp [map_add]

theorem trMat_sum {ι : Type*} (s : Finset ι) (B : ι → Matrix (Fin m) (Fin m) L) :
    trMat K (∑ i ∈ s, B i) = ∑ i ∈ s, trMat K (B i) := by
  ext i j
  simp [Matrix.sum_apply, map_sum]

theorem trMat_smul (c : K) (B : Matrix (Fin m) (Fin m) L) : trMat K (c • B) = c • trMat K B := by
  ext i j
  simp

theorem trMat_mul_map (C : Matrix (Fin m) (Fin m) L) (D : Matrix (Fin m) (Fin m) K) :
    trMat K (C * D.map (algebraMap K L)) = trMat K C * D := by
  ext i j
  simp only [trMat_apply, mul_apply, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]

theorem trMat_smul_map (t : L) (D : Matrix (Fin m) (Fin m) K) :
    trMat K (t • D.map (algebraMap K L)) = Algebra.trace K L t • D := by
  ext i j
  simp only [trMat_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]

theorem trace_quadForm (y : Fin m → K) (B : Matrix (Fin m) (Fin m) L) (t : L) :
    Algebra.trace K L (t * (liftVec K y ⬝ᵥ (B *ᵥ liftVec K y))) = y ⬝ᵥ (trMat K (t • B) *ᵥ y) := by
  simp only [dotProduct, mulVec, liftVec_apply, trMat_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show t * (algebraMap K L (y i) * (B i j * algebraMap K L (y j))) = (y i * y j) • (t * B i j) by
    rw [Algebra.smul_def, map_mul]; ring, LinearMap.map_smul, smul_eq_mul]
  ring

theorem inv_map_algebraMap (D : Matrix (Fin m) (Fin m) K) (hD : IsUnit D.det) :
    (D.map (algebraMap K L))⁻¹ = D⁻¹.map (algebraMap K L) := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv D hD, Matrix.map_one _ (map_zero _) (map_one _)]

variable (K) in
noncomputable def trPoly (μ : L) (t : L) : K[X] :=
  ∑ i ∈ Finset.range ((minpolyDiv K μ).natDegree + 1),
    C (Algebra.trace K L (t * (minpolyDiv K μ).coeff i)) * X ^ i

theorem aeval_trPoly (A : Matrix (Fin m) (Fin m) K) (μ t : L) :
    aeval A (trPoly K μ t) = ∑ i ∈ Finset.range ((minpolyDiv K μ).natDegree + 1),
      Algebra.trace K L (t * (minpolyDiv K μ).coeff i) • A ^ i := by
  simp only [trPoly, map_sum, map_mul, aeval_C, map_pow, aeval_X, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]

theorem natDegree_trPoly_le (μ t : L) : (trPoly K μ t).natDegree ≤ (minpolyDiv K μ).natDegree := by
  unfold trPoly
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := Finset.mem_range.1 hi
  omega

theorem coeff_trPoly (μ t : L) (i : ℕ) :
    (trPoly K μ t).coeff i = Algebra.trace K L (t * (minpolyDiv K μ).coeff i) := by
  unfold trPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hi : i < (minpolyDiv K μ).natDegree + 1
  · rw [Finset.sum_eq_single i (fun j _ hji => ite_eq_right (Ne.symm hji))
      (fun h => absurd (Finset.mem_range.2 hi) h), ite_eq_left rfl]
  · rw [Finset.sum_eq_zero (fun j hj => ite_eq_right (by
        intro hji
        subst hji
        exact hi (Finset.mem_range.1 hj))),
      coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, map_zero]

variable {β : K[X]} {μ : L}

theorem natDegree_trPoly_lt (h : IsGenRoot β μ) (t : L) : (trPoly K μ t).natDegree < β.natDegree := by
  have h1 := natDegree_trPoly_le (K := K) μ t
  have h2 : (minpolyDiv K μ).natDegree = β.natDegree - 1 := by
    rw [natDegree_minpolyDiv, h.minpoly_eq]
  have h3 : 0 < β.natDegree := h.irreducible.natDegree_pos
  omega

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem trPoly_eq_zero (h : IsGenRoot β μ) {t : L} (h0 : trPoly K μ t = 0) : t = 0 := by
  classical
  have hcoef : ∀ i, Algebra.trace K L (t * (minpolyDiv K μ).coeff i) = 0 := by
    intro i
    rw [← coeff_trPoly, h0, coeff_zero]
  set pb := h.powerBasis with hpb
  set D := aeval μ (derivative β) with hDdef
  have hD : D ≠ 0 := h.derivative_ne_zero
  have hdual : ∀ i, pb.basis.traceDual i = (minpolyDiv K μ).coeff i / D := by
    intro i
    rw [Module.Basis.traceDual_powerBasis_eq, h.powerBasis_gen, h.minpoly_eq]
  have hlin : Algebra.traceForm K L (t * D) = 0 := by
    apply pb.basis.traceDual.ext
    intro i
    rw [Algebra.traceForm_apply, hdual, LinearMap.zero_apply]
    rw [show t * D * ((minpolyDiv K μ).coeff i / D) = t * (minpolyDiv K μ).coeff i by
      field_simp]
    exact hcoef i
  have htD : t * D = 0 := (traceForm_nondegenerate K L).1 _ fun x => by rw [hlin]; rfl
  exact (mul_eq_zero.1 htD).resolve_right hD

theorem isUnit_aeval_of_isUnit (h : IsGenRoot β μ) (A : Matrix (Fin m) (Fin m) K)
    (hdet : IsUnit (A.map (algebraMap K L) - μ • 1).det) : IsUnit (aeval A β).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨w, hw, hwv⟩ := exists_trVec_eq h hv
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hv0 (by rw [← hwv, map_zero])
  apply isUnit_iff_ne_zero.1 hdet
  apply exists_mulVec_eq_zero_iff.1
  refine ⟨w, hw0, ?_⟩
  rw [sub_mulVec, smul_mulVec, one_mulVec, mem_eigsp.1 hw, sub_self]

theorem trMat_smul_resolvent (h : IsGenRoot β μ) (A : Matrix (Fin m) (Fin m) K)
    (hdet : IsUnit (A.map (algebraMap K L) - μ • 1).det) (t : L) :
    trMat K (t • (A.map (algebraMap K L) - μ • 1)⁻¹) = aeval A (trPoly K μ t) * (aeval A β)⁻¹ := by
  set AL := A.map (algebraMap K L) with hAL
  set γ := minpolyDiv K μ with hγ
  have hQ := isUnit_aeval_of_isUnit h A hdet
  have hfac : (AL - μ • 1) * aeval AL γ = (aeval A β).map (algebraMap K L) := by
    have hspec : (X - C μ) * γ = β.map (algebraMap K L) := by
      rw [mul_comm, hγ, minpolyDiv_spec, h.minpoly_eq]
    have h1 := congrArg (aeval AL) hspec
    rw [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, aeval_map_algebraMap,
      hAL, aeval_map_matrix] at h1
    exact h1
  have hB : (AL - μ • 1)⁻¹ = aeval AL γ * ((aeval A β)⁻¹).map (algebraMap K L) := by
    apply Matrix.inv_eq_right_inv
    rw [← mul_assoc, hfac, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hQ,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hγA : t • aeval AL γ = ∑ i ∈ Finset.range (γ.natDegree + 1),
      (t * γ.coeff i) • (A ^ i).map (algebraMap K L) := by
    rw [aeval_eq_sum_range, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hAL, Matrix.map_pow]
  rw [hB, ← smul_mul_assoc, trMat_mul_map, hγA, trMat_sum]
  congr 1
  rw [aeval_trPoly]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact trMat_smul_map _ _

end TraceIdentity

section Fourier

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [Algebra (ZMod p) L] {m : ℕ}

theorem twoValued_eq_liftVec (ξ : Fin m → Bool) :
    twoValued (1 : L) (-1) ξ = liftVec (ZMod p) (sgnP p ξ) := by
  funext j
  rw [sgnP_eq_twoValued]
  simp only [twoValued, liftVec_apply]
  cases ξ j <;> simp

theorem quadForm_trMat (ξ : Fin m → Bool) (B : Matrix (Fin m) (Fin m) L) (t : L) :
    sgnP p ξ ⬝ᵥ (trMat (ZMod p) (t • B) *ᵥ sgnP p ξ) =
      Algebra.trace (ZMod p) L (t * (twoValued (1 : L) (-1) ξ ⬝ᵥ (B *ᵥ twoValued 1 (-1) ξ))) := by
  rw [twoValued_eq_liftVec (p := p), trace_quadForm]

variable [FiniteDimensional (ZMod p) L]

theorem prob_quadL_eq_le_of (B : Matrix (Fin m) (Fin m) L) (a : L) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ s : L, s ≠ 0 → ‖quadSum (trMat (ZMod p) (s • B)) 1‖ ≤ ε) :
    prob (fun ξ : Fin m → Bool => twoValued (1 : L) (-1) ξ ⬝ᵥ (B *ᵥ twoValued 1 (-1) ξ) = a) ≤
      ((p : ℝ) ^ finrank (ZMod p) L)⁻¹ + ε := by
  classical
  set d := finrank (ZMod p) L with hd
  set b := Module.finBasisOfFinrankEq (ZMod p) L hd.symm with hb
  set q : (Fin m → Bool) → L := fun ξ => twoValued (1 : L) (-1) ξ ⬝ᵥ (B *ᵥ twoValued 1 (-1) ξ) with hq
  set Xc : (Fin m → Bool) → Fin d → ZMod p := fun ξ i => Algebra.trace (ZMod p) L (b i * q ξ) with hXc
  have h := prob_eq_le_fourier (Ω := Fin m → Bool) (ι := Fin d) Xc
    (fun i => Algebra.trace (ZMod p) L (b i * a)) hε0 (fun τ hτ => by
      set s : L := ∑ i, τ i • b i with hs
      have hs0 : s ≠ 0 := by
        intro h0
        apply hτ
        funext i
        exact Fintype.linearIndependent_iff.1 b.linearIndependent τ h0 i
      have e : ∀ ξ : Fin m → Bool, ∑ i, τ i * Xc ξ i =
          sgnP p ξ ⬝ᵥ (trMat (ZMod p) (s • B) *ᵥ sgnP p ξ) := by
        intro ξ
        rw [quadForm_trMat, hs, Finset.sum_mul, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hXc, smul_mul_assoc, LinearMap.map_smul, smul_eq_mul]
      have e2 : (Fintype.card (Fin m → Bool) : ℂ)⁻¹ *
          ∑ ξ : Fin m → Bool, ZMod.stdAddChar (∑ i, τ i * Xc ξ i) =
            quadSum (trMat (ZMod p) (s • B)) 1 := by
        unfold quadSum
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        push_cast
        congr 1
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [e, one_mul]
      rw [e2]
      exact hε s hs0)
  rw [Fintype.card_fin] at h
  refine le_trans (prob_mono fun ξ hξ => ?_) h
  funext i
  simp only [hXc]
  rw [show q ξ = a from hξ]

variable [Finite L]

theorem quadSum_trMat_le {T : Matrix (Fin m) (Fin m) ℤ} (hT : GoodPT T) (hp23 : 23 ≤ p)
    (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) (hL : finrank (ZMod p) L = 2)
    {μ : L} (hμ : μ ∉ Set.range (algebraMap (ZMod p) L))
    (hdet : IsUnit (T.map (Int.castRingHom L) - μ • 1).det) {t : L} (ht : t ≠ 0) :
    ‖quadSum (trMat (ZMod p) (t • (T.map (Int.castRingHom L) - μ • 1)⁻¹)) 1‖ ≤
      Real.exp (-(cPT * m) / 2) := by
  set β := minpoly (ZMod p) μ with hβ
  have hint : IsIntegral (ZMod p) μ := IsIntegral.of_finite (ZMod p) μ
  have hβd : β.natDegree = 2 := by
    have h1 : β.natDegree ≤ 2 := hL ▸ minpoly.natDegree_le μ
    have h2 : β.natDegree ≠ 1 := fun h => hμ (minpoly.natDegree_eq_one_iff.1 h)
    have h3 : 0 < β.natDegree := minpoly.natDegree_pos hint
    omega
  have hgen : IsGenRoot β μ :=
    ⟨minpoly.monic hint, minpoly.irreducible hint, minpoly.aeval _ _, by rw [hL, hβd]⟩
  have hAL : (modP p T).map (algebraMap (ZMod p) L) = T.map (Int.castRingHom L) := by
    ext i j
    simp [modP]
  rw [← hAL] at hdet ⊢
  rw [trMat_smul_resolvent hgen (modP p T) hdet t]
  refine hT p hp23 hpm β (trPoly (ZMod p) μ t) hgen.monic hβd (isUnit_aeval_of_isUnit hgen _ hdet)
    (fun h0 => ht (trPoly_eq_zero hgen h0)) ?_
  have := natDegree_trPoly_lt hgen t
  omega

theorem prob_quadL_le {T : Matrix (Fin m) (Fin m) ℤ} (hT : GoodPT T) (hp23 : 23 ≤ p)
    (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) (hL : finrank (ZMod p) L = 2)
    {μ : L} (hμ : μ ∉ Set.range (algebraMap (ZMod p) L))
    (hdet : IsUnit (T.map (Int.castRingHom L) - μ • 1).det) (a : L) :
    prob (fun ξ : Fin m → Bool => twoValued (1 : L) (-1) ξ ⬝ᵥ
      ((T.map (Int.castRingHom L) - μ • 1)⁻¹ *ᵥ twoValued 1 (-1) ξ) = a) ≤
      1 / (p : ℝ) ^ 2 + Real.exp (-(cPT * m) / 2) := by
  have h := prob_quadL_eq_le_of (L := L) (p := p) (T.map (Int.castRingHom L) - μ • 1)⁻¹ a
    (Real.exp_pos _).le fun t ht => quadSum_trMat_le hT hp23 hpm hL hμ hdet ht
  rwa [hL, ← one_div ((p : ℝ) ^ 2)] at h

end Fourier

end DGS
