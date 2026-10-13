module

public import DGS.S03_Prelim.KernelPoly
public import DGS.S11_Deg1.PencilSuppU

@[expose] public section

open Finset Matrix Polynomial Module

namespace DGS

section Coeffs

variable {F : Type*} [Field F] {m d : ℕ}

noncomputable def polyOf (a : Fin d → F) : F[X] := ∑ i : Fin d, C (a i) * X ^ (i : ℕ)

def polyA (A : Matrix (Fin m) (Fin m) F) (a : Fin d → F) : Matrix (Fin m) (Fin m) F :=
  ∑ i : Fin d, a i • A ^ (i : ℕ)

theorem aeval_polyOf (A : Matrix (Fin m) (Fin m) F) (a : Fin d → F) : aeval A (polyOf a) = polyA A a := by
  simp only [polyOf, polyA, map_sum, map_mul, aeval_C, map_pow, aeval_X, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]

theorem coeff_polyOf (a : Fin d → F) (i : Fin d) : (polyOf a).coeff i = a i := by
  rw [polyOf, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [ite_eq_right]
    intro h
    exact hj (Fin.ext h.symm)
  · simp

theorem polyOf_ne_zero {a : Fin d → F} (ha : a ≠ 0) : polyOf a ≠ 0 := by
  intro h0
  apply ha
  funext i
  rw [← coeff_polyOf a i, h0, coeff_zero, Pi.zero_apply]

theorem natDegree_polyOf_lt {a : Fin d → F} (ha : a ≠ 0) : (polyOf a).natDegree < d :=
  (natDegree_lt_iff_degree_lt (polyOf_ne_zero ha)).2 (degree_sum_fin_lt a)

theorem eq_polyOf {P : F[X]} (hP : P.natDegree < d) : P = polyOf (fun i : Fin d => P.coeff i) := by
  rw [polyOf, Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i)]
  exact as_sum_range_C_mul_X_pow' P hP

theorem coeffs_ne_zero {P : F[X]} (hP : P.natDegree < d) (hP0 : P ≠ 0) :
    (fun i : Fin d => P.coeff i) ≠ 0 := by
  intro h
  apply hP0
  rw [eq_polyOf hP, h]
  simp [polyOf]

end Coeffs

section Rank

variable {F : Type*} [Field F] {m : ℕ}

theorem rank_le_rank_mul_add (M N : Matrix (Fin m) (Fin m) F) :
    N.rank ≤ (M * N).rank + finrank F (LinearMap.ker M.mulVecLin) := by
  set V := LinearMap.range N.mulVecLin with hV
  set f := M.mulVecLin.domRestrict V with hf
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : LinearMap.range f = LinearMap.range (M * N).mulVecLin := by
    rw [hf, LinearMap.range_domRestrict, Matrix.mulVecLin_mul, LinearMap.range_comp]
  have h3 : finrank F (LinearMap.ker f) ≤ finrank F (LinearMap.ker M.mulVecLin) := by
    have hle : (LinearMap.ker f).map V.subtype ≤ LinearMap.ker M.mulVecLin := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    rw [← Submodule.finrank_map_subtype_eq V (LinearMap.ker f)]
    exact Submodule.finrank_mono hle
  have h4 : N.rank = finrank F V := rfl
  have h5 : (M * N).rank = finrank F (LinearMap.range (M * N).mulVecLin) := rfl
  rw [h4, h5, ← h2]
  omega

theorem rank_diagSet (U : Finset (Fin m)) : (diagSet U : Matrix (Fin m) (Fin m) F).rank = U.card := by
  classical
  rw [diagSet, Matrix.rank_diagonal, Fintype.card_subtype]
  congr 1
  ext j
  simp

theorem finrank_ker_diagSet (R : Finset (Fin m)) :
    finrank F (LinearMap.ker (diagSet R : Matrix (Fin m) (Fin m) F).mulVecLin) = Rᶜ.card := by
  have h := LinearMap.finrank_range_add_finrank_ker (diagSet R : Matrix (Fin m) (Fin m) F).mulVecLin
  have h1 : finrank F (LinearMap.range (diagSet R : Matrix (Fin m) (Fin m) F).mulVecLin) = R.card :=
    rank_diagSet R
  rw [h1, Module.finrank_fin_fun] at h
  have h2 := Finset.card_add_card_compl R
  simp only [Fintype.card_fin] at h2
  omega

theorem card_le_rank_diagSet (X : Matrix (Fin m) (Fin m) F) (R U : Finset (Fin m)) :
    U.card ≤ (diagSet R * X * diagSet U).rank + finrank F (LinearMap.ker X.mulVecLin) + Rᶜ.card := by
  have h1 := rank_le_rank_mul_add X (diagSet U)
  have h2 := rank_le_rank_mul_add (diagSet R) (X * diagSet U)
  rw [rank_diagSet] at h1
  rw [finrank_ker_diagSet, ← Matrix.mul_assoc] at h2
  omega

theorem finrank_ker_mul_inv_le (P Q : Matrix (Fin m) (Fin m) F) (hQ : IsUnit Q.det) :
    finrank F (LinearMap.ker (P * Q⁻¹).mulVecLin) ≤ finrank F (LinearMap.ker P.mulVecLin) := by
  have hle : LinearMap.ker (P * Q⁻¹).mulVecLin ≤ (LinearMap.ker P.mulVecLin).map Q.mulVecLin := by
    intro x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← mulVec_mulVec] at hx
    refine ⟨Q⁻¹ *ᵥ x, hx, ?_⟩
    rw [Matrix.mulVecLin_apply, mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ, one_mulVec]
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le _ _)

end Rank

section Kernel

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

variable (p) in
def KerGood (d r : ℕ) (A : Matrix (Fin m) (Fin m) (ZMod p)) : Prop :=
  ∀ a : Fin d → ZMod p, a ≠ 0 → finrank (ZMod p) (LinearMap.ker (polyA A a).mulVecLin) ≤ (d - 1) * (r - 1)

theorem not_dvd_one_sub_neg_one (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ 1 - -1 := by
  intro h
  have h2 : (p : ℤ) ∣ (2 : ℕ) := by norm_num at h ⊢; exact h
  have h3 : p ∣ 2 := Int.natCast_dvd_natCast.1 h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h3)

theorem prob_not_kerGood_le (hp2 : p ≠ 2) (d r : ℕ) (hr : 1 ≤ r) :
    prob (fun ω : Pairs m → Bool => ¬ KerGood p d r (modP p (seidelOf ω))) ≤
      60 * (p : ℝ) ^ (d - 1) * (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4)) := by
  refine le_trans (prob_mono fun ω hω => ?_) (cor_kernelpoly (not_dvd_one_sub_neg_one hp2) d r hr m)
  intro hall
  apply hω
  intro a ha
  have h := hall (polyOf a) (polyOf_ne_zero ha) (natDegree_polyOf_lt ha)
  rwa [aeval_polyOf] at h

end Kernel

section Supp

variable {m : ℕ}

theorem card_small_subsets20_le :
    ((((univ : Finset (Fin m)).powerset.filter fun S => 20 * S.card < m).card : ℕ) : ℝ) ≤
      (16 : ℝ) ^ (m / 20) * (17 / 16) ^ m := by
  set K := m / 20 with hK
  have h1 : ∀ S ∈ (univ : Finset (Fin m)).powerset.filter (fun S => 20 * S.card < m),
      (1 : ℝ) ≤ (16 : ℝ) ^ K * ((1 : ℝ) / 16) ^ S.card := by
    intro S hS
    rw [mem_filter] at hS
    have hSK : S.card ≤ K := by omega
    have e : (16 : ℝ) ^ K = 16 ^ (K - S.card) * 16 ^ S.card := by
      rw [← pow_add, Nat.sub_add_cancel hSK]
    rw [e, mul_assoc, ← mul_pow, show (16 : ℝ) * (1 / 16) = 1 by norm_num, one_pow, mul_one]
    exact one_le_pow₀ (by norm_num)
  calc ((((univ : Finset (Fin m)).powerset.filter fun S => 20 * S.card < m).card : ℕ) : ℝ)
      = ∑ _S ∈ (univ : Finset (Fin m)).powerset.filter (fun S => 20 * S.card < m), (1 : ℝ) := by
        rw [sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ S ∈ (univ : Finset (Fin m)).powerset.filter (fun S => 20 * S.card < m),
          (16 : ℝ) ^ K * ((1 : ℝ) / 16) ^ S.card := sum_le_sum h1
    _ ≤ ∑ S ∈ (univ : Finset (Fin m)).powerset, (16 : ℝ) ^ K * ((1 : ℝ) / 16) ^ S.card :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
    _ = (16 : ℝ) ^ K * (17 / 16) ^ m := by
        rw [← mul_sum]
        congr 1
        have := Finset.sum_pow_mul_eq_add_pow ((1 : ℝ) / 16) 1 (univ : Finset (Fin m))
        simp only [one_pow, mul_one, card_univ, Fintype.card_fin] at this
        rw [this]
        norm_num

theorem fullsupp_numeric {r : ℕ} (hr : 0.348 * (m : ℝ) ≤ r) :
    (16 : ℝ) ^ (m / 20) * (17 / 16) ^ m * (1 / 2 ^ r) ≤ Real.exp (-(m : ℝ) / 30) := by
  have hl1 : (0.6931 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2 : Real.log 2 ≤ 0.6932 := by have := Real.log_two_lt_d9; linarith
  have hK : ((m / 20 : ℕ) : ℝ) ≤ (m : ℝ) / 20 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (m / 20) * 20 ≤ m := Nat.div_mul_le_self m 20
    exact_mod_cast this
  have h16 : (16 : ℝ) ^ (m / 20) ≤ Real.exp (4 * 0.6932 * (m / 20 : ℕ)) := by
    rw [show (16 : ℝ) ^ (m / 20) = 2 ^ (4 * (m / 20)) by rw [pow_mul]; norm_num, two_pow_eq_exp]
    apply Real.exp_le_exp.2
    push_cast
    have : (0 : ℝ) ≤ ((m / 20 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h17 : ((17 : ℝ) / 16) ^ m ≤ Real.exp (m / 16) := by
    rw [show (m : ℝ) / 16 = m * (1 / 16) by ring, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by norm_num)
    have := Real.add_one_le_exp ((1 : ℝ) / 16)
    linarith
  have h2r : (1 : ℝ) / 2 ^ r ≤ Real.exp (-(0.6931 * 0.348 * m)) := by
    rw [two_pow_eq_exp, one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.2
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    nlinarith
  calc (16 : ℝ) ^ (m / 20) * (17 / 16) ^ m * (1 / 2 ^ r)
      ≤ Real.exp (4 * 0.6932 * (m / 20 : ℕ)) * Real.exp (m / 16) * Real.exp (-(0.6931 * 0.348 * m)) := by
        gcongr
    _ = Real.exp (4 * 0.6932 * (m / 20 : ℕ) + m / 16 - 0.6931 * 0.348 * m) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(m : ℝ) / 30) := by
        apply Real.exp_le_exp.2
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        nlinarith

variable {p : ℕ} [Fact p.Prime]

theorem lem_fullsupp_U (hp2 : p ≠ 2) {d r : ℕ} {A Q : Matrix (Fin m) (Fin m) (ZMod p)}
    (hker : KerGood p d r A) (hr : 500 * ((d - 1) * (r - 1)) ≤ m) (hQ : IsUnit Q.det)
    (U : Finset (Fin m)) (hU : 2 * m ≤ 5 * U.card) :
    prob (fun ξ : Fin m → Bool => ∃ a : Fin d → ZMod p, a ≠ 0 ∧
      20 * (univ.filter fun j => ((polyA A a * Q⁻¹) *ᵥ uOn p U ξ) j ≠ 0).card < m) ≤
      (p : ℝ) ^ d * Real.exp (-(m : ℝ) / 30) := by
  classical
  set c := Real.exp (-(m : ℝ) / 30) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  set N : ℝ := (16 : ℝ) ^ (m / 20) * (17 / 16) ^ m with hN
  have hN0 : 0 < N := by positivity
  have hbound : ∀ a : Fin d → ZMod p, prob (fun ξ : Fin m → Bool => a ≠ 0 ∧
      20 * (univ.filter fun j => ((polyA A a * Q⁻¹) *ᵥ uOn p U ξ) j ≠ 0).card < m) ≤ c := by
    intro a
    by_cases ha : a = 0
    · rw [prob_congr (Q := fun _ => False) fun ξ => ⟨fun h => h.1 ha, False.elim⟩, prob_false]
      exact hc0
    set X := polyA A a * Q⁻¹ with hX
    set Sset := (univ : Finset (Fin m)).powerset.filter fun S => 20 * S.card < m with hSset
    have hsub : ∀ ξ : Fin m → Bool, (a ≠ 0 ∧ 20 * (univ.filter fun j => (X *ᵥ uOn p U ξ) j ≠ 0).card < m) →
        ∃ S ∈ Sset, ∀ j ∈ Sᶜ, (X *ᵥ uOn p U ξ) j = 0 := by
      intro ξ ⟨_, hlt⟩
      refine ⟨univ.filter fun j => (X *ᵥ uOn p U ξ) j ≠ 0, ?_, ?_⟩
      · rw [hSset, mem_filter, mem_powerset]
        exact ⟨subset_univ _, hlt⟩
      · intro j hj
        rw [mem_compl, mem_filter] at hj
        by_contra h0
        exact hj ⟨mem_univ _, h0⟩
    have hdimX : finrank (ZMod p) (LinearMap.ker X.mulVecLin) ≤ (d - 1) * (r - 1) :=
      (finrank_ker_mul_inv_le _ _ hQ).trans (hker a ha)
    have hrank : ∀ S ∈ Sset, 0.348 * (m : ℝ) ≤ (diagSet Sᶜ * X * diagSet U).rank := by
      intro S hS
      rw [hSset, mem_filter] at hS
      have h1 := card_le_rank_diagSet X Sᶜ U
      rw [compl_compl] at h1
      have h1' : U.card ≤ (diagSet Sᶜ * X * diagSet U).rank + (d - 1) * (r - 1) + S.card := by omega
      have h2 : ((2 * m : ℕ) : ℝ) ≤ ((5 * U.card : ℕ) : ℝ) := by exact_mod_cast hU
      have h3 : ((500 * ((d - 1) * (r - 1)) : ℕ) : ℝ) ≤ m := by exact_mod_cast hr
      have h4 : ((20 * S.card : ℕ) : ℝ) < m := by exact_mod_cast hS.2
      have h5 : ((U.card : ℕ) : ℝ) ≤ (((diagSet Sᶜ * X * diagSet U).rank + (d - 1) * (r - 1) + S.card : ℕ) : ℝ) := by
        exact_mod_cast h1'
      push_cast at h2 h3 h4 h5
      linarith
    calc prob (fun ξ : Fin m → Bool => a ≠ 0 ∧
          20 * (univ.filter fun j => (X *ᵥ uOn p U ξ) j ≠ 0).card < m)
        ≤ prob (fun ξ : Fin m → Bool => ∃ S ∈ Sset, ∀ j ∈ Sᶜ, (X *ᵥ uOn p U ξ) j = 0) := prob_mono hsub
      _ ≤ ∑ S ∈ Sset, prob (fun ξ : Fin m → Bool => ∀ j ∈ Sᶜ, (X *ᵥ uOn p U ξ) j = 0) :=
          prob_exists_le_sum _ _
      _ ≤ ∑ S ∈ Sset, N * (1 / 2 ^ (diagSet Sᶜ * X * diagSet U).rank) / N := by
          refine sum_le_sum fun S _ => (prob_CuR_zero_le hp2 X U Sᶜ).trans (le_of_eq ?_)
          field_simp
      _ ≤ ∑ _S ∈ Sset, c / N := by
          refine sum_le_sum fun S hS => ?_
          gcongr
          exact fullsupp_numeric (hrank S hS)
      _ = (Sset.card : ℝ) * (c / N) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ N * (c / N) := by
          gcongr
          exact card_small_subsets20_le
      _ = c := by field_simp
  calc prob (fun ξ : Fin m → Bool => ∃ a : Fin d → ZMod p, a ≠ 0 ∧
        20 * (univ.filter fun j => ((polyA A a * Q⁻¹) *ᵥ uOn p U ξ) j ≠ 0).card < m)
      ≤ ∑ a : Fin d → ZMod p, prob (fun ξ : Fin m → Bool => a ≠ 0 ∧
          20 * (univ.filter fun j => ((polyA A a * Q⁻¹) *ᵥ uOn p U ξ) j ≠ 0).card < m) :=
        prob_exists_le_sum_fintype _
    _ ≤ ∑ _a : Fin d → ZMod p, c := sum_le_sum fun a _ => hbound a
    _ = (p : ℝ) ^ d * c := by
        rw [sum_const, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

theorem lem_fullsupp (hp2 : p ≠ 2) {d r : ℕ} {A Q : Matrix (Fin m) (Fin m) (ZMod p)}
    (hker : KerGood p d r A) (hr : 500 * ((d - 1) * (r - 1)) ≤ m) (hQ : IsUnit Q.det) :
    prob (fun x : SignPair m => 2 * m ≤ 5 * (suppU x).card ∧ ∃ a : Fin d → ZMod p, a ≠ 0 ∧
      20 * (univ.filter fun j => ((polyA A a * Q⁻¹) *ᵥ uPair p x) j ≠ 0).card < m) ≤
      (p : ℝ) ^ d * Real.exp (-(m : ℝ) / 30) := by
  classical
  rw [← prob_equiv pairDiffEquiv.symm]
  refine prob_le_of_forall_snd (fun dd => ?_) (by positivity)
  set U := univ.filter fun j => dd j = true with hU
  by_cases hUc : 2 * m ≤ 5 * U.card
  · refine le_trans (prob_mono fun ξ hξ => ?_) (lem_fullsupp_U hp2 hker hr hQ U hUc)
    obtain ⟨-, a, ha, h⟩ := hξ
    rw [uPair_pairDiff] at h
    exact ⟨a, ha, h⟩
  · rw [prob_congr (Q := fun _ => False) fun ξ => ⟨fun h => hUc (by
      have h1 := h.1
      rw [suppU_pairDiff] at h1
      exact h1), False.elim⟩, prob_false]
    positivity

end Supp

end DGS
