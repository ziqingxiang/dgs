module

public import DGS.S07_Small.TightB

@[expose] public section

open Matrix Polynomial

namespace DGS

section Par

variable {R : Type*} [CommRing R] {n : ℕ}

theorem dot_pow_mulVec_pow {M : Matrix (Fin n) (Fin n) R} (hM : Mᵀ = M) (a b : ℕ)
    (u v : Fin n → R) : (M ^ a *ᵥ u) ⬝ᵥ (M ^ b *ᵥ v) = u ⬝ᵥ (M ^ (a + b) *ᵥ v) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, transpose_pow, hM, mulVec_mulVec,
    ← pow_add, dotProduct_comm]

theorem dot_self_eq_ones_dot (y : Fin n → ZMod 2) : y ⬝ᵥ y = ones n (ZMod 2) ⬝ᵥ y := by
  simp only [dotProduct, ones, one_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := ZMod.pow_card (y i)
  rwa [sq] at this

variable {M : Matrix (Fin n) (Fin n) (ZMod 2)}

theorem lem_par (hM : Mᵀ = M) (hd : ∀ i, M i i = 0) :
    ∀ i, 1 ≤ i → ones n (ZMod 2) ⬝ᵥ (M ^ i *ᵥ ones n (ZMod 2)) = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' i
    · have h1 : ones n (ZMod 2) ⬝ᵥ (M ^ (2 * l) *ᵥ ones n (ZMod 2)) =
          (M ^ l *ᵥ ones n (ZMod 2)) ⬝ᵥ (M ^ l *ᵥ ones n (ZMod 2)) := by
        rw [dot_pow_mulVec_pow hM, two_mul]
      rw [h1, dot_self_eq_ones_dot, ih l (by omega) (by omega)]
    · have h1 : ones n (ZMod 2) ⬝ᵥ (M ^ (2 * l + 1) *ᵥ ones n (ZMod 2)) =
          (M ^ l *ᵥ ones n (ZMod 2)) ⬝ᵥ (M *ᵥ (M ^ l *ᵥ ones n (ZMod 2))) := by
        rw [mulVec_mulVec, ← pow_succ', dot_pow_mulVec_pow hM, show l + (l + 1) = 2 * l + 1 by ring]
      rw [h1]
      exact dotProduct_mulVec_self_eq_zero (by decide) hM hd _

theorem dot_pow_ones_eq_zero (hM : Mᵀ = M) (hd : ∀ i, M i i = 0) {i j : ℕ} (h : i ≠ 0 ∨ j ≠ 0) :
    (M ^ i *ᵥ ones n (ZMod 2)) ⬝ᵥ (M ^ j *ᵥ ones n (ZMod 2)) = 0 := by
  rw [dot_pow_mulVec_pow hM]
  exact lem_par hM hd _ (by omega)

theorem ones_dot_aeval (hM : Mᵀ = M) (hd : ∀ i, M i i = 0) (g : (ZMod 2)[X]) :
    ones n (ZMod 2) ⬝ᵥ (aeval M g *ᵥ ones n (ZMod 2)) = g.coeff 0 * n := by
  rw [aeval_eq_sum_range, Matrix.sum_mulVec, dotProduct_sum, Finset.sum_range_succ']
  rw [Finset.sum_eq_zero (fun k _ => ?_), zero_add]
  · have h1 : ones n (ZMod 2) ⬝ᵥ ones n (ZMod 2) = n := by simp [ones, dotProduct]
    rw [pow_zero, smul_mulVec, one_mulVec, dotProduct_smul, h1, smul_eq_mul]
  · rw [smul_mulVec, dotProduct_smul, lem_par hM hd _ (by omega), smul_zero]

end Par

section Involutions

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem neg_eq_self_of_two_eq_zero (h2 : (2 : R) = 0) (x : R) : -x = x :=
  neg_eq_of_add_eq_zero_right (by rw [← two_mul, h2, zero_mul])

theorem det_eq_sum_involutions (h2 : (2 : R) = 0) (S : Matrix ι ι R) (hS : Sᵀ = S) :
    S.det = ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm ι => σ * σ = 1), ∏ i, S (σ i) i := by
  rw [det_apply]
  have hsign : ∀ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, S (σ i) i = ∏ i, S (σ i) i := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul, neg_eq_self_of_two_eq_zero h2]
  simp_rw [hsign]
  have h0 : ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm ι => ¬ σ * σ = 1), ∏ i, S (σ i) i = 0 := by
    refine Finset.sum_involution (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
    · intro σ _
      have : ∏ i, S (σ⁻¹ i) i = ∏ i, S (σ i) i := by
        rw [← Equiv.prod_comp σ (fun i => S (σ⁻¹ i) i)]
        refine Finset.prod_congr rfl fun j _ => ?_
        simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
        have := congrFun (congrFun hS (σ j)) j
        rwa [transpose_apply] at this
      rw [this, ← two_mul, h2, zero_mul]
    · intro σ hσ _ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      apply hσ
      nth_rewrite 2 [← heq]
      exact mul_inv_cancel σ
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      rwa [← _root_.mul_inv_rev, inv_eq_one]
    · intro σ _
      exact inv_inv σ
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ : Equiv.Perm ι => σ * σ = 1), h0,
    add_zero]

theorem card_fixed_modEq {σ : Equiv.Perm ι} (hσ : σ * σ = 1) :
    (Finset.univ.filter fun i => σ i = i).card % 2 = Fintype.card ι % 2 := by
  have h1 : σ ^ 2 ^ 1 = 1 := by rw [pow_one, sq]; exact hσ
  have h2 := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1) h1
  have h3 : (Finset.univ.filter fun i => σ i = i) = σ.supportᶜ := by
    ext i
    simp [Equiv.Perm.mem_support]
  rw [h3]
  exact h2

theorem charpoly_coeff_eq_zero_of_parity (h2 : (2 : R) = 0) {M : Matrix ι ι R} (hM : Mᵀ = M)
    (hd : ∀ i, M i i = 0) {k : ℕ} (hk : k % 2 ≠ Fintype.card ι % 2) : M.charpoly.coeff k = 0 := by
  have h2' : (2 : R[X]) = 0 := by
    rw [← map_ofNat C 2, h2, C_0]
  have hS : (charmatrix M)ᵀ = charmatrix M := by rw [← charmatrix_transpose, hM]
  rw [Matrix.charpoly, det_eq_sum_involutions h2' _ hS, finsetSum_coeff]
  refine Finset.sum_eq_zero fun σ hσ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  have hterm : ∏ i, charmatrix M (σ i) i = ∏ i, (if σ i = i then X else C (-M (σ i) i)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [h, charmatrix_apply_eq, hd, C_0, sub_zero]
    · rw [charmatrix_apply_ne _ _ _ h, C_neg]
  rw [hterm, Finset.prod_ite, Finset.prod_const, ← map_prod, mul_comm, coeff_C_mul_X_pow]
  rw [ite_eq_right]
  intro hkm
  apply hk
  rw [hkm]
  exact card_fixed_modEq hσ

end Involutions

section Adjugate

variable {R : Type*} [CommRing R] {n : ℕ}

theorem aeval_map_C_map (A : Matrix (Fin n) (Fin n) R) (g : R[X]) :
    aeval (A.map (C : R →+* R[X])) (g.map (C : R →+* R[X])) = (aeval A g).map C := by
  have h2 : aeval (A.map (C : R →+* R[X])) (g.map C) = aeval (A.map (C : R →+* R[X])) g := by
    rw [← Polynomial.algebraMap_eq, Polynomial.aeval_map_algebraMap]
  rw [h2]
  exact Polynomial.aeval_algHom_apply ((Algebra.ofId R R[X]).mapMatrix) A g

theorem exists_adjugate_charmatrix_eq (A : Matrix (Fin n) (Fin n) R) :
    ∃ g : R[X][X], (charmatrix A).adjugate = aeval (A.map (C : R →+* R[X])) g := by
  obtain ⟨g, hg⟩ := X_sub_C_dvd_sub_C_eval (p := A.charpoly.map (C : R →+* R[X])) (a := (X : R[X]))
  refine ⟨g, ?_⟩
  have heval : (A.charpoly.map (C : R →+* R[X])).eval X = A.charpoly := by
    rw [eval_map, eval₂_C_X]
  rw [heval] at hg
  set A' : Matrix (Fin n) (Fin n) R[X] := A.map (C : R →+* R[X]) with hA'
  have h1 : aeval A' (A.charpoly.map (C : R →+* R[X])) = 0 := by
    rw [hA', aeval_map_C_map, aeval_self_charpoly, Matrix.map_zero _ (map_zero _)]
  have h2 := congrArg (aeval A') hg
  rw [map_sub, h1, aeval_C, map_mul, map_sub, aeval_X, aeval_C, zero_sub,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at h2
  have hcm : charmatrix A = (X : R[X]) • (1 : Matrix (Fin n) (Fin n) R[X]) - A' := by
    rw [charmatrix, RingHom.mapMatrix_apply, scalar_apply, smul_one_eq_diagonal]
  have h3 : charmatrix A * aeval A' g = A.charpoly • (1 : Matrix (Fin n) (Fin n) R[X]) := by
    rw [hcm, ← neg_sub, neg_mul, ← h2, neg_neg]
  have hdet : (charmatrix A).det = A.charpoly := rfl
  have h4 : A.charpoly • aeval A' g = A.charpoly • (charmatrix A).adjugate := by
    calc A.charpoly • aeval A' g = ((charmatrix A).adjugate * charmatrix A) * aeval A' g := by
          rw [adjugate_mul, hdet, smul_mul_assoc, Matrix.one_mul]
      _ = (charmatrix A).adjugate * (A.charpoly • (1 : Matrix (Fin n) (Fin n) R[X])) := by
          rw [Matrix.mul_assoc, h3]
      _ = A.charpoly • (charmatrix A).adjugate := by rw [mul_smul_comm, Matrix.mul_one]
  refine Matrix.ext fun i j => ?_
  have h5 := congrFun (congrFun h4 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h5
  have h6 : A.charpoly * ((charmatrix A).adjugate i j - aeval A' g i j) = 0 := by
    rw [mul_sub, h5, sub_self]
  rw [(charpoly_monic A).mul_right_eq_zero_iff] at h6
  exact (sub_eq_zero.1 h6)

theorem X_mul_psiPoly_of_walks (A : Matrix (Fin n) (Fin n) R)
    (hN : ∀ k, 1 ≤ k → ones n R ⬝ᵥ (A ^ k *ᵥ ones n R) = 0) :
    X * psiPoly A = (n : R[X]) * A.charpoly := by
  obtain ⟨g, hg⟩ := exists_adjugate_charmatrix_eq A
  set A' : Matrix (Fin n) (Fin n) R[X] := A.map (C : R →+* R[X]) with hA'
  have hψ : psiPoly A = ones n R[X] ⬝ᵥ ((charmatrix A).adjugate *ᵥ ones n R[X]) := by
    simp [psiPoly, dotProduct, mulVec, ones]
  have hX : (X : R[X]) • ones n R[X] = charmatrix A *ᵥ ones n R[X] + A' *ᵥ ones n R[X] := by
    rw [← add_mulVec, charmatrix, RingHom.mapMatrix_apply, ← hA', sub_add_cancel, scalar_apply,
      ← smul_one_eq_diagonal, smul_mulVec, one_mulVec]
  have hones : ones n R[X] ⬝ᵥ ones n R[X] = (n : R[X]) := by
    simp [ones, dotProduct]
  have hmap : ∀ k, ones n R[X] ⬝ᵥ (A' ^ k *ᵥ ones n R[X]) = C (ones n R ⬝ᵥ (A ^ k *ᵥ ones n R)) := by
    intro k
    rw [hA', ← Matrix.map_pow]
    simp [dotProduct, mulVec, ones, map_sum]
  have hzero : ones n R[X] ⬝ᵥ (((charmatrix A).adjugate * A') *ᵥ ones n R[X]) = 0 := by
    rw [hg]
    nth_rewrite 2 [← aeval_X (R := R[X]) A']
    rw [← map_mul, aeval_eq_sum_range, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_mulVec, dotProduct_smul, hmap]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [coeff_mul_X_zero, zero_smul]
    · rw [hN k hk, C_0, smul_zero]
  have hdet : (charmatrix A).det = A.charpoly := rfl
  calc X * psiPoly A = ones n R[X] ⬝ᵥ ((charmatrix A).adjugate *ᵥ ((X : R[X]) • ones n R[X])) := by
        rw [hψ, mulVec_smul, dotProduct_smul, smul_eq_mul]
    _ = ones n R[X] ⬝ᵥ (((charmatrix A).adjugate * charmatrix A) *ᵥ ones n R[X]) +
          ones n R[X] ⬝ᵥ (((charmatrix A).adjugate * A') *ᵥ ones n R[X]) := by
        rw [hX, mulVec_add, dotProduct_add, mulVec_mulVec, mulVec_mulVec]
    _ = (n : R[X]) * A.charpoly := by
        rw [hzero, add_zero, adjugate_mul, hdet, smul_mulVec, one_mulVec, dotProduct_smul, hones,
          smul_eq_mul, mul_comm]

end Adjugate

section Gamma

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

noncomputable def phiZero : (ZMod 2)[X] :=
  if n % 2 = 0 then redP 2 A.charpoly else divX (redP 2 A.charpoly)

noncomputable def gam : (ZMod 2)[X] := contract 2 (phiZero A)

variable {A}

theorem modP_two_transpose (hA : A.IsSymm) : (modP 2 A)ᵀ = modP 2 A := modP_isSymm 2 hA

theorem modP_two_diag (hd : ∀ i, A i i = 0) (i : Fin n) : modP 2 A i i = 0 := by
  simp [modP, hd]

variable (hA : A.IsSymm) (hd : ∀ i, A i i = 0)
include hA hd

theorem redP_charpoly_coeff_eq_zero {k : ℕ} (hk : k % 2 ≠ n % 2) :
    (redP 2 A.charpoly).coeff k = 0 := by
  rw [← charpoly_modP_eq]
  exact charpoly_coeff_eq_zero_of_parity (by decide) (modP_two_transpose hA) (modP_two_diag hd)
    (by rwa [Fintype.card_fin])

theorem phiZero_coeff_odd {k : ℕ} (hk : k % 2 = 1) : (phiZero A).coeff k = 0 := by
  unfold phiZero
  split_ifs with h
  · exact redP_charpoly_coeff_eq_zero hA hd (by omega)
  · rw [coeff_divX]
    exact redP_charpoly_coeff_eq_zero hA hd (by omega)

theorem phiZero_eq_gam_sq : phiZero A = gam A ^ 2 := by
  have h1 : expand (ZMod 2) 2 (gam A) = phiZero A := by
    ext m
    rw [gam, coeff_expand (by norm_num), coeff_contract (by norm_num)]
    split_ifs with h
    · rw [Nat.div_mul_cancel h]
    · symm
      exact phiZero_coeff_odd hA hd (by omega)
  rw [← h1, ZMod.expand_card]

theorem redP_charpoly_eq : redP 2 A.charpoly = X ^ (n % 2) * gam A ^ 2 := by
  rw [← phiZero_eq_gam_sq hA hd, phiZero]
  split_ifs with h
  · rw [h, pow_zero, one_mul]
  · have h1 : n % 2 = 1 := by omega
    have h0 : (redP 2 A.charpoly).coeff 0 = 0 := redP_charpoly_coeff_eq_zero hA hd (by omega)
    have := X_mul_divX_add (redP 2 A.charpoly)
    rw [h0, C_0, add_zero] at this
    rw [h1, pow_one, this]

omit hA hd in
theorem redP_charpoly_monic : (redP 2 A.charpoly).Monic := (charpoly_monic A).map _

omit hA hd in
theorem natDegree_redP_charpoly : (redP 2 A.charpoly).natDegree = n := by
  rw [← charpoly_modP_eq, charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem gam_ne_zero : gam A ≠ 0 := by
  intro h
  have := redP_charpoly_eq hA hd
  rw [h, zero_pow two_ne_zero, mul_zero] at this
  exact (redP_charpoly_monic (A := A)).ne_zero this

theorem gam_monic : (gam A).Monic := by
  have h1 : (X ^ (n % 2) * gam A ^ 2).Monic := by
    rw [← redP_charpoly_eq hA hd]; exact redP_charpoly_monic
  have h2 : (gam A ^ 2).Monic := (monic_X_pow _).of_mul_monic_left h1
  have h3 : (gam A).leadingCoeff ^ 2 = 1 := by
    rw [← leadingCoeff_pow]; exact h2
  have h4 := ZMod.pow_card (gam A).leadingCoeff
  rw [h3] at h4
  exact h4.symm

theorem natDegree_gam : (gam A).natDegree = n / 2 := by
  have h := congrArg natDegree (redP_charpoly_eq hA hd)
  rw [natDegree_redP_charpoly, natDegree_mul (pow_ne_zero _ X_ne_zero)
    (pow_ne_zero _ (gam_ne_zero hA hd)), natDegree_X_pow, natDegree_pow] at h
  omega

theorem X_mul_psi_mod2 : X * redP 2 (psiPoly A) = (n : (ZMod 2)[X]) * redP 2 A.charpoly := by
  have h := X_mul_psiPoly_of_walks (modP 2 A) (lem_par (modP_two_transpose hA) (modP_two_diag hd))
  rwa [charpoly_modP_eq, modP, psiPoly_map] at h

theorem psi_mod2_even (h : n % 2 = 0) : redP 2 (psiPoly A) = 0 := by
  have h1 := X_mul_psi_mod2 hA hd
  have h2 : (n : (ZMod 2)[X]) = 0 := by
    rw [← map_natCast C, (ZMod.natCast_eq_zero_iff n 2).2 (Nat.dvd_of_mod_eq_zero h), C_0]
  rw [h2, zero_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left X_ne_zero

theorem psi_mod2_odd (h : n % 2 = 1) : redP 2 (psiPoly A) = gam A ^ 2 := by
  have h1 := X_mul_psi_mod2 hA hd
  have h2 : (n : (ZMod 2)[X]) = 1 := by
    rw [← map_natCast C, ← ZMod.natCast_mod, h, Nat.cast_one, C_1]
  rw [h2, one_mul, redP_charpoly_eq hA hd, h, pow_one] at h1
  exact mul_left_cancel₀ X_ne_zero h1

theorem span_phi_psi_mod2 :
    Ideal.span {redP 2 A.charpoly, redP 2 (psiPoly A)} = Ideal.span {gam A ^ 2} := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro f (rfl | rfl)
    · rw [redP_charpoly_eq hA hd]
      exact Ideal.mem_span_singleton.2 (dvd_mul_left _ _)
    · rcases Nat.mod_two_eq_zero_or_one n with h | h
      · rw [psi_mod2_even hA hd h]; exact zero_mem _
      · rw [psi_mod2_odd hA hd h]; exact Ideal.mem_span_singleton_self _
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have : gam A ^ 2 = redP 2 A.charpoly := by
        rw [redP_charpoly_eq hA hd, h, pow_zero, one_mul]
      rw [this]
      exact Ideal.subset_span (Set.mem_insert _ _)
    · rw [← psi_mod2_odd hA hd h]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

theorem dvd_phi_psi_iff {β : (ZMod 2)[X]} (hβ : Irreducible β) :
    (β ∣ redP 2 A.charpoly ∧ β ∣ redP 2 (psiPoly A)) ↔ β ∣ gam A := by
  have hp := hβ.prime
  constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [redP_charpoly_eq hA hd, h, pow_zero, one_mul] at h1
      exact hp.dvd_of_dvd_pow h1
    · rw [psi_mod2_odd hA hd h] at h2
      exact hp.dvd_of_dvd_pow h2
  · intro h
    have h' : β ∣ gam A ^ 2 := h.trans (dvd_pow_self _ two_ne_zero)
    refine ⟨?_, ?_⟩
    · rw [redP_charpoly_eq hA hd]; exact h'.trans (dvd_mul_left _ _)
    · rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
      · rw [psi_mod2_even hA hd h2]; exact dvd_zero _
      · rw [psi_mod2_odd hA hd h2]; exact h'

theorem idealT_le_idealM_iff {β : (ZMod 2)[X]} (hβ : Irreducible β) :
    idealT A ≤ idealM 2 β ↔ β ∣ gam A := by
  rw [← dvd_phi_psi_iff hA hd hβ, idealT, Ideal.span_le]
  constructor
  · intro h
    exact ⟨(mem_idealM_iff β _).1 (h (Set.mem_insert _ _)),
      (mem_idealM_iff β _).1 (h (Set.mem_insert_of_mem _ rfl))⟩
  · rintro ⟨h1, h2⟩ f (rfl | rfl)
    · exact (mem_idealM_iff β _).2 h1
    · exact (mem_idealM_iff β _).2 h2

theorem mem_factorsSet_of_dvd_gam {β : (ZMod 2)[X]} (hβm : β.Monic) (hβ : Irreducible β)
    (h : β ∣ gam A) : β ∈ factorsSet (redP 2 A.charpoly) :=
  mem_factorsSet_of_dvd redP_charpoly_monic hβm hβ ((dvd_phi_psi_iff hA hd hβ).2 h).1

theorem lem_Ttwo_c (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) {β : (ZMod 2)[X]} (hβm : β.Monic)
    (hβ : Irreducible β) : TTpart A 2 β ≠ ⊥ ↔ β ∣ gam A := by
  constructor
  · intro hne
    by_contra hdvd
    rw [← idealT_le_idealM_iff hA hd hβ] at hdvd
    apply hne
    rw [TTpart]
    exact Ideal.map_mk_eq_bot_of_le (JT_le_idealT_of_not_le hβ hdvd)
  · intro h
    rw [TTpart_ne_bot_iff hA hn hW (mem_factorsSet_of_dvd_gam hA hd hβm hβ h)]
    exact (idealT_le_idealM_iff hA hd hβ).2 h

end Gamma

end DGS
