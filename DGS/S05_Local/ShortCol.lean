module

public import DGS.S05_Local.Levels

@[expose] public section

open Matrix Polynomial

namespace DGS

variable {n : ℕ}

section PowMult

variable {F : Type*} [Field F]

theorem pow_mult_mem_span {φ β : F[X]} (hφ : φ.Monic) (hβ : β ∈ factorsSet φ) (k : ℕ) :
    β ^ mult φ β ∈ Ideal.span {φ, β ^ k} := by
  rcases le_or_gt k (mult φ β) with hk | hk
  · have : β ^ mult φ β = β ^ (mult φ β - k) * β ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  · have hcop := isCoprime_pow_cofactor hβ
    have hcop1 : IsCoprime β (cofactor φ β) :=
      hcop.of_isCoprime_of_dvd_left (dvd_pow_self β (mult_pos hβ).ne')
    obtain ⟨u, v, huv⟩ := (hcop1.pow_left (m := k - mult φ β))
    have h1 : β ^ mult φ β = u * β ^ k + v * φ := by
      have hφeq := pow_mul_cofactor hφ hβ
      have : β ^ k = β ^ (k - mult φ β) * β ^ mult φ β := by
        rw [← pow_add, Nat.sub_add_cancel hk.le]
      linear_combination (-(β ^ mult φ β)) * huv + (-u) * this + v * hφeq
    rw [h1, add_comm]
    exact Ideal.mem_span_pair.2 ⟨v, u, rfl⟩

end PowMult

section Lift

variable {p : ℕ} [hp : Fact p.Prime]

theorem liftZ_pow_mult_mem {φ : ℤ[X]} (hφ : φ.Monic) {β : (ZMod p)[X]}
    (hβ : β ∈ factorsSet (redP p φ)) (k : ℕ) {𝔞 : Ideal ℤ[X]} (hp𝔞 : C (p : ℤ) ∈ 𝔞)
    (hφ𝔞 : φ ∈ 𝔞) (hk𝔞 : liftZ p β ^ k ∈ 𝔞) : liftZ p β ^ mult (redP p φ) β ∈ 𝔞 := by
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (pow_mult_mem_span (hφ.map _) hβ k)
  have h0 : (liftZ p β ^ mult (redP p φ) β - liftZ p u * φ - liftZ p v * liftZ p β ^ k).map
      (Int.castRingHom (ZMod p)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_pow, map_liftZ, map_liftZ, map_liftZ, ← huv]
    simp
  obtain ⟨q, hq⟩ := (map_eq_zero_iff_C_dvd p _).1 h0
  have : liftZ p β ^ mult (redP p φ) β = C (p : ℤ) * q + liftZ p u * φ + liftZ p v * liftZ p β ^ k := by
    linear_combination hq
  rw [this]
  exact add_mem (add_mem (Ideal.mul_mem_right _ _ hp𝔞) (Ideal.mul_mem_left _ _ hφ𝔞))
    (Ideal.mul_mem_left _ _ hk𝔞)

end Lift

section AnnLat

variable (A : Matrix (Fin n) (Fin n) ℤ)

noncomputable def annLat {L : Submodule ℤ (Fin n → ℚ)} (hL : IsAStable A L) (y : Fin n → ℚ) :
    Ideal ℤ[X] where
  carrier := {g | actZ A g *ᵥ y ∈ L}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, actZ_add, add_mulVec] at *
    exact add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, actZ_zero, zero_mulVec]
    exact zero_mem _
  smul_mem' := by
    intro c g hg
    simp only [Set.mem_ofPred_eq, smul_eq_mul, actZ_mul, ← mulVec_mulVec] at *
    exact actZ_mulVec_mem hL c hg

end AnnLat

section ShortCol

variable {A : Matrix (Fin n) (Fin n) ℤ} {p : ℕ} [hp : Fact p.Prime]
  (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0)
include hA hn hW

noncomputable def levelCol (Q : Matrix (Fin n) (Fin n) ℚ) (j : Fin n) : Fin n → ℤ :=
  fun i => levelMat Q i j

omit hA hn hW in
theorem intVec_levelCol (Q : Matrix (Fin n) (Fin n) ℚ) (j : Fin n) :
    intVec (levelCol Q j) = ((level Q : ℕ) : ℤ) • (Q *ᵥ intVec (Pi.single j 1)) := by
  funext i
  simp [intVec, levelCol, levelMat_cast, mulVec, dotProduct, Pi.single_apply, zsmul_eq_mul]

omit hA in
theorem aeval_mulVec_levelCol {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : IsMateMatrix A Q)
    (hpℓ : p ∣ level Q) (j : Fin n) :
    aeval (modP p A) (∏ β ∈ Fset A Q p, β ^ mult (redP p A.charpoly) β) *ᵥ
      redVec p (levelCol Q j) = 0 := by
  obtain ⟨hΛ, hΛu, hCΛ, hΛC⟩ := lem_ideals hn hQ
  have hZ := lem_ideals hn (isMateMatrix_one A)
  rw [latOf_one] at hZ
  obtain ⟨hZst, hZu, hCZ, hZC⟩ := hZ
  have hK := one_le_Kexp hW
  obtain ⟨ℓ1, hℓ1⟩ := hpℓ
  set y := Q *ᵥ intVec (Pi.single j 1) with hydef
  have hyΛ : y ∈ latOf Q := mem_latOf.2 ⟨_, rfl⟩
  set u := (ℓ1 : ℤ) • y with hudef
  have huΛ : u ∈ latOf Q := Submodule.smul_mem _ _ hyΛ
  have hpu : (p : ℤ) • u = intVec (levelCol Q j) := by
    rw [intVec_levelCol, hudef, smul_smul, hℓ1]; push_cast; rfl
  have hpuZ : (p : ℤ) • u ∈ latZ n := by rw [hpu]; exact ⟨_, rfl⟩
  obtain ⟨c, N', hcopN, hdec⟩ := exists_pPart_decomp hn hW (A := A) p
  obtain ⟨hupK, hu'N⟩ := hdec u (hΛC huΛ)
  have hw' : (1 - c) • u ∈ latZ n := by
    refine mem_of_isCoprime_smul_mem (a := (p : ℤ)) (b := (N' : ℤ)) ?_ ?_ ?_
    · exact Nat.isCoprime_iff_coprime.2 hcopN
    · rw [smul_comm]; exact Submodule.smul_mem _ _ hpuZ
    · rw [smul_smul]; exact hCZ hu'N
  set up := c • u
  have hupΛ : up ∈ latOf Q := Submodule.smul_mem _ c huΛ
  have hpup : (p : ℤ) • up ∈ latZ n := by
    rw [smul_comm]; exact Submodule.smul_mem _ _ hpuZ
  set gZ := ∏ β ∈ Fset A Q p, liftZ p β ^ mult (redP p A.charpoly) β with hgZ
  have hsum := sum_actZ_idemZ_sub_mem (A := A) (p := p) hK hupK
  have hparts : ∀ β ∈ factorsSet (redP p A.charpoly),
      actZ A gZ *ᵥ (actZ A (idemZ p A.charpoly β (Kexp A)) *ᵥ up) ∈ latZ n := by
    intro β hβ
    set v := actZ A (idemZ p A.charpoly β (Kexp A)) *ᵥ up
    have hv := actZ_idemZ_mem_mPart hβ hK hΛ hupΛ hupK
    by_cases hF : β ∈ Fset A Q p
    ·
      obtain ⟨-, k, -, hk2⟩ := hv
      have hpv : C (p : ℤ) ∈ annLat A hZst v := by
        show actZ A (C (p : ℤ)) *ᵥ (actZ A (idemZ p A.charpoly β (Kexp A)) *ᵥ up) ∈ latZ n
        rw [actZ_C_mulVec, ← mulVec_smul]
        exact actZ_mulVec_mem hZst _ hpup
      have hφv : A.charpoly ∈ annLat A hZst v := by
        show actZ A A.charpoly *ᵥ v ∈ latZ n
        rw [actZ_charpoly, zero_mulVec]; exact zero_mem _
      have hkv : liftZ p β ^ k ∈ annLat A hZst v := hCZ hk2
      have ha := liftZ_pow_mult_mem (charpoly_monic A) hβ k hpv hφv hkv
      have hsplit : gZ = liftZ p β ^ mult (redP p A.charpoly) β *
          ∏ β' ∈ (Fset A Q p).erase β, liftZ p β' ^ mult (redP p A.charpoly) β' := by
        rw [hgZ]
        exact (Finset.mul_prod_erase _ (fun β => liftZ p β ^ mult (redP p A.charpoly) β) hF).symm
      rw [hsplit, mul_comm, actZ_mul, ← mulVec_mulVec]
      exact actZ_mulVec_mem hZst _ ha
    · have heq : mPart A p β (latOf Q) = mPart A p β (latZ n) := by
        by_contra hne; exact hF (mem_Fset.2 ⟨hβ, hne⟩)
      rw [heq] at hv
      exact actZ_mulVec_mem hZst _ hv.1
  have hgu : actZ A gZ *ᵥ u ∈ latZ n := by
    have hsplit : u = (1 - c) • u + (∑ β ∈ factorsSet (redP p A.charpoly),
        actZ A (idemZ p A.charpoly β (Kexp A)) *ᵥ up -
        (∑ β ∈ factorsSet (redP p A.charpoly), actZ A (idemZ p A.charpoly β (Kexp A)) *ᵥ up - up)) := by
      rw [sub_sub_cancel, ← add_smul, sub_add_cancel, one_smul]
    rw [hsplit, mulVec_add, mulVec_sub, Matrix.mulVec_sum]
    refine add_mem (actZ_mulVec_mem hZst _ hw') (sub_mem (sum_mem hparts) ?_)
    exact actZ_mulVec_mem hZst _ (hCZ hsum)
  obtain ⟨d, hd⟩ := hgu
  have h1 : intVec (aeval A gZ *ᵥ levelCol Q j) = intVec ((p : ℤ) • d) := by
    rw [← actZ_mulVec_intVec, ← hpu, mulVec_smul, hd, intVec_smul]
  have h2 := intVec_injective h1
  have hmap : (∏ β ∈ Fset A Q p, β ^ mult (redP p A.charpoly) β) =
      gZ.map (Int.castRingHom (ZMod p)) := by
    rw [hgZ, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun β _ => ?_
    rw [Polynomial.map_pow, map_liftZ]
  rw [hmap, ← redVec_aeval_mulVec, h2, redVec_eq_zero_iff]
  intro i
  rw [Pi.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

omit hA hn hW in
theorem card_levelCol_le {Q : Matrix (Fin n) (Fin n) ℚ} (hQQ : Qᵀ * Q = 1) (j : Fin n) :
    (Finset.univ.filter fun i => redVec p (levelCol Q j) i ≠ 0).card ≤ level Q ^ 2 := by
  classical
  set z := levelCol Q j
  have hnorm : ∑ i, z i ^ 2 = ((level Q : ℕ) : ℤ) ^ 2 := by
    have h1 : ((∑ i, z i ^ 2 : ℤ) : ℚ) = (((level Q : ℕ) : ℤ) : ℚ) ^ 2 := by
      push_cast
      have hjj : ∑ i, Q i j * Q i j = 1 := by
        have := congrFun (congrFun hQQ j) j
        simpa [Matrix.mul_apply] using this
      simp only [z, levelCol, levelMat_cast, mul_pow]
      rw [← Finset.mul_sum]
      simp only [sq] at hjj ⊢
      rw [hjj, mul_one]
    exact_mod_cast h1
  have hsub : (Finset.univ.filter fun i => redVec p z i ≠ 0) ⊆ Finset.univ.filter fun i => z i ≠ 0 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hz
    apply hi
    simp [redVec, hz]
  refine (Finset.card_le_card hsub).trans ?_
  have hcard : ((Finset.univ.filter fun i => z i ≠ 0).card : ℤ) ≤ ∑ i, z i ^ 2 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    calc ∑ i ∈ Finset.univ.filter (fun i => z i ≠ 0), ((1 : ℕ) : ℤ)
        ≤ ∑ i ∈ Finset.univ.filter (fun i => z i ≠ 0), z i ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          push_cast
          exact one_le_sq_iff_one_le_abs _ |>.2 (Int.one_le_abs hi)
      _ ≤ ∑ i, z i ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun i _ _ => sq_nonneg _
  rw [hnorm] at hcard
  exact_mod_cast hcard

omit hA in
theorem lem_shortcol {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : IsMateMatrix A Q) (hpℓ : p ∣ level Q) :
    ∃ j : Fin n, 0 < (Finset.univ.filter fun i => redVec p (levelCol Q j) i ≠ 0).card ∧
      (Finset.univ.filter fun i => redVec p (levelCol Q j) i ≠ 0).card ≤ level Q ^ 2 ∧
      aeval (modP p A) (∏ β ∈ Fset A Q p, β ^ mult (redP p A.charpoly) β) *ᵥ
        redVec p (levelCol Q j) = 0 := by
  classical
  obtain ⟨ℓ1, hℓ1⟩ := hpℓ
  have hℓpos := level_pos Q
  have hℓ1pos : 0 < ℓ1 := by
    rcases Nat.eq_zero_or_pos ℓ1 with h | h
    · rw [h, mul_zero] at hℓ1; omega
    · exact h
  have hnot : ¬ IsIntegralMul ℓ1 Q := by
    intro h
    have := level_le hℓ1pos h
    have hp2 := hp.out.two_le
    rw [hℓ1] at this
    nlinarith
  simp only [IsIntegralMul, not_forall] at hnot
  obtain ⟨i, j, hij⟩ := hnot
  refine ⟨j, ?_, card_levelCol_le hQ.1 j, aeval_mulVec_levelCol hn hW hQ ⟨ℓ1, hℓ1⟩ j⟩
  refine Finset.card_pos.2 ⟨i, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro h0
  apply hij
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨m, ?_⟩
  have h1 : ((levelCol Q j i : ℤ) : ℚ) = (level Q : ℚ) * Q i j := levelMat_cast Q i j
  rw [hm, hℓ1] at h1
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  push_cast at h1
  field_simp at h1 ⊢
  linear_combination -h1

end ShortCol

end DGS
