module

public import DGS.Ext.Cyclic.Bound
public import DGS.Ext.Cyclic.Krylov

@[expose] public section

open Matrix Polynomial Module Filter Topology

namespace DGS

section Real

variable {k : ℕ}

theorem exists_sq_dvd_charpoly_of_discr {A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (hA : A.IsHermitian)
    (h : A.charpoly.discr = 0) : ∃ x : ℝ, (X - C x) ^ 2 ∣ A.charpoly := by
  set χ := A.charpoly with hχdef
  have hχm : χ.Monic := charpoly_monic A
  have hχdeg : χ.natDegree = k + 1 := by rw [hχdef, charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdeg : 0 < χ.degree := by
    rw [degree_eq_natDegree hχm.ne_zero, hχdeg]
    exact_mod_cast Nat.succ_pos k
  have hsplit : χ.Splits := hA.splits_charpoly
  have hrd := resultant_deriv hdeg
  rw [hχm.leadingCoeff, mul_one, h, mul_zero, hχdeg] at hrd
  have h2 := resultant_eq_prod_eval χ (derivative χ) (k + 1 - 1)
    (by rw [← hχdeg]; exact natDegree_derivative_le _) hsplit
  rw [hχdeg, hχm.leadingCoeff, one_pow, one_mul, hrd] at h2
  obtain ⟨y, hy, hy0⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 h2.symm)
  refine ⟨y, ?_⟩
  have hroot : χ.IsRoot y := (mem_roots hχm.ne_zero).1 hy
  have h1 : 1 < χ.rootMultiplicity y := (one_lt_rootMultiplicity_iff_isRoot hχm.ne_zero).2 ⟨hroot, hy0⟩
  exact (le_rootMultiplicity_iff hχm.ne_zero).1 (by omega)

theorem two_le_corank_of_sq_dvd {A : Matrix (Fin k) (Fin k) ℝ} (hA : Aᵀ = A) {x : ℝ}
    (h : (X - C x) ^ 2 ∣ A.charpoly) : 2 ≤ corank (A - x • 1) := by
  have hE : Module.End.eigenspace (toLin' A) x = LinearMap.ker (A - x • 1).mulVecLin := by
    ext w
    rw [Module.End.mem_eigenspace_iff, toLin'_apply, LinearMap.mem_ker, mulVecLin_apply, sub_mulVec,
      smul_mulVec, one_mulVec, sub_eq_zero]
  rcases (sq_dvd_charpoly_iff A hA x).1 h with h2 | ⟨h1, hiso⟩
  · rw [hE] at h2
    exact h2
  · exfalso
    obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_finrank_pos (K := Module.End.eigenspace (toLin' A) x) (by omega)
    exact hw0 (dotProduct_self_eq_zero.1 (hiso w hw))

theorem exists_ker_delMat_perp {B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (hB : Bᵀ = B) (h2 : 2 ≤ corank B) :
    ∃ v : Fin k → ℝ, v ≠ 0 ∧ delMat B (Fin.last k) *ᵥ v = 0 ∧ delCol B (Fin.last k) ⬝ᵥ v = 0 := by
  by_cases hi : ∃ w ∈ LinearMap.ker B.mulVecLin, w (Fin.last k) ≠ 0
  · obtain ⟨hdim, horth, -⟩ := lem_delete hB (Fin.last k) hi
    obtain ⟨v, hv, hv0⟩ := exists_ne_zero_of_finrank_pos
      (K := LinearMap.ker (delMat B (Fin.last k)).mulVecLin) (by unfold corank at hdim h2; omega)
    exact ⟨v, hv0, mem_ker_mulVecLin.1 hv, horth v hv⟩
  · push Not at hi
    obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_finrank_pos (K := LinearMap.ker B.mulVecLin)
      (by unfold corank at h2; omega)
    have hwl := hi w hw
    have hBw := mem_ker_mulVecLin.1 hw
    refine ⟨fun l => w ((Fin.last k).succAbove l), ?_, ?_, ?_⟩
    · intro h0
      apply hw0
      funext i
      refine Fin.lastCases ?_ (fun l => ?_) i
      · exact hwl
      · have := congrFun h0 l
        simpa [Fin.succAbove_last] using this
    · funext j
      have h1 := mulVec_succAbove B (Fin.last k) w j
      rw [hBw, hwl, mul_zero, add_zero, Pi.zero_apply] at h1
      exact h1.symm
    · have h1 := mulVec_self_of_symm hB (Fin.last k) w
      rw [hBw, hwl, mul_zero, add_zero, Pi.zero_apply] at h1
      exact h1.symm

end Real

theorem notCyc_of_discr_eq_zero {k : ℕ} {S : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ} (hS : S.IsSymm)
    (h : S.charpoly.discr = 0) (p : ℕ) [Fact p.Prime] :
    NotCyc p (delMat S (Fin.last k)) (delCol S (Fin.last k)) := by
  set A := S.map (Int.castRingHom ℝ) with hAdef
  have hAs : Aᵀ = A := by rw [hAdef, ← transpose_map, hS.eq]
  have hAh : A.IsHermitian := by
    rw [isHermitian_iff_isSymm]
    exact hAs
  have hΔ : A.charpoly.discr = 0 := by
    have hres : ∀ {R : Type} [CommRing R] (f : R[X]), 0 < f.degree → f.Monic → (f.discr = 0 ↔
        resultant f (derivative f) f.natDegree (f.natDegree - 1) = 0) := by
      intro R _ f hf hfm
      rw [resultant_deriv hf, hfm.leadingCoeff, mul_one]
      constructor
      · intro h0; rw [h0, mul_zero]
      · intro h0
        exact (((isUnit_neg_one (α := R)).pow _).mul_right_eq_zero).1 h0
    have hχm : S.charpoly.Monic := charpoly_monic S
    have hχdeg : S.charpoly.natDegree = k + 1 := by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hdegS : 0 < S.charpoly.degree := by
      rw [degree_eq_natDegree hχm.ne_zero, hχdeg]; exact_mod_cast Nat.succ_pos k
    have hAχ : A.charpoly = S.charpoly.map (Int.castRingHom ℝ) := by rw [hAdef, charpoly_map]
    have hAm : A.charpoly.Monic := charpoly_monic A
    have hAdeg : A.charpoly.natDegree = k + 1 := by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hdegA : 0 < A.charpoly.degree := by
      rw [degree_eq_natDegree hAm.ne_zero, hAdeg]; exact_mod_cast Nat.succ_pos k
    rw [hres _ hdegA hAm, hAdeg, hAχ, derivative_map, resultant_map_map]
    rw [hres _ hdegS hχm, hχdeg] at h
    rw [h, map_zero]
  obtain ⟨x, hx⟩ := exists_sq_dvd_charpoly_of_discr hAh hΔ
  have h2 := two_le_corank_of_sq_dvd hAs hx
  have hBs : (A - x • 1)ᵀ = A - x • 1 := by rw [transpose_sub, transpose_smul, transpose_one, hAs]
  obtain ⟨v, hv0, hker, horth⟩ := exists_ker_delMat_perp hBs h2
  set T := delMat S (Fin.last k) with hTdef
  set s := delCol S (Fin.last k) with hsdef
  have hTA : delMat A (Fin.last k) = T.map (Int.castRingHom ℝ) := by rw [hAdef, delMat_map]
  have hsA : delCol A (Fin.last k) = fun j => ((s j : ℤ) : ℝ) := by
    rw [hAdef, delCol_map]
    rfl
  have hTv : T.map (Int.castRingHom ℝ) *ᵥ v = x • v := by
    rw [delMat_sub_smul_one, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero, hTA] at hker
    exact hker
  have hsv : (fun j => ((s j : ℤ) : ℝ)) ⬝ᵥ v = 0 := by
    rw [delCol_sub_smul_one, hsA] at horth
    exact horth
  have hTsymm : (T.map (Int.castRingHom ℝ))ᵀ = T.map (Int.castRingHom ℝ) := by
    rw [← hTA, delMat_transpose, hAs]
  have hK : (krylovMat (T.map (Int.castRingHom ℝ)) (fun j => ((s j : ℤ) : ℝ))).det = 0 := by
    refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨v, hv0, ?_⟩
    funext j
    have hpow : ∀ n : ℕ, (T.map (Int.castRingHom ℝ)) ^ n *ᵥ v = x ^ n • v := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero, one_mulVec, one_smul]
      | succ n ih =>
        rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hTv, smul_smul, pow_succ]
    have hsym : ∀ n : ℕ, ((T.map (Int.castRingHom ℝ)) ^ n)ᵀ = (T.map (Int.castRingHom ℝ)) ^ n := by
      intro n
      rw [transpose_pow, hTsymm]
    have e : (v ᵥ* krylovMat (T.map (Int.castRingHom ℝ)) (fun j => ((s j : ℤ) : ℝ))) j =
        v ⬝ᵥ ((T.map (Int.castRingHom ℝ)) ^ (j : ℕ) *ᵥ fun j => ((s j : ℤ) : ℝ)) := by
      simp [vecMul, dotProduct, krylovMat]
    rw [e, dotProduct_mulVec, ← mulVec_transpose, hsym, hpow, dotProduct_comm, dotProduct_smul, hsv,
      smul_zero, Pi.zero_apply]
  have hKZ : (krylovMat T s).det = 0 := by
    have h1 := RingHom.map_det (Int.castRingHom ℝ) (krylovMat T s)
    rw [RingHom.mapMatrix_apply, krylovMat_map] at h1
    have h2 : ((krylovMat T s).det : ℝ) = 0 := h1.trans hK
    exact_mod_cast h2
  have hKp : (krylovMat (modP p T) (modPVec p s)).det = 0 := by
    have := RingHom.map_det (Int.castRingHom (ZMod p)) (krylovMat T s)
    rw [RingHom.mapMatrix_apply, krylovMat_map, hKZ, map_zero] at this
    exact this.symm
  have hTp : (modP p T)ᵀ = modP p T := (modP_isSymm p (delMat_isSymm hS (Fin.last k))).eq
  obtain ⟨U, hU, hUs⟩ := exists_simple_perp_of_det_eq_zero hTp hKp
  exact ⟨U, hU, hUs⟩

theorem ext_tao_vu : TaoVuStatement := by
  unfold TaoVuStatement
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_prob_notCyc
    (fun _ => prob_nonneg _) fun N => ?_
  obtain ⟨hp, -, -⟩ := corePrime_spec N
  have : Fact (corePrime N).Prime := ⟨hp⟩
  calc probSeidel (N + 1) (fun S => S.charpoly.discr = 0)
      ≤ prob (fun ω : Pairs (N + 1) → Bool => NotCyc (corePrime N) (delMat (seidelOf ω) (Fin.last N))
          (delCol (seidelOf ω) (Fin.last N))) :=
        prob_mono fun ω h => notCyc_of_discr_eq_zero (isSeidel_seidelOf ω).1 h _
    _ = prob (fun x : (Pairs N → Bool) × (Fin N → Bool) =>
          NotCyc (corePrime N) (seidelOf x.1) (signVec x.2)) := lem_exch_law (NotCyc (corePrime N))

end DGS
