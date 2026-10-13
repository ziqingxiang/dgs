module

public import DGS.Core.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.Int.Basic

@[expose] public section

open Matrix Polynomial Module

namespace DGS

section DetDvd

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pow_dvd_det_of_le_finrank_ker (N : Matrix ι ι ℤ) {p : ℕ} [hp : Fact p.Prime] {e : ℕ}
    (he : e ≤ finrank (ZMod p) (LinearMap.ker (N.map (Int.castRingHom (ZMod p))).mulVecLin)) :
    (p : ℤ) ^ e ∣ N.det := by
  classical
  set Nb := N.map (Int.castRingHom (ZMod p)) with hNb
  set V := LinearMap.ker Nb.mulVecLin with hV
  obtain ⟨W, hVW⟩ := Submodule.exists_isCompl V
  set d := finrank (ZMod p) V with hd
  let bV : Basis (Fin d) (ZMod p) V := Module.finBasisOfFinrankEq (ZMod p) V rfl
  let bW : Basis (Fin (finrank (ZMod p) W)) (ZMod p) W := Module.finBasis (ZMod p) W
  let b : Basis (Fin d ⊕ Fin (finrank (ZMod p) W)) (ZMod p) (ι → ZMod p) :=
    (bV.prod bW).map (Submodule.prodEquivOfIsCompl V W hVW)
  have hb : ∀ i, b (Sum.inl i) = (bV i : ι → ZMod p) := by
    intro i
    simp [b, Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl', Module.Basis.prod_apply]
  have hcard : Fintype.card (Fin d ⊕ Fin (finrank (ZMod p) W)) = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  let σ : (Fin d ⊕ Fin (finrank (ZMod p) W)) ≃ ι := Fintype.equivOfCardEq hcard
  let b' : Basis ι (ZMod p) (ι → ZMod p) := b.reindex σ
  set Pb : Matrix ι ι (ZMod p) := (Pi.basisFun (ZMod p) ι).toMatrix b' with hPbdef
  have hPb : ∀ r c, Pb r c = b' c r := fun r c => by
    rw [hPbdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hPbdet : Pb.det ≠ 0 := by
    have : Invertible Pb := (Pi.basisFun (ZMod p) ι).invertibleToMatrix b'
    exact (Matrix.isUnit_det_of_invertible Pb).ne_zero
  set P : Matrix ι ι ℤ := Matrix.of fun r c => ((Pb r c).val : ℤ) with hPdef
  have hPmap : P.map (Int.castRingHom (ZMod p)) = Pb := by
    ext r c
    simp [hPdef]
  have hPdvd : ¬ (p : ℤ) ∣ P.det := by
    intro h
    apply hPbdet
    rw [← hPmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
  set J : Finset ι := Finset.univ.image (fun i : Fin d => σ (Sum.inl i)) with hJ
  have hJcard : J.card = d := by
    rw [hJ, Finset.card_image_of_injective _ (fun a b hab => Sum.inl_injective (σ.injective hab)),
      Finset.card_univ, Fintype.card_fin]
  have hcol : ∀ c ∈ J, ∀ r, (p : ℤ) ∣ (N * P) r c := by
    intro c hc r
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h1 : ((N * P) r (σ (Sum.inl i)) : ZMod p) = (Nb * Pb) r (σ (Sum.inl i)) := by
      rw [← hPmap, hNb, ← Matrix.map_mul]
      rfl
    rw [h1]
    have h2 : (fun r => Pb r (σ (Sum.inl i))) = (bV i : ι → ZMod p) := by
      funext r
      rw [hPb, Module.Basis.reindex_apply, Equiv.symm_apply_apply, hb]
    have h3 : Nb *ᵥ (bV i : ι → ZMod p) = 0 := by
      have h := LinearMap.mem_ker.1 (bV i).2
      rwa [mulVecLin_apply] at h
    have h4 : (Nb * Pb) r (σ (Sum.inl i)) = (Nb *ᵥ fun r => Pb r (σ (Sum.inl i))) r := by
      simp [mul_apply, mulVec, dotProduct]
    rw [h4, h2, h3, Pi.zero_apply]
  set M := (N * P)ᵀ with hM
  set Q : Matrix ι ι ℤ := Matrix.of fun c r => if c ∈ J then M c r / p else M c r with hQ
  set v : ι → ℤ := fun c => if c ∈ J then (p : ℤ) else 1 with hv
  have hMQ : M = Matrix.of fun c r => v c * Q c r := by
    ext c r
    simp only [hQ, hv, Matrix.of_apply]
    split_ifs with h
    · rw [Int.mul_ediv_cancel' (by rw [hM, transpose_apply]; exact hcol c h r)]
    · rw [one_mul]
  have hprod : ∏ c, v c = (p : ℤ) ^ J.card := by
    rw [hv, ← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
  have hdet : N.det * P.det = (p : ℤ) ^ d * Q.det := by
    rw [← det_mul, ← det_transpose, ← hM, hMQ, det_mul_column, hprod, hJcard]
  have h1 : (p : ℤ) ^ e ∣ N.det * P.det := by
    rw [hdet]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ he) _
  have hcop : IsCoprime ((p : ℤ) ^ e) P.det :=
    IsCoprime.pow_left ((Int.prime_iff_natAbs_prime.2 (by rw [Int.natAbs_natCast]; exact hp.out)
      ).coprime_iff_not_dvd.2 hPdvd)
  exact hcop.dvd_of_dvd_mul_right h1

end DetDvd

section Sylvester

variable {F : Type*} [Field F]

theorem le_finrank_ker_sylvester {f g h : F[X]} {m n : ℕ} (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hf0 : f ≠ 0) (hhf : h ∣ f) (hhg : h ∣ g) :
    h.natDegree ≤ finrank F (LinearMap.ker (sylvester f g m n).mulVecLin) := by
  classical
  obtain ⟨f1, rfl⟩ := hhf
  obtain ⟨g1, rfl⟩ := hhg
  have hh0 : h ≠ 0 := left_ne_zero_of_mul hf0
  have hf10 : f1 ≠ 0 := right_ne_zero_of_mul hf0
  set e := h.natDegree
  have hdeg1 : ∀ c ∈ degreeLT F e, -(c * f1) ∈ degreeLT F m := by
    intro c hc
    rw [Submodule.neg_mem_iff, mem_degreeLT]
    rw [mem_degreeLT] at hc
    by_cases hc0 : c = 0
    · rw [hc0, zero_mul, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_mul, degree_eq_natDegree hc0, degree_eq_natDegree hf10]
      rw [degree_eq_natDegree hc0] at hc
      have h1 : c.natDegree < e := by exact_mod_cast hc
      have h2 : (h * f1).natDegree = e + f1.natDegree := natDegree_mul hh0 hf10
      have h3 : c.natDegree + f1.natDegree < m := by omega
      exact_mod_cast h3
  have hdeg2 : ∀ c ∈ degreeLT F e, c * g1 ∈ degreeLT F n := by
    intro c hc
    rw [mem_degreeLT]
    rw [mem_degreeLT] at hc
    by_cases hc0 : c = 0
    · rw [hc0, zero_mul, degree_zero]; exact WithBot.bot_lt_coe _
    by_cases hg10 : g1 = 0
    · rw [hg10, mul_zero, degree_zero]; exact WithBot.bot_lt_coe _
    rw [degree_mul, degree_eq_natDegree hc0, degree_eq_natDegree hg10]
    rw [degree_eq_natDegree hc0] at hc
    have h1 : c.natDegree < e := by exact_mod_cast hc
    have h2 : (h * g1).natDegree = e + g1.natDegree := natDegree_mul hh0 hg10
    have h3 : c.natDegree + g1.natDegree < n := by omega
    exact_mod_cast h3
  let φ1 : degreeLT F e →ₗ[F] degreeLT F m :=
    LinearMap.codRestrict (degreeLT F m) (-(LinearMap.mulRight F f1) ∘ₗ (degreeLT F e).subtype)
      (fun c => by simpa using hdeg1 c.1 c.2)
  let φ2 : degreeLT F e →ₗ[F] degreeLT F n :=
    LinearMap.codRestrict (degreeLT F n) (LinearMap.mulRight F g1 ∘ₗ (degreeLT F e).subtype)
      (fun c => by simpa using hdeg2 c.1 c.2)
  let Φ : degreeLT F e →ₗ[F] degreeLT F m × degreeLT F n := φ1.prod φ2
  have hΦ1 : ∀ c, (((Φ c).1 : degreeLT F m) : F[X]) = -((c : F[X]) * f1) := fun c => rfl
  have hΦ2 : ∀ c, (((Φ c).2 : degreeLT F n) : F[X]) = (c : F[X]) * g1 := fun c => rfl
  have hΦ : ∀ c, sylvesterMap (h * f1) (h * g1) hf hg (Φ c) = 0 := by
    intro c
    apply Subtype.ext
    rw [sylvesterMap_apply_coe, hΦ1, hΦ2, ZeroMemClass.coe_zero]
    ring
  have hΦinj : Function.Injective Φ := by
    intro c c' hcc
    have h1 : -((c : F[X]) * f1) = -((c' : F[X]) * f1) := by
      rw [← hΦ1, ← hΦ1, hcc]
    exact Subtype.ext (mul_right_cancel₀ hf10 (neg_inj.1 h1))
  set b1 := ((degreeLT.basis F m).prod (degreeLT.basis F n)).reindex finSumFinEquiv
  set b2 := degreeLT.basis F (m + n)
  let Ψ : degreeLT F e →ₗ[F] (Fin (m + n) → F) := b1.equivFun.toLinearMap ∘ₗ Φ
  have hΨinj : Function.Injective Ψ := b1.equivFun.injective.comp hΦinj
  have hΨker : LinearMap.range Ψ ≤ LinearMap.ker (sylvester (h * f1) (h * g1) m n).mulVecLin := by
    rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, ← toMatrix_sylvesterMap' (h * f1) (h * g1) hf hg]
    have := LinearMap.toMatrix_mulVec_repr b1 b2 (sylvesterMap (h * f1) (h * g1) hf hg) (Φ c)
    simp only [Ψ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Module.Basis.equivFun_apply]
    rw [this, hΦ, map_zero]
    rfl
  have h1 := Submodule.finrank_mono hΨker
  rw [LinearMap.finrank_range_of_inj hΨinj, (degreeLTEquiv F e).finrank_eq,
    Module.finrank_fin_fun] at h1
  exact h1

end Sylvester

section PartA

theorem isCoprime_of_monic_irreducible {F : Type*} [Field F] {β β' : F[X]} (hβ : β.Monic)
    (hβi : Irreducible β) (hβ' : β'.Monic) (hβ'i : Irreducible β') (hne : β ≠ β') : IsCoprime β β' := by
  rw [Irreducible.coprime_iff_not_dvd hβi]
  intro hd
  exact hne (eq_of_monic_of_associated hβ hβ' (hβi.associated_of_dvd hβ'i hd))

theorem pow_dvd_discr {χ : ℤ[X]} (hχ : χ.Monic) {p : ℕ} [hp : Fact p.Prime]
    (B : Finset (ZMod p)[X])
    (hB : ∀ β ∈ B, β.Monic ∧ Irreducible β ∧ β ^ 2 ∣ χ.map (Int.castRingHom (ZMod p))) :
    (p : ℤ) ^ (∑ β ∈ B, β.natDegree) ∣ χ.discr := by
  classical
  set φ := Int.castRingHom (ZMod p)
  set f := χ.map φ with hfdef
  have hfm : f.Monic := hχ.map φ
  have hfdeg : f.natDegree = χ.natDegree := hχ.natDegree_map φ
  by_cases hm : χ.natDegree = 0
  · have hB0 : B = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro β hβ
      obtain ⟨hβm, hβi, hdvd⟩ := hB β hβ
      have hf1 : f = 1 := eq_one_of_monic_natDegree_zero hfm (by rw [hfdeg, hm])
      rw [hf1] at hdvd
      exact hβi.not_isUnit (isUnit_of_dvd_one ((dvd_pow_self β two_ne_zero).trans hdvd))
    rw [hB0, Finset.sum_empty, pow_zero]
    exact one_dvd _
  set m := χ.natDegree with hmdef
  set h := ∏ β ∈ B, β with hhdef
  have hpair : (B : Set (ZMod p)[X]).Pairwise (Function.onFun IsCoprime id) := by
    intro β hβ β' hβ' hne
    exact isCoprime_of_monic_irreducible (hB β hβ).1 (hB β hβ).2.1 (hB β' hβ').1 (hB β' hβ').2.1 hne
  have hhf : h ∣ f := Finset.prod_dvd_of_coprime hpair fun β hβ =>
    (dvd_pow_self β two_ne_zero).trans (hB β hβ).2.2
  have hhg : h ∣ derivative f := Finset.prod_dvd_of_coprime hpair fun β hβ => by
    have := pow_sub_one_dvd_derivative_of_pow_dvd (hB β hβ).2.2
    simpa using this
  have hhdeg : h.natDegree = ∑ β ∈ B, β.natDegree :=
    natDegree_prod _ _ fun β hβ => (hB β hβ).1.ne_zero
  have hker := le_finrank_ker_sylvester (f := f) (g := derivative f) (m := m) (n := m - 1)
    (by rw [hfdeg]) (by rw [← hfdeg]; exact natDegree_derivative_le f) hfm.ne_zero hhf hhg
  have hsyl : sylvester f (derivative f) m (m - 1) =
      (sylvester χ (derivative χ) m (m - 1)).map φ := by
    rw [hfdef, derivative_map, sylvester_map_map]
    rfl
  rw [hsyl, hhdeg] at hker
  have hres := pow_dvd_det_of_le_finrank_ker (sylvester χ (derivative χ) m (m - 1)) hker
  have hdeg : 0 < χ.degree := by
    rw [degree_eq_natDegree hχ.ne_zero]
    exact_mod_cast Nat.pos_of_ne_zero hm
  have hrd := resultant_deriv hdeg
  rw [hχ.leadingCoeff, mul_one] at hrd
  have h2 : (p : ℤ) ^ (∑ β ∈ B, β.natDegree) ∣
      (-1) ^ (χ.natDegree * (χ.natDegree - 1) / 2) * χ.discr := by
    rw [← hrd]
    exact hres
  exact (((isUnit_neg_one (α := ℤ)).pow _).dvd_mul_left).1 h2

theorem lem_budget_a {m : ℕ} (T : Matrix (Fin m) (Fin m) ℤ) {p : ℕ} [Fact p.Prime]
    (B : Finset (ZMod p)[X]) (hB : ∀ β ∈ B, IsRepeatedFactor p T β) :
    (p : ℤ) ^ (∑ β ∈ B, β.natDegree) ∣ T.charpoly.discr := by
  refine pow_dvd_discr (charpoly_monic T) B fun β hβ => ⟨(hB β hβ).1, (hB β hβ).2.1, ?_⟩
  have := (hB β hβ).2.2
  rwa [modP, charpoly_map] at this

end PartA

section PartB

variable {m : ℕ}

theorem abs_multiset_prod_le (s : Multiset ℝ) {c : ℝ} (hc : 0 ≤ c) (h : ∀ y ∈ s, |y| ≤ c) :
    |s.prod| ≤ c ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, abs_mul, Multiset.card_cons, pow_succ]
    have ha := h a (Multiset.mem_cons_self a s)
    have hs := ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
    calc |a| * |s.prod| ≤ c * c ^ Multiset.card s := mul_le_mul ha hs (abs_nonneg _) hc
      _ = c ^ Multiset.card s * c := mul_comm _ _

theorem abs_eigenvalue_le {A : Matrix (Fin m) (Fin m) ℝ} (hA : ∀ i j, |A i j| ≤ 1) {μ : ℝ}
    {v : Fin m → ℝ} (hv0 : v ≠ 0) (hv : A *ᵥ v = μ • v) : |μ| ≤ m := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    obtain ⟨i, -⟩ := Function.ne_iff.1 hv0
    exact ⟨i, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|) hne
  have hvj : 0 < |v j| := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
    exact lt_of_lt_of_le (abs_pos.2 hi) (hj i (Finset.mem_univ _))
  have h1 : |μ| * |v j| ≤ m * |v j| := by
    have h2 : μ * v j = ∑ k, A j k * v k := by
      have := congrFun hv j
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      exact this.symm
    rw [← abs_mul, h2]
    calc |∑ k, A j k * v k| ≤ ∑ k, |A j k * v k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin m, |v j| := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          calc |A j k| * |v k| ≤ 1 * |v j| :=
                mul_le_mul (hA j k) (hj k (Finset.mem_univ _)) (abs_nonneg _) zero_le_one
            _ = |v j| := one_mul _
      _ = m * |v j| := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_of_mul_le_mul_right h1 hvj

theorem abs_discr_le {T : Matrix (Fin m) (Fin m) ℤ} (hT : T.IsSymm) (hT1 : ∀ i j, |T i j| ≤ 1) :
    |T.charpoly.discr| ≤ (2 * m : ℤ) ^ (m * (m - 1)) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [charpoly_isEmpty, ← C_1, discr_C]
    simp
  set χ := T.charpoly with hχdef
  have hχm : χ.Monic := charpoly_monic T
  have hχdeg : χ.natDegree = m := by rw [hχdef, charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdeg : 0 < χ.degree := by
    rw [degree_eq_natDegree hχm.ne_zero, hχdeg]
    exact_mod_cast hm
  have hrd := resultant_deriv hdeg
  rw [hχm.leadingCoeff, mul_one, hχdeg] at hrd
  set A := T.map (Int.castRingHom ℝ) with hAdef
  have hAh : A.IsHermitian := by
    rw [isHermitian_iff_isSymm]
    exact Matrix.IsSymm.ext fun i j => by simp [hAdef, hT.apply j i]
  have hA1 : ∀ i j, |A i j| ≤ 1 := fun i j => by
    simp only [hAdef, map_apply, eq_intCast]
    exact_mod_cast hT1 i j
  set χR := A.charpoly with hχR
  have hχRmap : χR = χ.map (Int.castRingHom ℝ) := by rw [hχR, hAdef, charpoly_map]
  have hsplit : χR.Splits := hAh.splits_charpoly
  have hχRm : χR.Monic := charpoly_monic A
  have hχRdeg : χR.natDegree = m := by rw [hχR, charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hres : ((χ.resultant (derivative χ) m (m - 1) : ℤ) : ℝ) =
      (χR.roots.map fun x => eval x (derivative χR)).prod := by
    have h1 := resultant_map_map χ (derivative χ) m (m - 1) (Int.castRingHom ℝ)
    rw [← derivative_map, ← hχRmap] at h1
    rw [eq_intCast] at h1
    rw [← h1]
    have h2 := resultant_eq_prod_eval χR (derivative χR) (m - 1)
      (by rw [← hχRdeg]; exact natDegree_derivative_le _) hsplit
    rw [hχRdeg, hχRm.leadingCoeff, one_pow, one_mul] at h2
    exact h2
  have hroot : ∀ x ∈ χR.roots, |x| ≤ m := by
    intro x hx
    have hx' : (LinearMap.charpoly (toLin' A)).IsRoot x := by
      rw [charpoly_toLin', ← hχR]
      exact (mem_roots hχRm.ne_zero).1 hx
    obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 hx').exists_hasEigenvector
    have hv1 := hv.apply_eq_smul
    rw [toLin'_apply] at hv1
    exact abs_eigenvalue_le hA1 hv.2 hv1
  have hcard : χR.roots.card = m := by rw [← hsplit.natDegree_eq_card_roots, hχRdeg]
  have h2m : (0 : ℝ) ≤ 2 * m := by positivity
  have hterm : ∀ x ∈ χR.roots, |eval x (derivative χR)| ≤ (2 * m : ℝ) ^ (m - 1) := by
    intro x hx
    rw [hsplit.eval_root_derivative hχRm hx]
    have hcard' : Multiset.card ((χR.roots.erase x).map fun y => x - y) = m - 1 := by
      rw [Multiset.card_map, Multiset.card_erase_of_mem hx, hcard, Nat.pred_eq_sub_one]
    rw [← hcard']
    refine abs_multiset_prod_le _ h2m fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    have hx1 := hroot x hx
    have hy1 := hroot y (Multiset.mem_of_mem_erase hy)
    calc |x - y| ≤ |x| + |y| := abs_sub _ _
      _ ≤ m + m := add_le_add hx1 hy1
      _ = 2 * m := by ring
  have htot : |(χR.roots.map fun x => eval x (derivative χR)).prod| ≤
      ((2 * m : ℝ) ^ (m - 1)) ^ m := by
    have := abs_multiset_prod_le (χR.roots.map fun x => eval x (derivative χR))
      (pow_nonneg h2m (m - 1)) fun z hz => by
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
        exact hterm x hx
    rwa [Multiset.card_map, hcard] at this
  have habs : |(χ.discr : ℝ)| = |((χ.resultant (derivative χ) m (m - 1) : ℤ) : ℝ)| := by
    rw [hrd]
    push_cast
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hfin : |(χ.discr : ℝ)| ≤ (2 * m : ℝ) ^ (m * (m - 1)) := by
    rw [habs, hres, show m * (m - 1) = (m - 1) * m by ring, pow_mul]
    exact htot
  have : ((|χ.discr| : ℤ) : ℝ) ≤ (((2 * m : ℤ) ^ (m * (m - 1)) : ℤ) : ℝ) := by
    push_cast
    exact hfin
  exact_mod_cast this

theorem lem_budget_b {T : Matrix (Fin m) (Fin m) ℤ} (hT : T.IsSymm) (hT1 : ∀ i j, |T i j| ≤ 1)
    (hΔ : T.charpoly.discr ≠ 0) {P : ℝ} (hP : 2 ≤ P) (X : Finset (Σ p : ℕ, (ZMod p)[X]))
    (hX : ∀ x ∈ X, x.1.Prime ∧ P < x.1 ∧ IsRepeatedFactor x.1 T x.2) :
    (X.card : ℝ) ≤ (m : ℝ) ^ 2 * Real.log (2 * m) / Real.log P := by
  classical
  set Ps := X.image Sigma.fst with hPs
  obtain ⟨B, hBmem⟩ : ∃ B : ∀ p : ℕ, Finset (ZMod p)[X],
      ∀ p β, β ∈ B p ↔ (⟨p, β⟩ : Σ p : ℕ, (ZMod p)[X]) ∈ X :=
    ⟨fun p => X.preimage (fun β : (ZMod p)[X] => (⟨p, β⟩ : Σ p : ℕ, (ZMod p)[X]))
      (fun a _ b _ h => by simpa using h), fun p β => Finset.mem_preimage⟩
  have hsub : X ⊆ Ps.sigma B := by
    rintro ⟨p, β⟩ hx
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_image_of_mem _ hx, (hBmem p β).2 hx⟩
  have hPpos : 0 < Real.log P := Real.log_pos (by linarith)
  have hprime : ∀ p ∈ Ps, p.Prime ∧ P < p := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨(hX x hx).1, (hX x hx).2.1⟩
  have hrep : ∀ p ∈ Ps, ∀ β ∈ B p, IsRepeatedFactor p T β := by
    intro p _ β hβ
    exact (hX _ ((hBmem p β).1 hβ)).2.2
  set r : ℕ → ℕ := fun p => ∑ β ∈ B p, β.natDegree with hr
  have hcardB : ∀ p ∈ Ps, (B p).card ≤ r p := by
    intro p hp
    have : Fact p.Prime := ⟨(hprime p hp).1⟩
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun β hβ => (hrep p hp β hβ).2.1.natDegree_pos
  have hdvd : ∏ p ∈ Ps, (p : ℤ) ^ r p ∣ T.charpoly.discr := by
    refine Finset.prod_dvd_of_coprime ?_ fun p hp => ?_
    · intro p hp q hq hne
      have h1 : Nat.Coprime p q := (Nat.coprime_primes (hprime p hp).1 (hprime q hq).1).2 hne
      have h2 := Nat.isCoprime_iff_coprime.2 (h1.pow (r p) (r q))
      simpa [Function.onFun] using h2
    · have : Fact p.Prime := ⟨(hprime p hp).1⟩
      exact lem_budget_a T (B p) (hrep p hp)
  have hle : (∏ p ∈ Ps, (p : ℝ) ^ r p) ≤ (2 * m : ℝ) ^ (m * (m - 1)) := by
    have h1 : ∏ p ∈ Ps, (p : ℤ) ^ r p ≤ |T.charpoly.discr| :=
      Int.le_of_dvd (abs_pos.2 hΔ) ((dvd_abs _ _).2 hdvd)
    have h2 := abs_discr_le hT hT1
    have h3 : ((∏ p ∈ Ps, (p : ℤ) ^ r p : ℤ) : ℝ) ≤ (((2 * m : ℤ) ^ (m * (m - 1)) : ℤ) : ℝ) := by
      exact_mod_cast h1.trans h2
    push_cast at h3
    exact h3
  have hlog : ∑ p ∈ Ps, (r p : ℝ) * Real.log p ≤ (m * (m - 1) : ℕ) * Real.log (2 * m) := by
    have hpos : ∀ p ∈ Ps, (0 : ℝ) < (p : ℝ) ^ r p := fun p hp => by
      have := (hprime p hp).1.pos
      positivity
    have h1 : Real.log (∏ p ∈ Ps, (p : ℝ) ^ r p) = ∑ p ∈ Ps, (r p : ℝ) * Real.log p := by
      rw [Real.log_prod (fun p hp => (hpos p hp).ne')]
      exact Finset.sum_congr rfl fun p _ => Real.log_pow _ _
    rw [← h1, ← Real.log_pow]
    exact Real.log_le_log (Finset.prod_pos hpos) hle
  have hsum : (∑ p ∈ Ps, (r p : ℝ)) * Real.log P ≤ (m * (m - 1) : ℕ) * Real.log (2 * m) := by
    refine le_trans ?_ hlog
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (hprime p hp).2.le) (Nat.cast_nonneg _)
  have hm2 : ((m * (m - 1) : ℕ) : ℝ) * Real.log (2 * m) ≤ (m : ℝ) ^ 2 * Real.log (2 * m) := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp
    · have hl : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ m := by exact_mod_cast h0
        linarith)
      apply mul_le_mul_of_nonneg_right _ hl
      have : m * (m - 1) ≤ m ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      exact_mod_cast this
  rw [le_div_iff₀ hPpos]
  calc (X.card : ℝ) * Real.log P ≤ (∑ p ∈ Ps, (r p : ℝ)) * Real.log P := by
        apply mul_le_mul_of_nonneg_right _ hPpos.le
        have h1 : X.card ≤ ∑ p ∈ Ps, r p := by
          calc X.card ≤ (Ps.sigma B).card := Finset.card_le_card hsub
            _ = ∑ p ∈ Ps, (B p).card := Finset.card_sigma _ _
            _ ≤ ∑ p ∈ Ps, r p := Finset.sum_le_sum hcardB
        exact_mod_cast h1
    _ ≤ (m * (m - 1) : ℕ) * Real.log (2 * m) := hsum
    _ ≤ (m : ℝ) ^ 2 * Real.log (2 * m) := hm2

end PartB

end DGS
