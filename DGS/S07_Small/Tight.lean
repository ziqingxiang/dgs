module

public import DGS.S07_Small.FirstMoment

@[expose] public section

open Matrix Polynomial Filter Topology Module

namespace DGS

section Primary

variable {F : Type*} [Field F]

theorem det_aeval_eq_zero_of_dvd_charpoly {m : ℕ} (M : Matrix (Fin m) (Fin m) F) {β : F[X]}
    (hβ : Irreducible β) (hdvd : β ∣ M.charpoly) : (aeval M β).det = 0 := by
  have : Fact (Irreducible β) := ⟨hβ⟩
  set μ : AdjoinRoot β := AdjoinRoot.root β with hμ
  have hμβ : aeval μ β = 0 := by rw [hμ, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  set ML := M.map (algebraMap F (AdjoinRoot β)) with hML
  have hχ : ML.charpoly.eval μ = 0 := by
    rw [hML, Matrix.charpoly_map, Polynomial.eval_map_algebraMap]
    obtain ⟨g, hg⟩ := hdvd
    rw [hg, map_mul, hμβ, zero_mul]
  rw [Matrix.eval_charpoly] at hχ
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hχ
  have hev : ML *ᵥ w = μ • w := by
    rw [sub_mulVec, sub_eq_zero] at hw
    rw [← hw]
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have h2 := aeval_mulVec_of_eigen hev β
  rw [hμβ, zero_smul, hML, aeval_map_matrix] at h2
  have h3 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw0, h2⟩
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h3
  exact (map_eq_zero_iff _ (algebraMap F (AdjoinRoot β)).injective).1 h3

variable {V : Type*} [AddCommGroup V] [Module F V]

theorem pow_restrict_coe (f : Module.End F V) {W : Submodule F V} (hW : ∀ x ∈ W, f x ∈ W)
    (m : ℕ) (x : W) : (((f.restrict hW) ^ m) x : V) = (f ^ m) x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, pow_succ',
      Module.End.mul_apply]

theorem aeval_restrict_coe (f : Module.End F V) {W : Submodule F V} (hW : ∀ x ∈ W, f x ∈ W)
    (g : F[X]) (x : W) : ((aeval (f.restrict hW) g) x : V) = aeval f g x := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial m a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul, pow_restrict_coe]

theorem ker_pow_mono (N : Module.End F V) {a b : ℕ} (hab : a ≤ b) :
    LinearMap.ker (N ^ a) ≤ LinearMap.ker (N ^ b) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [add_comm, pow_add, Module.End.mul_apply, hx, map_zero]

variable [FiniteDimensional F V]

theorem not_injective_aeval_of_dvd_charpoly (f : Module.End F V) {β : F[X]} (hβ : Irreducible β)
    (hdvd : β ∣ f.charpoly) : ¬ Function.Injective (aeval f β) := by
  intro hinj
  set b := Module.finBasis F V
  have hχ : (LinearMap.toMatrix b b f).charpoly = f.charpoly := LinearMap.charpoly_toMatrix f b
  have hdet := det_aeval_eq_zero_of_dvd_charpoly (LinearMap.toMatrix b b f) hβ
    (by rw [hχ]; exact hdvd)
  have e : ∀ g : Module.End F V, LinearMap.toMatrix b b g = LinearMap.toMatrixAlgEquiv b g := by
    intro g; ext i j; rw [LinearMap.toMatrix_apply, LinearMap.toMatrixAlgEquiv_apply]
  have hA : aeval (LinearMap.toMatrix b b f) β = LinearMap.toMatrix b b (aeval f β) := by
    rw [e, e]
    exact aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b) f β
  rw [hA, LinearMap.det_toMatrix] at hdet
  have hiff := (LinearMap.not_hasEigenvalue_zero_tfae (aeval f β)).out 4 6
  exact hiff.2 (fun x hx => hinj (by rw [hx, map_zero])) hdet

theorem exists_finrank_ker_ge (f : Module.End F V) {β : F[X]} (hβ : Irreducible β) {k : ℕ}
    (hdvd : β ^ k ∣ f.charpoly) :
    ∃ m, k * β.natDegree ≤ finrank F (LinearMap.ker (aeval f β ^ m)) := by
  set N := aeval f β with hN
  obtain ⟨m, hm, hm1⟩ :=
    ((N.eventually_isCompl_ker_pow_range_pow).and (eventually_ge_atTop 1)).exists
  refine ⟨m, ?_⟩
  set P := LinearMap.ker (N ^ m) with hP
  set W := LinearMap.range (N ^ m) with hW
  have hcomm : Commute f (N ^ m) := (Commute.pow_right (aeval_mul_comm f β).symm m)
  have hcommx : ∀ y, (N ^ m) (f y) = f ((N ^ m) y) := by
    intro y
    have h := LinearMap.congr_fun hcomm.eq y
    simp only [Module.End.mul_apply] at h
    exact h.symm
  have hfP : ∀ x ∈ P, f x ∈ P := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hcommx, hx, map_zero]
  have hfW : ∀ x ∈ W, f x ∈ W := by
    rintro _ ⟨y, rfl⟩
    exact ⟨f y, hcommx y⟩
  set FP := f.restrict hfP with hFP
  set FW := f.restrict hfW with hFW
  set e := Submodule.prodEquivOfIsCompl P W hm with he
  have hψ : FP.prodMap FW = e.symm.conj f := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply, LinearEquiv.symm_symm, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.eq_symm_apply,
      Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', LinearMap.prodMap_apply,
      LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply, map_add]
  have hχ : f.charpoly = FP.charpoly * FW.charpoly := by
    rw [← e.symm.charpoly_conj f, ← hψ, LinearMap.charpoly_prodMap]
  have hinjW : Function.Injective (aeval FW β) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : N (x : V) = 0 := by
      rw [hN, ← aeval_restrict_coe f hfW β x, hx]; rfl
    have h2 : (x : V) ∈ P := by
      rw [hP, LinearMap.mem_ker]
      obtain ⟨t, ht⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
      rw [ht, pow_succ, Module.End.mul_apply, h1, map_zero]
    have h3 : (x : V) ∈ P ⊓ W := ⟨h2, x.2⟩
    rw [hm.inf_eq_bot, Submodule.mem_bot] at h3
    exact Subtype.ext h3
  have hndvd : ¬ β ∣ FW.charpoly := fun h => not_injective_aeval_of_dvd_charpoly FW hβ h hinjW
  have hcop : IsCoprime (β ^ k) FW.charpoly :=
    ((Irreducible.coprime_iff_not_dvd hβ).2 hndvd).pow_left
  have hdvdP : β ^ k ∣ FP.charpoly := hcop.dvd_of_dvd_mul_right (by rw [← hχ]; exact hdvd)
  calc k * β.natDegree = (β ^ k).natDegree := (natDegree_pow β k).symm
    _ ≤ FP.charpoly.natDegree := natDegree_le_of_dvd hdvdP (LinearMap.charpoly_monic FP).ne_zero
    _ = finrank F P := LinearMap.charpoly_natDegree FP

end Primary

theorem sum_C_mul_X_pow_ne_zero {F : Type*} [Field F] {d : ℕ} {c : Fin d → F} (hc : c ≠ 0) :
    ∑ j : Fin d, C (c j) * X ^ (j : ℕ) ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h; push Not at h; exact hc (funext h)
  intro h
  apply hj
  have h1 := congrArg (fun f => f.coeff j) h
  simp only [Polynomial.finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at h1
  rw [Finset.sum_eq_single j] at h1
  · simpa using h1
  · intro b _ hb
    have : (j : ℕ) ≠ (b : ℕ) := fun h' => hb (Fin.ext h').symm
    simp [this]
  · simp

section Chain

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem finrank_ker_succ_ge (f : Module.End F V) {β : F[X]} (hβ : Irreducible β) {j : ℕ}
    (hne : LinearMap.ker (aeval f β ^ j) ≠ LinearMap.ker (aeval f β ^ (j + 1))) :
    finrank F (LinearMap.ker (aeval f β ^ j)) + β.natDegree ≤
      finrank F (LinearMap.ker (aeval f β ^ (j + 1))) := by
  set d := β.natDegree with hd
  have hK : ∀ i, LinearMap.ker (aeval f β ^ i) = LinearMap.ker (aeval f (β ^ i)) := fun i => by
    rw [map_pow]
  rw [hK, hK] at hne ⊢
  have hle : LinearMap.ker (aeval f (β ^ j)) ≤ LinearMap.ker (aeval f (β ^ (j + 1))) := by
    rw [← hK, ← hK]; exact ker_pow_mono _ (Nat.le_succ j)
  obtain ⟨w, hw1, hw0⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hle hne)
  rw [LinearMap.mem_ker] at hw1
  set L := Fintype.linearCombination F (fun i : Fin d => (f ^ (i : ℕ)) w) with hL
  have hLg : ∀ c : Fin d → F, L c = aeval f (∑ i : Fin d, C (c i) * X ^ (i : ℕ)) w := by
    intro c
    rw [hL, Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, aeval_C, aeval_X_pow, Module.End.mul_apply, Module.algebraMap_end_apply]
  have hind : ∀ c : Fin d → F, L c ∈ LinearMap.ker (aeval f (β ^ j)) → c = 0 := by
    intro c hc
    by_contra hc0
    set g := ∑ i : Fin d, C (c i) * X ^ (i : ℕ) with hg
    have hg0 : g ≠ 0 := sum_C_mul_X_pow_ne_zero hc0
    have hgdeg : g.natDegree < d := (natDegree_lt_iff_degree_lt hg0).2 (degree_sum_fin_lt c)
    have hcop : IsCoprime β g := (Irreducible.coprime_iff_not_dvd hβ).2 fun h => by
      have := natDegree_le_of_dvd h hg0
      omega
    obtain ⟨a, b, hab⟩ := hcop
    apply hw0
    rw [LinearMap.mem_ker, hLg] at hc
    rw [LinearMap.mem_ker]
    have e : β ^ j = a * β ^ (j + 1) + b * (β ^ j * g) := by
      linear_combination (-(β ^ j)) * hab
    rw [e, map_add, map_mul, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, hw1, hc, map_zero, map_zero, add_zero]
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact hind c (by rw [hc]; exact Submodule.zero_mem _)
  have hrange : finrank F (LinearMap.range L) = d := by
    rw [LinearMap.finrank_range_of_inj hLinj, Module.finrank_fin_fun]
  have hdisj : LinearMap.range L ⊓ LinearMap.ker (aeval f (β ^ j)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨c, rfl⟩, hx⟩
    rw [hind c hx, map_zero]
    exact Submodule.zero_mem _
  have hsup : LinearMap.range L ⊔ LinearMap.ker (aeval f (β ^ j)) ≤
      LinearMap.ker (aeval f (β ^ (j + 1))) := by
    refine sup_le ?_ hle
    rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker, hLg]
    have h1 : aeval f (β ^ (j + 1)) * aeval f (∑ i : Fin d, C (c i) * X ^ (i : ℕ)) =
        aeval f (∑ i : Fin d, C (c i) * X ^ (i : ℕ)) * aeval f (β ^ (j + 1)) := by
      rw [← map_mul, mul_comm, map_mul]
    rw [← Module.End.mul_apply, h1, Module.End.mul_apply, hw1, map_zero]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range L)
    (LinearMap.ker (aeval f (β ^ j)))
  rw [hdisj, finrank_bot, add_zero, hrange] at h
  have h2 := Submodule.finrank_mono hsup
  omega

theorem finrank_ker_aeval_pow_ge (f : Module.End F V) {β : F[X]} (hβ : Irreducible β) {k : ℕ}
    (hdvd : β ^ k ∣ f.charpoly) :
    k * β.natDegree ≤ finrank F (LinearMap.ker (aeval f (β ^ k))) := by
  set N := aeval f β with hN
  set d := β.natDegree with hd
  obtain ⟨m, hm⟩ := exists_finrank_ker_ge f hβ hdvd
  have key : ∀ i, i * d ≤ finrank F (LinearMap.ker (N ^ i)) ∨
      ∃ j ≤ i, LinearMap.ker (N ^ j) = LinearMap.ker (N ^ (j + 1)) := by
    intro i
    induction i with
    | zero => left; simp
    | succ i ih =>
      rcases ih with h | ⟨j, hj, hjeq⟩
      · by_cases heq : LinearMap.ker (N ^ i) = LinearMap.ker (N ^ (i + 1))
        · exact Or.inr ⟨i, by omega, heq⟩
        · left
          have h2 := finrank_ker_succ_ge f hβ heq
          rw [add_mul, one_mul]
          linarith
      · exact Or.inr ⟨j, by omega, hjeq⟩
  rw [map_pow]
  rcases key k with h | ⟨j, hj, hjeq⟩
  · exact h
  · have hconst := Module.End.ker_pow_constant (f := N) hjeq
    have h1 : LinearMap.ker (N ^ k) = LinearMap.ker (N ^ j) := by
      rw [hconst (k - j), show j + (k - j) = k by omega]
    have h2 : LinearMap.ker (N ^ m) ≤ LinearMap.ker (N ^ k) := by
      rw [h1, hconst (m + k - j)]
      exact ker_pow_mono N (by omega)
    exact hm.trans (Submodule.finrank_mono h2)

end Chain

section MatrixAnn

variable {F : Type*} [Field F] {n : ℕ}

theorem aeval_toLin'_apply (M : Matrix (Fin n) (Fin n) F) (g : F[X]) (z : Fin n → F) :
    aeval (Matrix.toLin' M) g z = aeval M g *ᵥ z := by
  have e : Matrix.toLin' M = Matrix.toLinAlgEquiv' M := LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLinAlgEquiv'_apply]
  rw [e, aeval_algHom_apply, Matrix.toLinAlgEquiv'_apply]

theorem charpoly_toLin' (M : Matrix (Fin n) (Fin n) F) :
    LinearMap.charpoly (Matrix.toLin' M) = M.charpoly := by
  rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' M) (Pi.basisFun F (Fin n)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem card_ker_aeval_pow_ge {p : ℕ} [Fact p.Prime] (M : Matrix (Fin n) (Fin n) (ZMod p))
    {β : (ZMod p)[X]} (hβ : Irreducible β) {k : ℕ} (hdvd : β ^ k ∣ M.charpoly) :
    p ^ (k * β.natDegree) ≤
      (Finset.univ.filter fun z : Fin n → ZMod p => aeval M (β ^ k) *ᵥ z = 0).card := by
  classical
  set f := Matrix.toLin' M with hf
  have h1 := finrank_ker_aeval_pow_ge f hβ (by rw [hf, charpoly_toLin']; exact hdvd)
  have hmem : ∀ z : Fin n → ZMod p,
      z ∈ LinearMap.ker (aeval f (β ^ k)) ↔ aeval M (β ^ k) *ᵥ z = 0 := by
    intro z; rw [LinearMap.mem_ker, hf, aeval_toLin'_apply]
  have hcard : (Finset.univ.filter fun z : Fin n → ZMod p => aeval M (β ^ k) *ᵥ z = 0).card =
      p ^ finrank (ZMod p) (LinearMap.ker (aeval f (β ^ k))) := by
    rw [show (Finset.univ.filter fun z : Fin n → ZMod p => aeval M (β ^ k) *ᵥ z = 0) =
        Finset.univ.filter fun z => z ∈ LinearMap.ker (aeval f (β ^ k)) from
        Finset.filter_congr fun z _ => (hmem z).symm]
    rw [← Fintype.card_subtype,
      Module.card_eq_pow_finrank (K := ZMod p) (V := LinearMap.ker (aeval f (β ^ k))), ZMod.card]
  rw [hcard]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos h1

theorem aeval_mulVec_ne_zero_of_lt {M : Matrix (Fin n) (Fin n) F} {β : F[X]} (hβ : Irreducible β)
    {j : ℕ} {z : Fin n → F} (hz : aeval M (β ^ j) *ᵥ z = 0)
    (hz' : aeval M (β ^ (j - 1)) *ᵥ z ≠ 0) {g : F[X]} (hg0 : g ≠ 0)
    (hgd : g.natDegree < j * β.natDegree) : aeval M g *ᵥ z ≠ 0 := by
  intro hgz
  obtain ⟨i, g', hndvd, rfl⟩ := WfDvdMonoid.max_power_factor hg0 hβ
  have hg'0 : g' ≠ 0 := right_ne_zero_of_mul hg0
  have hβ0 : β ≠ 0 := hβ.ne_zero
  have hi : i < j := by
    have h1 : (β ^ i * g').natDegree = i * β.natDegree + g'.natDegree := by
      rw [natDegree_mul (pow_ne_zero _ hβ0) hg'0, natDegree_pow]
    by_contra hij
    push Not at hij
    have h2 : j * β.natDegree ≤ i * β.natDegree := Nat.mul_le_mul_right _ hij
    rw [h1] at hgd
    omega
  obtain ⟨a, b, hab⟩ := ((Irreducible.coprime_iff_not_dvd hβ).2 hndvd).pow_left (m := j)
  have h1 : aeval M (β ^ i) *ᵥ z = 0 := by
    have e : β ^ i = (a * β ^ i) * β ^ j + b * (β ^ i * g') := by
      linear_combination (-(β ^ i)) * hab
    rw [e, map_add, add_mulVec, map_mul (aeval M) (a * β ^ i) (β ^ j), ← mulVec_mulVec, hz,
      mulVec_zero, map_mul (aeval M) b, ← mulVec_mulVec, hgz, mulVec_zero, add_zero]
  apply hz'
  have e2 : β ^ (j - 1) = β ^ (j - 1 - i) * β ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [e2, map_mul, ← mulVec_mulVec, h1, mulVec_zero]

theorem krylovN_mulVec_eq_zero_of_ann {M : Matrix (Fin n) (Fin n) F} {β : F[X]}
    (hβ : Irreducible β) {j : ℕ} {z : Fin n → F} (hz : aeval M (β ^ j) *ᵥ z = 0)
    (hz' : aeval M (β ^ (j - 1)) *ᵥ z ≠ 0) {c : Fin (j * β.natDegree) → F}
    (hc : krylovN M z (j * β.natDegree) *ᵥ c = 0) : c = 0 := by
  by_contra hc0
  rw [krylovN_mulVec] at hc
  exact aeval_mulVec_ne_zero_of_lt hβ hz hz' (sum_C_mul_X_pow_ne_zero hc0)
    ((natDegree_lt_iff_degree_lt (sum_C_mul_X_pow_ne_zero hc0)).2 (degree_sum_fin_lt c)) hc

theorem aeval_mulVec_krylovN {M : Matrix (Fin n) (Fin n) F} {h : F[X]} {z : Fin n → F}
    (hz : aeval M h *ᵥ z = 0) (d : ℕ) (c : Fin d → F) : aeval M h *ᵥ (krylovN M z d *ᵥ c) = 0 := by
  rw [krylovN_mulVec, mulVec_mulVec, ← map_mul, mul_comm, map_mul, ← mulVec_mulVec, hz,
    mulVec_zero]

end MatrixAnn

section Compat

variable {F : Type*} [Field F] {D : ℕ}

theorem mulVec_single_one_apply (M : Matrix (Fin D) (Fin D) F) (i k : Fin D) :
    (M *ᵥ Pi.single i 1) k = M k i := by
  rw [mulVec_single_one]; rfl

theorem compMat_mulVec_single (g : F[X]) (i : Fin D) (hi : (i : ℕ) + 1 < D) :
    compMat g D *ᵥ Pi.single i 1 = Pi.single ⟨(i : ℕ) + 1, hi⟩ 1 := by
  funext k
  rw [mulVec_single_one_apply]
  simp only [compMat, Matrix.of_apply, hi, ite_true, Pi.single_apply, Fin.ext_iff]

theorem compMat_pow_mulVec_single_zero (g : F[X]) (hD : 0 < D) {a : ℕ} (ha : a < D) :
    compMat g D ^ a *ᵥ Pi.single ⟨0, hD⟩ 1 = Pi.single ⟨a, ha⟩ 1 := by
  induction a with
  | zero => rw [pow_zero, one_mulVec]
  | succ a ih =>
    rw [pow_succ', ← mulVec_mulVec, ih (by omega), compMat_mulVec_single g ⟨a, by omega⟩ ha]

theorem compMat_pow_apply_zero (g : F[X]) (hD : 0 < D) {a : ℕ} (ha : a < D) (l : Fin D) :
    (compMat g D ^ a) l ⟨0, hD⟩ = if l = ⟨a, ha⟩ then 1 else 0 := by
  have h := congrFun (compMat_pow_mulVec_single_zero g hD ha) l
  rw [mulVec_single_one_apply] at h
  rw [h, Pi.single_apply]

theorem compMat_pow_apply (g : F[X]) (hD : 0 < D) (a : ℕ) (l b : Fin D) :
    (compMat g D ^ a) l b = (compMat g D ^ (a + (b : ℕ))) l ⟨0, hD⟩ := by
  rw [← mulVec_single_one_apply (compMat g D ^ a) b l,
    ← mulVec_single_one_apply (compMat g D ^ (a + (b : ℕ))) ⟨0, hD⟩ l, pow_add, ← mulVec_mulVec,
    compMat_pow_mulVec_single_zero g hD b.2]

theorem transpose_pow_mul_eq {Q Θ : Matrix (Fin D) (Fin D) F} (h : Qᵀ * Θ = Θ * Q) (a : ℕ) :
    (Q ^ a)ᵀ * Θ = Θ * Q ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, transpose_mul, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h, Matrix.mul_assoc,
      ← pow_succ', pow_succ]

theorem entry_eq_of_comm (g : F[X]) (hD : 0 < D) {Θ : Matrix (Fin D) (Fin D) F}
    (h : (compMat g D)ᵀ * Θ = Θ * compMat g D) (a b : Fin D) :
    Θ a b = ∑ l, Θ ⟨0, hD⟩ l * (compMat g D ^ ((a : ℕ) + (b : ℕ))) l ⟨0, hD⟩ := by
  have h1 := congrFun (congrFun (transpose_pow_mul_eq h (a : ℕ)) ⟨0, hD⟩) b
  rw [Matrix.mul_apply, Matrix.mul_apply] at h1
  simp only [transpose_apply, compMat_pow_apply_zero g hD a.2] at h1
  have h2 : ∑ l : Fin D, (if l = (⟨(a : ℕ), a.2⟩ : Fin D) then (1 : F) else 0) * Θ l b = Θ a b := by
    simp
  rw [h2] at h1
  rw [h1]
  exact Finset.sum_congr rfl fun l _ => by rw [compMat_pow_apply g hD]

open Classical in
noncomputable def Sset (p : ℕ) [Fact p.Prime] {D : ℕ} (Q : Matrix (Fin D) (Fin D) (ZMod p)) :
    Finset (Matrix (Fin D) (Fin D) (ZMod p)) :=
  Finset.univ.filter fun Θ => Θᵀ = Θ ∧ (Θ * Q)ᵀ = Θ * Q ∧ (p = 2 → ∀ i, (Θ * Q) i i = 0)

theorem mem_Sset_iff {p : ℕ} [Fact p.Prime] {Q Θ : Matrix (Fin D) (Fin D) (ZMod p)} :
    Θ ∈ Sset p Q ↔ Θᵀ = Θ ∧ (Θ * Q)ᵀ = Θ * Q ∧ (p = 2 → ∀ i, (Θ * Q) i i = 0) := by
  classical
  simp only [Sset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem comm_of_mem_Sset {p : ℕ} [Fact p.Prime] {Q Θ : Matrix (Fin D) (Fin D) (ZMod p)} (hΘ : Θ ∈ Sset p Q) :
    Qᵀ * Θ = Θ * Q := by
  rw [mem_Sset_iff] at hΘ
  rw [← hΘ.2.1, transpose_mul, hΘ.1]

theorem card_Sset_le {p : ℕ} [Fact p.Prime] (g : (ZMod p)[X]) (hD : 0 < D) :
    (Sset p (compMat g D)).card ≤ p ^ D := by
  classical
  have hinj : Set.InjOn (fun Θ : Matrix (Fin D) (Fin D) (ZMod p) => Θ ⟨0, hD⟩)
      (Sset p (compMat g D) : Set (Matrix (Fin D) (Fin D) (ZMod p))) := by
    intro Θ hΘ Θ' hΘ' h
    have h' : Θ ⟨0, hD⟩ = Θ' ⟨0, hD⟩ := h
    ext a b
    rw [entry_eq_of_comm g hD (comm_of_mem_Sset (Finset.mem_coe.1 hΘ)),
      entry_eq_of_comm g hD (comm_of_mem_Sset (Finset.mem_coe.1 hΘ')), h']
  calc (Sset p (compMat g D)).card ≤ (Finset.univ : Finset (Fin D → ZMod p)).card :=
        Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = p ^ D := by rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

def oddCols (Q : Matrix (Fin D) (Fin D) F) (hD : 0 < D) : Matrix (Fin D) (Fin D) F :=
  Matrix.of fun i a => (Q ^ (2 * (a : ℕ) + 1)) i ⟨0, hD⟩

theorem oddCols_transpose_mulVec (g : F[X]) (hD : 0 < D) {Θ : Matrix (Fin D) (Fin D) F}
    (h : (compMat g D)ᵀ * Θ = Θ * compMat g D) (a : Fin D) :
    ((oddCols (compMat g D) hD)ᵀ *ᵥ Θ ⟨0, hD⟩) a = (Θ * compMat g D) a a := by
  have hΨ : (compMat g D)ᵀ * (Θ * compMat g D) = (Θ * compMat g D) * compMat g D := by
    rw [← Matrix.mul_assoc, h]
  rw [entry_eq_of_comm g hD hΨ a a]
  have e1 : ∑ l, (Θ * compMat g D) ⟨0, hD⟩ l * (compMat g D ^ ((a : ℕ) + (a : ℕ))) l ⟨0, hD⟩ =
      (Θ * compMat g D * compMat g D ^ ((a : ℕ) + (a : ℕ))) ⟨0, hD⟩ ⟨0, hD⟩ :=
    (Matrix.mul_apply).symm
  have e2 : Θ * compMat g D * compMat g D ^ ((a : ℕ) + (a : ℕ)) =
      Θ * compMat g D ^ (2 * (a : ℕ) + 1) := by
    rw [Matrix.mul_assoc, ← pow_succ', show (a : ℕ) + (a : ℕ) + 1 = 2 * (a : ℕ) + 1 by ring]
  rw [e1, e2, Matrix.mul_apply]
  simp only [mulVec, dotProduct, oddCols, transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem card_Sset_le_ker {p : ℕ} [Fact p.Prime] (g : (ZMod p)[X]) (hD : 0 < D) (hp2 : p = 2) :
    (Sset p (compMat g D)).card ≤
      (Finset.univ.filter fun v : Fin D → ZMod p => (oddCols (compMat g D) hD)ᵀ *ᵥ v = 0).card := by
  classical
  have hinj : Set.InjOn (fun Θ : Matrix (Fin D) (Fin D) (ZMod p) => Θ ⟨0, hD⟩)
      (Sset p (compMat g D) : Set (Matrix (Fin D) (Fin D) (ZMod p))) := by
    intro Θ hΘ Θ' hΘ' h
    have h' : Θ ⟨0, hD⟩ = Θ' ⟨0, hD⟩ := h
    ext a b
    rw [entry_eq_of_comm g hD (comm_of_mem_Sset (Finset.mem_coe.1 hΘ)),
      entry_eq_of_comm g hD (comm_of_mem_Sset (Finset.mem_coe.1 hΘ')), h']
  refine Finset.card_le_card_of_injOn _ (fun Θ hΘ => ?_) hinj
  have hΘ' := Finset.mem_coe.1 hΘ
  have hc := comm_of_mem_Sset hΘ'
  rw [mem_Sset_iff] at hΘ'
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  funext a
  rw [oddCols_transpose_mulVec g hD hc a, hΘ'.2.2 hp2 a, Pi.zero_apply]

theorem card_ker_transpose {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : Matrix (Fin D) (Fin D) K) :
    (Finset.univ.filter fun v : Fin D → K => Wᵀ *ᵥ v = 0).card =
      (Finset.univ.filter fun v : Fin D → K => W *ᵥ v = 0).card := by
  classical
  have h : ∀ Y : Matrix (Fin D) (Fin D) K,
      (Finset.univ.filter fun v : Fin D → K => Y *ᵥ v = 0).card = Fintype.card K ^ (D - Y.rank) := by
    intro Y
    have h1 := LinearMap.finrank_range_add_finrank_ker Y.mulVecLin
    rw [Module.finrank_fin_fun] at h1
    have h2 : (Finset.univ.filter fun v : Fin D → K => Y *ᵥ v = 0) =
        Finset.univ.filter fun v => v ∈ LinearMap.ker Y.mulVecLin :=
      Finset.filter_congr fun v _ => by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [h2, ← Fintype.card_subtype,
      Module.card_eq_pow_finrank (K := K) (V := LinearMap.ker Y.mulVecLin)]
    congr 1
    rw [Matrix.rank]
    omega
  rw [h, h, Matrix.rank_transpose]

theorem oddCols_mulVec (Q : Matrix (Fin D) (Fin D) F) (hD : 0 < D) (y : Fin D → F) :
    oddCols Q hD *ᵥ y =
      aeval Q (∑ a : Fin D, C (y a) * X ^ (2 * (a : ℕ) + 1)) *ᵥ Pi.single ⟨0, hD⟩ 1 := by
  funext i
  rw [mulVec_single_one_apply, map_sum, Matrix.sum_apply]
  simp only [mulVec, dotProduct, oddCols, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, aeval_C, aeval_X_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem aeval_compMat_mulVec_single_zero (g : F[X]) (hg : g.Monic) (hgd : g.natDegree = D)
    (hD : 0 < D) : aeval (compMat g D) g *ᵥ Pi.single ⟨0, hD⟩ 1 = 0 := by
  have hcoeff : g.coeff D = 1 := hgd ▸ hg.coeff_natDegree
  have h1 : aeval (compMat g D) g =
      ∑ i ∈ Finset.range D, g.coeff i • compMat g D ^ i + compMat g D ^ D := by
    rw [aeval_eq_sum_range, hgd, Finset.sum_range_succ, hcoeff, one_smul]
  funext k
  rw [h1, mulVec_single_one_apply, Matrix.add_apply, Matrix.sum_apply, Pi.zero_apply]
  have h2 : ∑ i ∈ Finset.range D, (g.coeff i • compMat g D ^ i) k ⟨0, hD⟩ = g.coeff k := by
    rw [Finset.sum_eq_single (k : ℕ)]
    · rw [Matrix.smul_apply, compMat_pow_apply_zero g hD k.2, ite_eq_left rfl, smul_eq_mul, mul_one]
    · intro i hi hik
      rw [Matrix.smul_apply, compMat_pow_apply_zero g hD (Finset.mem_range.1 hi), ite_eq_right, smul_zero]
      intro h
      exact hik (by rw [h])
    · intro hk
      exact absurd (Finset.mem_range.2 k.2) hk
  have hD1 : D - 1 + 1 = D := Nat.sub_add_cancel hD
  have h3 : (compMat g D ^ D) k ⟨0, hD⟩ = -g.coeff k := by
    rw [show compMat g D ^ D = compMat g D * compMat g D ^ (D - 1) by rw [← pow_succ', hD1],
      Matrix.mul_apply]
    simp only [compMat_pow_apply_zero g hD (Nat.sub_lt hD one_pos)]
    rw [Finset.sum_eq_single ⟨D - 1, Nat.sub_lt hD one_pos⟩]
    · rw [ite_eq_left rfl, mul_one]
      simp only [compMat, Matrix.of_apply]
      rw [ite_eq_right (by show ¬ ((D - 1) + 1 < D); omega)]
    · intro l _ hl
      rw [ite_eq_right hl, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h2, h3, add_neg_cancel]

theorem dvd_of_aeval_compMat_mulVec_eq_zero (g : F[X]) (hg : g.Monic) (hgd : g.natDegree = D)
    (hD : 0 < D) {h : F[X]} (hh : aeval (compMat g D) h *ᵥ Pi.single ⟨0, hD⟩ 1 = 0) : g ∣ h := by
  have hg1 : g ≠ 1 := fun h1 => by rw [h1, natDegree_one] at hgd; omega
  rw [← modByMonic_eq_zero_iff_dvd hg]
  have hrdeg : (h %ₘ g).natDegree < D := hgd ▸ natDegree_modByMonic_lt h hg hg1
  have hr0 : aeval (compMat g D) (h %ₘ g) *ᵥ Pi.single ⟨0, hD⟩ 1 = 0 := by
    have hdec : h %ₘ g = h - g * (h /ₘ g) := eq_sub_of_add_eq (modByMonic_add_div h g)
    rw [hdec, map_sub, sub_mulVec, hh, zero_sub, neg_eq_zero, mul_comm, map_mul, ← mulVec_mulVec,
      aeval_compMat_mulVec_single_zero g hg hgd hD, mulVec_zero]
  have hcoef : ∀ k : Fin D, (h %ₘ g).coeff k = 0 := by
    intro k
    have h1 := congrFun hr0 k
    rw [aeval_eq_sum_range' hrdeg, mulVec_single_one_apply, Matrix.sum_apply, Pi.zero_apply] at h1
    rw [Finset.sum_eq_single (k : ℕ)] at h1
    · rw [Matrix.smul_apply, compMat_pow_apply_zero g hD k.2, ite_eq_left rfl, smul_eq_mul,
        mul_one] at h1
      exact h1
    · intro i hi hik
      rw [Matrix.smul_apply, compMat_pow_apply_zero g hD (Finset.mem_range.1 hi), ite_eq_right, smul_zero]
      intro h
      exact hik (by rw [h])
    · intro hk
      exact absurd (Finset.mem_range.2 k.2) hk
  ext i
  rw [coeff_zero]
  by_cases hi : i < D
  · exact hcoef ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

end Compat

section Two

variable {D : ℕ}

theorem oddPoly_eq_two (y : Fin D → ZMod 2) :
    ∑ a : Fin D, C (y a) * X ^ (2 * (a : ℕ) + 1) = X * (∑ a : Fin D, C (y a) * X ^ (a : ℕ)) ^ 2 := by
  rw [← ZMod.expand_card (p := 2) (∑ a : Fin D, C (y a) * X ^ (a : ℕ)), map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, expand_C, map_pow, expand_X]
  ring

theorem pow_half_dvd_of_dvd_X_mul_sq {F : Type*} [Field F] {β g : F[X]} (hβ : Irreducible β)
    {j : ℕ} (h : β ^ j ∣ X * g ^ 2) : β ^ (j / 2) ∣ g := by
  by_cases hg0 : g = 0
  · rw [hg0]; exact dvd_zero _
  obtain ⟨v, g', hndvd, rfl⟩ := WfDvdMonoid.max_power_factor hg0 hβ
  refine dvd_mul_of_dvd_left (pow_dvd_pow β ?_) _
  by_contra hlt
  push Not at hlt
  have hβ0 : β ≠ 0 := hβ.ne_zero
  have h1 : β ^ (2 * v) * β ^ (j - 2 * v) ∣ β ^ (2 * v) * (X * g' ^ 2) := by
    rw [← pow_add, show 2 * v + (j - 2 * v) = j by omega]
    convert h using 1
    ring
  have h2 : β ^ (j - 2 * v) ∣ X * g' ^ 2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hβ0)).1 h1
  have hcop : IsCoprime (β ^ (j - 2 * v)) (g' ^ 2) :=
    (((Irreducible.coprime_iff_not_dvd hβ).2 hndvd).pow_left).pow_right
  have h3 : β ^ (j - 2 * v) ∣ X := hcop.dvd_of_dvd_mul_right h2
  have h4 := natDegree_le_of_dvd h3 X_ne_zero
  rw [natDegree_pow, natDegree_X] at h4
  have hd := hβ.natDegree_pos
  have h5 : 2 ≤ j - 2 * v := by omega
  nlinarith

theorem eq_sum_fin_of_natDegree_lt {F : Type*} [Field F] {t : F[X]} {m : ℕ} (ht : t.natDegree < m) :
    t = ∑ l : Fin m, C (t.coeff l) * X ^ (l : ℕ) := by
  conv_lhs => rw [t.as_sum_range' m ht]
  rw [Fin.sum_univ_eq_sum_range (fun l => C (t.coeff l) * X ^ l) m]
  exact Finset.sum_congr rfl fun l _ => (C_mul_X_pow_eq_monomial).symm

theorem coeff_sum_fin {F : Type*} [Field F] (y : Fin D → F) (i : Fin D) :
    (∑ a : Fin D, C (y a) * X ^ (a : ℕ)).coeff i = y i := by
  simp only [Polynomial.finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have : (i : ℕ) ≠ (b : ℕ) := fun h' => hb (Fin.ext h').symm
    simp [this]
  · simp

open Classical in
theorem card_filter_dvd_le {p : ℕ} [Fact p.Prime] {β : (ZMod p)[X]} (hβ : β ≠ 0) (c : ℕ) :
    (Finset.univ.filter fun y : Fin D → ZMod p =>
      β ^ c ∣ ∑ a : Fin D, C (y a) * X ^ (a : ℕ)).card ≤ p ^ (D - c * β.natDegree) := by
  classical
  set φ : (Fin (D - c * β.natDegree) → ZMod p) → (Fin D → ZMod p) := fun q i =>
    (β ^ c * ∑ l : Fin (D - c * β.natDegree), C (q l) * X ^ (l : ℕ)).coeff i with hφ
  have hsub : (Finset.univ.filter fun y : Fin D → ZMod p =>
      β ^ c ∣ ∑ a : Fin D, C (y a) * X ^ (a : ℕ)) ⊆ Finset.univ.image φ := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨t, ht⟩ := hy
    rw [Finset.mem_image]
    refine ⟨fun l => t.coeff l, Finset.mem_univ _, ?_⟩
    have htsum : ∑ l : Fin (D - c * β.natDegree), C (t.coeff l) * X ^ (l : ℕ) = t := by
      by_cases ht0 : t = 0
      · simp [ht0]
      · have hdeg : (∑ a : Fin D, C (y a) * X ^ (a : ℕ)).natDegree < D ∨
            ∑ a : Fin D, C (y a) * X ^ (a : ℕ) = 0 := by
          by_cases hz : ∑ a : Fin D, C (y a) * X ^ (a : ℕ) = 0
          · exact Or.inr hz
          · exact Or.inl ((natDegree_lt_iff_degree_lt hz).2 (degree_sum_fin_lt y))
        rcases hdeg with hdeg | hz
        · rw [ht, natDegree_mul (pow_ne_zero _ hβ) ht0, natDegree_pow] at hdeg
          exact (eq_sum_fin_of_natDegree_lt (by omega)).symm
        · rw [hz] at ht
          exact absurd ((mul_eq_zero.1 ht.symm).resolve_left (pow_ne_zero _ hβ)) ht0
    funext i
    simp only [hφ]
    rw [htsum, ← ht, coeff_sum_fin]
  calc (Finset.univ.filter fun y : Fin D → ZMod p =>
        β ^ c ∣ ∑ a : Fin D, C (y a) * X ^ (a : ℕ)).card ≤ (Finset.univ.image φ).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin (D - c * β.natDegree) → ZMod p)).card := Finset.card_image_le
    _ = p ^ (D - c * β.natDegree) := by
        rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem card_Sset_two_le {p : ℕ} [Fact p.Prime] (hp2 : p = 2) {β : (ZMod p)[X]}
    (hβ : Irreducible β) (hβm : β.Monic) {j : ℕ} (hj : 1 ≤ j) :
    (Sset p (compMat (β ^ j) (j * β.natDegree))).card ≤ p ^ ((j - j / 2) * β.natDegree) := by
  classical
  have hD : 0 < j * β.natDegree := Nat.mul_pos hj hβ.natDegree_pos
  have hgm : (β ^ j).Monic := hβm.pow j
  have hgd : (β ^ j).natDegree = j * β.natDegree := natDegree_pow β j
  refine (card_Sset_le_ker (β ^ j) hD hp2).trans ?_
  rw [card_ker_transpose]
  have hsub : (Finset.univ.filter fun y : Fin (j * β.natDegree) → ZMod p =>
      oddCols (compMat (β ^ j) (j * β.natDegree)) hD *ᵥ y = 0) ⊆
      Finset.univ.filter fun y : Fin (j * β.natDegree) → ZMod p =>
        β ^ (j / 2) ∣ ∑ a : Fin (j * β.natDegree), C (y a) * X ^ (a : ℕ) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [oddCols_mulVec] at hy
    have h1 := dvd_of_aeval_compMat_mulVec_eq_zero (β ^ j) hgm hgd hD hy
    subst hp2
    rw [oddPoly_eq_two] at h1
    exact pow_half_dvd_of_dvd_X_mul_sq hβ h1
  refine (Finset.card_le_card hsub).trans ((card_filter_dvd_le hβ.ne_zero (j / 2)).trans ?_)
  apply le_of_eq
  congr 1
  rw [Nat.sub_mul]

end Two

section PropA

variable {p : ℕ} [hp : Fact p.Prime]

theorem tor2_mul_eq_zero_iff_prime (w : ZMod p) :
    (∀ b : Tor2 p, b.1 * w = 0) ↔ (p = 2 → ∃ y : ZMod p, w = 2 * y) := by
  by_cases hp2 : p = 2
  · subst hp2
    have h2 : (2 : ZMod 2) = 0 := rfl
    constructor
    · intro h _
      have h1 := h ⟨1, rfl⟩
      rw [one_mul] at h1
      exact ⟨0, by rw [h1, mul_zero]⟩
    · rintro h b
      obtain ⟨y, hy⟩ := h rfl
      rw [hy, h2, zero_mul, mul_zero]
  · exact tor2_mul_eq_zero_iff_odd hp2 w

theorem card_tor2_two_eq (hp2 : p = 2) : Fintype.card (Tor2 p) = 2 := by
  subst hp2
  rfl

theorem sym_dim_eq (D : ℕ) : D * (D + 1) / 2 = D * (D - 1) / 2 + D := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp
  · have h : D * (D + 1) = D * (D - 1) + 2 * D := by
      obtain ⟨e, rfl⟩ : ∃ e, D = e + 1 := ⟨D - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [h, Nat.add_mul_div_left _ _ (by norm_num)]

theorem card_Sset_antisymm_le {β : (ZMod p)[X]} (hβ : Irreducible β) (hβm : β.Monic) {j k : ℕ}
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    ((Sset p (compMat (β ^ j) (j * β.natDegree))).card : ℝ) * (antisymm (j * β.natDegree) p).card *
      ((p : ℝ) ^ ((j * β.natDegree) * ((j * β.natDegree) + 1) / 2))⁻¹ ≤
        (p : ℝ) ^ ((k - k / 2) * β.natDegree) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  set d := β.natDegree with hd
  set D := j * d with hDdef
  have hD : 0 < D := Nat.mul_pos hj hβ.natDegree_pos
  have hSym : ((p : ℝ) ^ (D * (D + 1) / 2)) = (p : ℝ) ^ (D * (D - 1) / 2) * (p : ℝ) ^ D := by
    rw [sym_dim_eq, pow_add]
  have hpos1 : (0 : ℝ) < (p : ℝ) ^ (D * (D - 1) / 2) := by positivity
  have hpos2 : (0 : ℝ) < (p : ℝ) ^ D := by positivity
  by_cases hp2 : p = 2
  · have hA : ((antisymm D p).card : ℝ) = (p : ℝ) ^ (D * (D - 1) / 2) * (p : ℝ) ^ D := by
      have h2 : (2 : ℝ) = (p : ℝ) := by rw [hp2]; norm_num
      rw [card_antisymm, card_tor2_two_eq hp2]
      push_cast
      rw [h2]
    have hS := card_Sset_two_le hp2 hβ hβm hj
    calc ((Sset p (compMat (β ^ j) D)).card : ℝ) * (antisymm D p).card *
          ((p : ℝ) ^ (D * (D + 1) / 2))⁻¹ = (Sset p (compMat (β ^ j) D)).card := by
          rw [hA, hSym]; field_simp
      _ ≤ (p : ℝ) ^ ((j - j / 2) * d) := by exact_mod_cast hS
      _ ≤ (p : ℝ) ^ ((k - k / 2) * d) :=
          pow_le_pow_right₀ hp1 (Nat.mul_le_mul_right _ (by omega))
  · have hA : ((antisymm D p).card : ℝ) = (p : ℝ) ^ (D * (D - 1) / 2) := by
      rw [card_antisymm_odd_one hp2]; push_cast; rfl
    have hS : ((Sset p (compMat (β ^ j) D)).card : ℝ) ≤ (p : ℝ) ^ D := by
      exact_mod_cast card_Sset_le (β ^ j) hD
    calc ((Sset p (compMat (β ^ j) D)).card : ℝ) * (antisymm D p).card *
          ((p : ℝ) ^ (D * (D + 1) / 2))⁻¹ ≤ (p : ℝ) ^ D * (p : ℝ) ^ (D * (D - 1) / 2) *
          ((p : ℝ) ^ (D * (D + 1) / 2))⁻¹ := by
          rw [hA]; gcongr
      _ = 1 := by rw [hSym]; field_simp
      _ ≤ (p : ℝ) ^ ((k - k / 2) * d) := one_le_pow₀ hp1

theorem dotProduct_mulVec_self_eq_zero {R : Type*} [CommRing R] {m : ℕ} (h2 : (2 : R) = 0)
    {A : Matrix (Fin m) (Fin m) R} (hA : Aᵀ = A) (hdiag : ∀ i, A i i = 0) (y : Fin m → R) :
    y ⬝ᵥ (A *ᵥ y) = 0 := by
  set U : Matrix (Fin m) (Fin m) R := Matrix.of fun a b => if a < b then A a b else 0 with hU
  have hAU : A = U + Uᵀ := by
    ext a b
    simp only [hU, Matrix.add_apply, transpose_apply, Matrix.of_apply]
    rcases lt_trichotomy a b with h | rfl | h
    · rw [ite_eq_left h, ite_eq_right (not_lt.2 h.le), add_zero]
    · rw [ite_eq_right (lt_irrefl _), add_zero, hdiag]
    · rw [ite_eq_right (not_lt.2 h.le), ite_eq_left h, zero_add]
      exact (congrFun (congrFun hA a) b).symm
  rw [hAU, add_mulVec, dotProduct_add]
  have : y ⬝ᵥ (Uᵀ *ᵥ y) = y ⬝ᵥ (U *ᵥ y) := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [this, ← two_mul, h2, zero_mul]

omit hp in
theorem modP_symOf_transpose {n : ℕ} (ω : Pairs n → Bool) :
    (modP p (symOf 1 0 ω))ᵀ = modP p (symOf 1 0 ω) := by
  ext i j
  simp only [transpose_apply, modP, Matrix.map_apply]
  rw [symOf_comm]

theorem modP_symOf_diag {n : ℕ} (ω : Pairs n → Bool) (i : Fin n) : modP p (symOf 1 0 ω) i i = 0 := by
  simp [modP, symOf]

open Classical in
noncomputable def tFrames (p : ℕ) [Fact p.Prime] (n : ℕ) (β : (ZMod p)[X]) (j : ℕ) :
    Finset (Matrix (Fin n) (Fin (j * β.natDegree)) (ZMod p)) :=
  Finset.univ.filter fun V => IsRobust (sDelta (1 / 4) n) V ∧
    Vᵀ * V ∈ Sset p (compMat (β ^ j) (j * β.natDegree))

theorem mem_tFrames_iff {n : ℕ} {β : (ZMod p)[X]} {j : ℕ}
    {V : Matrix (Fin n) (Fin (j * β.natDegree)) (ZMod p)} :
    V ∈ tFrames p n β j ↔
      IsRobust (sDelta (1 / 4) n) V ∧ Vᵀ * V ∈ Sset p (compMat (β ^ j) (j * β.natDegree)) := by
  classical
  simp only [tFrames, Finset.mem_filter, Finset.mem_univ, true_and]

theorem tight_count_ge {n k : ℕ} {β : (ZMod p)[X]} (hβ : Irreducible β) (hβm : β.Monic)
    (hR : ∀ j ∈ Finset.Icc 1 k, (p, j * β.natDegree) ∈ Rn (1 / 4) n)
    (ω : Pairs n → Bool) (hdvd : β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly)
    (hN : NoShort (1 / 4) n ω) :
    (p : ℝ) ^ (k * β.natDegree) ≤ 1 + ∑ j ∈ Finset.Icc 1 k,
      (((tFrames p n β j).filter fun V =>
        modP p (symOf 1 0 ω) * V = V * compMat (β ^ j) (j * β.natDegree)).card : ℝ) := by
  set A := modP p (symOf 1 0 ω) with hA
  set d := β.natDegree with hd
  have hd1 : 1 ≤ d := hβ.natDegree_pos
  have hAsymm : Aᵀ = A := modP_symOf_transpose ω
  have hAdiag : ∀ i, A i i = 0 := modP_symOf_diag ω
  set Kset := Finset.univ.filter fun z : Fin n → ZMod p => aeval A (β ^ k) *ᵥ z = 0 with hKset
  have hK := card_ker_aeval_pow_ge A hβ hdvd
  set Z : ℕ → Finset (Fin n → ZMod p) := fun j => Finset.univ.filter fun z =>
    aeval A (β ^ j) *ᵥ z = 0 ∧ aeval A (β ^ (j - 1)) *ᵥ z ≠ 0 with hZ
  have hcover : Kset ⊆ {0} ∪ (Finset.Icc 1 k).biUnion Z := by
    intro z hz
    rw [hKset, Finset.mem_filter] at hz
    by_cases hz0 : z = 0
    · rw [hz0]
      exact Finset.mem_union_left _ (Finset.mem_singleton_self 0)
    · rw [Finset.mem_union, Finset.mem_biUnion]
      right
      have hex : ∃ j, aeval A (β ^ j) *ᵥ z = 0 := ⟨k, hz.2⟩
      have hpos : 0 < Nat.find hex := by
        by_contra h0
        push Not at h0
        have h1 : Nat.find hex = 0 := by omega
        have h2 := Nat.find_spec hex
        rw [h1, pow_zero, map_one, one_mulVec] at h2
        exact hz0 h2
      refine ⟨Nat.find hex, Finset.mem_Icc.2 ⟨hpos, Nat.find_min' hex hz.2⟩, ?_⟩
      rw [hZ, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Nat.find_spec hex, Nat.find_min hex (by omega)⟩
  have hZcard : ∀ j ∈ Finset.Icc 1 k, (Z j).card ≤
      ((tFrames p n β j).filter fun V => A * V = V * compMat (β ^ j) (j * d)).card := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have hD : 0 < j * d := Nat.mul_pos hj'.1 hd1
    apply Finset.card_le_card_of_injOn (fun z => krylovN A z (j * d))
    · intro z hz
      rw [Finset.mem_coe, hZ, Finset.mem_filter] at hz
      obtain ⟨-, hz1, hz2⟩ := hz
      have hAV := mul_krylovN A z (hβm.pow j) (natDegree_pow β j) hz1
      rw [Finset.mem_coe, Finset.mem_filter, mem_tFrames_iff]
      refine ⟨⟨?_, ?_⟩, hAV⟩
      ·
        intro c hc
        have hv0 : krylovN A z (j * d) *ᵥ c ≠ 0 := fun h =>
          hc (krylovN_mulVec_eq_zero_of_ann hβ hz1 hz2 h)
        have hvk : aeval A (β ^ j) *ᵥ (krylovN A z (j * d) *ᵥ c) = 0 :=
          aeval_mulVec_krylovN hz1 _ c
        by_contra hlt
        push Not at hlt
        have hwt : 0 < wt (krylovN A z (j * d) *ᵥ c) := by
          obtain ⟨i, hi⟩ : ∃ i, (krylovN A z (j * d) *ᵥ c) i ≠ 0 := by
            by_contra h; push Not at h; exact hv0 (funext h)
          exact Finset.card_pos.2 ⟨i, by simp [hi]⟩
        exact hN p hp.out (β ^ j) (hβm.pow j) (by rw [natDegree_pow]; exact hR j hj) _ hwt hlt hvk
      ·
        rw [mem_Sset_iff]
        set V := krylovN A z (j * d) with hV
        have hVC : Vᵀ * V * compMat (β ^ j) (j * d) = Vᵀ * A * V := by
          rw [Matrix.mul_assoc, ← hAV, Matrix.mul_assoc]
        refine ⟨by rw [transpose_mul, transpose_transpose], ?_, ?_⟩
        · rw [hVC, transpose_mul, transpose_mul, transpose_transpose, hAsymm, Matrix.mul_assoc]
        · intro hp2 i
          rw [hVC]
          have h2 : (2 : ZMod p) = 0 := by subst hp2; rfl
          have h3 := dotProduct_mulVec_self_eq_zero h2 hAsymm hAdiag (fun l => V l i)
          rw [← h3, Matrix.mul_assoc, Matrix.mul_apply]
          rfl
    · intro z _ z' _ h
      funext l
      have h0 := congrArg (fun V : Matrix (Fin n) (Fin (j * d)) (ZMod p) => V l ⟨0, hD⟩) h
      simpa [krylovN] using h0
  calc (p : ℝ) ^ (k * d) ≤ (Kset.card : ℝ) := by exact_mod_cast hK
    _ ≤ (({0} ∪ (Finset.Icc 1 k).biUnion Z).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcover
    _ ≤ 1 + ∑ j ∈ Finset.Icc 1 k, ((Z j).card : ℝ) := by
        have h1 := Finset.card_union_le {0} ((Finset.Icc 1 k).biUnion Z)
        have h2 := Finset.card_biUnion_le (s := Finset.Icc 1 k) (t := Z)
        rw [Finset.card_singleton] at h1
        have h3 : ({0} ∪ (Finset.Icc 1 k).biUnion Z).card ≤
            1 + ∑ j ∈ Finset.Icc 1 k, (Z j).card := by omega
        exact_mod_cast h3
    _ ≤ 1 + ∑ j ∈ Finset.Icc 1 k,
          (((tFrames p n β j).filter fun V => A * V = V * compMat (β ^ j) (j * d)).card : ℝ) := by
        gcongr with j hj
        exact_mod_cast hZcard j hj

theorem prob_tight_beta_le {n k : ℕ} {β : (ZMod p)[X]} (hβ : Irreducible β) (hβm : β.Monic)
    (hR : ∀ j ∈ Finset.Icc 1 k, (p, j * β.natDegree) ∈ Rn (1 / 4) n) :
    prob (fun ω : Pairs n → Bool =>
      β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly ∧ NoShort (1 / 4) n ω) ≤
      ((p : ℝ) ^ (k * β.natDegree))⁻¹ * (1 + ∑ j ∈ Finset.Icc 1 k, ∑ V ∈ tFrames p n β j,
        prob (fun ω : Pairs n → Bool =>
          modP p (symOf 1 0 ω) * V = V * compMat (β ^ j) (j * β.natDegree))) := by
  have hpk : (0 : ℝ) < (p : ℝ) ^ (k * β.natDegree) := by
    have := hp.out.pos; positivity
  set X : (Pairs n → Bool) → ℝ := fun ω => ((p : ℝ) ^ (k * β.natDegree))⁻¹ *
    (1 + ∑ j ∈ Finset.Icc 1 k, (((tFrames p n β j).filter fun V =>
      modP p (symOf 1 0 ω) * V = V * compMat (β ^ j) (j * β.natDegree)).card : ℝ)) with hX
  have hind : ∀ ω : Pairs n → Bool, @ite ℝ (β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly ∧
      NoShort (1 / 4) n ω) (Classical.dec _) 1 0 ≤ X ω := by
    intro ω
    by_cases h : β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly ∧ NoShort (1 / 4) n ω
    · rw [ite_eq_left h, hX, le_inv_mul_iff₀ hpk, mul_one]
      exact tight_count_ge hβ hβm hR ω h.1 h.2
    · rw [ite_eq_right h]
      exact mul_nonneg (inv_nonneg.2 hpk.le)
        (add_nonneg zero_le_one (Finset.sum_nonneg fun j _ => Nat.cast_nonneg _))
  rw [← expect_indicator']
  refine (expect_mono hind).trans (le_of_eq ?_)
  rw [hX, expect_const_mul]
  congr 1
  rw [expect_add, expect_const, expect_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ ω : Pairs n → Bool, ((((tFrames p n β j).filter fun V =>
      modP p (symOf 1 0 ω) * V = V * compMat (β ^ j) (j * β.natDegree)).card : ℕ) : ℝ) =
      ∑ V ∈ tFrames p n β j, (if modP p (symOf 1 0 ω) * V = V * compMat (β ^ j) (j * β.natDegree)
        then (1 : ℝ) else 0) := by
    intro ω; rw [Finset.card_filter]; push_cast; rfl
  simp_rw [h1]
  rw [expect_sum]
  exact Finset.sum_congr rfl fun V _ => expect_indicator _

theorem card_gram_eq_le (n : ℕ) {D : ℕ} (hD : 1 ≤ D) {Θ : Matrix (Fin D) (Fin D) (ZMod p)}
    (hΘ : Θᵀ = Θ) :
    ((Finset.univ.filter fun V : Matrix (Fin n) (Fin D) (ZMod p) => Vᵀ * V = Θ).card : ℝ) ≤
      (p : ℝ) ^ (n * D) * (((p : ℝ) ^ (D * (D + 1) / 2))⁻¹ + (p : ℝ) ^ D * cGram p D ^ n) := by
  classical
  obtain ⟨hc0, -, hc⟩ := cGram_bounds (q := p) (r := D) hp.out.two_le hD
  have h := abs_prob_gram_fst_sub_le (fun w => tor2_mul_eq_zero_iff_prime (p := p) w) hc0 hc n hΘ
  have hprob : prob (fun V : Matrix (Fin n) (Fin D) (ZMod p) => Vᵀ * V = Θ) =
      ((Finset.univ.filter fun V : Matrix (Fin n) (Fin D) (ZMod p) => Vᵀ * V = Θ).card : ℝ) /
        (p : ℝ) ^ (n * D) := by
    rw [prob_eq_card_filter]
    congr 1
    rw [show Fintype.card (Matrix (Fin n) (Fin D) (ZMod p)) =
      Fintype.card (Fin n → Fin D → ZMod p) from rfl, Fintype.card_fun, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rw [← pow_mul, mul_comm D n]
  have hpos : (0 : ℝ) < (p : ℝ) ^ (n * D) := by have := hp.out.pos; positivity
  rw [hprob] at h
  have h3 := (abs_le.1 h).2
  have h4 : ((Finset.univ.filter fun V : Matrix (Fin n) (Fin D) (ZMod p) => Vᵀ * V = Θ).card : ℝ) /
      (p : ℝ) ^ (n * D) ≤ ((p : ℝ) ^ (D * (D + 1) / 2))⁻¹ + (p : ℝ) ^ D * cGram p D ^ n := by
    linarith
  rw [div_le_iff₀ hpos] at h4
  linarith

theorem card_tFrames_le (n : ℕ) {β : (ZMod p)[X]} {j : ℕ} (hD : 1 ≤ j * β.natDegree) :
    ((tFrames p n β j).card : ℝ) ≤ (Sset p (compMat (β ^ j) (j * β.natDegree))).card *
      ((p : ℝ) ^ (n * (j * β.natDegree)) *
        (((p : ℝ) ^ ((j * β.natDegree) * ((j * β.natDegree) + 1) / 2))⁻¹ +
          (p : ℝ) ^ (j * β.natDegree) * cGram p (j * β.natDegree) ^ n)) := by
  classical
  set D := j * β.natDegree with hDdef
  set S := Sset p (compMat (β ^ j) D) with hS
  have h1 : (tFrames p n β j).card ≤
      (Finset.univ.filter fun V : Matrix (Fin n) (Fin D) (ZMod p) => Vᵀ * V ∈ S).card := by
    apply Finset.card_le_card
    intro V hV
    rw [mem_tFrames_iff] at hV
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hV.2
  have h2 : (Finset.univ.filter fun V : Matrix (Fin n) (Fin D) (ZMod p) => Vᵀ * V ∈ S).card =
      ∑ Θ ∈ S, (Finset.univ.filter fun V : Matrix (Fin n) (Fin D) (ZMod p) => Vᵀ * V = Θ).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun V => Vᵀ * V) (t := S)]
    · refine Finset.sum_congr rfl fun Θ hΘ => ?_
      congr 1
      ext V
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hΘ, h⟩
    · intro V hV
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hV
      exact hV
  calc ((tFrames p n β j).card : ℝ)
      ≤ ((Finset.univ.filter fun V : Matrix (Fin n) (Fin D) (ZMod p) => Vᵀ * V ∈ S).card : ℝ) := by
        exact_mod_cast h1
    _ = ∑ Θ ∈ S, ((Finset.univ.filter fun V : Matrix (Fin n) (Fin D) (ZMod p) =>
          Vᵀ * V = Θ).card : ℝ) := by rw [h2]; push_cast; rfl
    _ ≤ ∑ _Θ ∈ S, (p : ℝ) ^ (n * D) * (((p : ℝ) ^ (D * (D + 1) / 2))⁻¹ +
          (p : ℝ) ^ D * cGram p D ^ n) := by
        refine Finset.sum_le_sum fun Θ hΘ => card_gram_eq_le n hD ?_
        rw [hS, mem_Sset_iff] at hΘ
        exact hΘ.1
    _ = (S.card : ℝ) * ((p : ℝ) ^ (n * D) * (((p : ℝ) ^ (D * (D + 1) / 2))⁻¹ +
          (p : ℝ) ^ D * cGram p D ^ n)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

theorem sum_tFrames_prob_le (n : ℕ) {β : (ZMod p)[X]} {j : ℕ} (hD : 1 ≤ j * β.natDegree) {b : ℝ}
    (hb0 : 0 ≤ b)
    (hb : ∀ V ∈ tFrames p n β j, prob (fun ω : Pairs n → Bool =>
      modP p (symOf 1 0 ω) * V = V * compMat (β ^ j) (j * β.natDegree)) ≤
        b * (((p : ℝ) ^ (n * (j * β.natDegree)))⁻¹ * (antisymm (j * β.natDegree) p).card)) :
    ∑ V ∈ tFrames p n β j, prob (fun ω : Pairs n → Bool =>
      modP p (symOf 1 0 ω) * V = V * compMat (β ^ j) (j * β.natDegree)) ≤
      ((Sset p (compMat (β ^ j) (j * β.natDegree))).card * (antisymm (j * β.natDegree) p).card : ℝ) *
        (((p : ℝ) ^ ((j * β.natDegree) * ((j * β.natDegree) + 1) / 2))⁻¹ +
          (p : ℝ) ^ (j * β.natDegree) * cGram p (j * β.natDegree) ^ n) * b := by
  set D := j * β.natDegree with hDdef
  have hP : (0 : ℝ) < (p : ℝ) ^ (n * D) := by have := hp.out.pos; positivity
  have hc0 := (cGram_bounds (q := p) (r := D) hp.out.two_le hD).1
  have hw0 : (0 : ℝ) ≤ ((p : ℝ) ^ (D * (D + 1) / 2))⁻¹ + (p : ℝ) ^ D * cGram p D ^ n := by
    positivity
  calc ∑ V ∈ tFrames p n β j, prob (fun ω : Pairs n → Bool =>
        modP p (symOf 1 0 ω) * V = V * compMat (β ^ j) D)
      ≤ ∑ _V ∈ tFrames p n β j, b * (((p : ℝ) ^ (n * D))⁻¹ * (antisymm D p).card) :=
        Finset.sum_le_sum hb
    _ = ((tFrames p n β j).card : ℝ) * (b * (((p : ℝ) ^ (n * D))⁻¹ * (antisymm D p).card)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Sset p (compMat (β ^ j) D)).card * ((p : ℝ) ^ (n * D) *
          (((p : ℝ) ^ (D * (D + 1) / 2))⁻¹ + (p : ℝ) ^ D * cGram p D ^ n))) *
          (b * (((p : ℝ) ^ (n * D))⁻¹ * (antisymm D p).card)) := by
        gcongr
        exact card_tFrames_le n hD
    _ = ((Sset p (compMat (β ^ j) D)).card * (antisymm D p).card : ℝ) *
          (((p : ℝ) ^ (D * (D + 1) / 2))⁻¹ + (p : ℝ) ^ D * cGram p D ^ n) * b := by
        field_simp

theorem tendsto_tight_term (a u v c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => a * (u + v * c ^ n) * (1 + |ε n|)) atTop (𝓝 (a * u)) := by
  have h1 : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
  have h2 : Tendsto (fun n : ℕ => |ε n|) atTop (𝓝 0) := by simpa using hε.abs
  have h3 := ((tendsto_const_nhds (x := a)).mul ((tendsto_const_nhds (x := u)).add
    ((tendsto_const_nhds (x := v)).mul h1))).mul ((tendsto_const_nhds (x := (1 : ℝ))).add h2)
  simpa using h3

theorem prop_tight_a (p : ℕ) [hp : Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) (k : ℕ) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, prob (fun ω : Pairs n → Bool =>
      ∃ β ∈ irrSet p d, β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly) ≤
        (k + 1) * piCount p d * ((p : ℝ) ^ (k / 2 * d))⁻¹ + η := by
  obtain ⟨ε, hε, hev⟩ := lem_fourier_b_gen (δ := 1 / 4) (by norm_num) (by norm_num)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  set Ir := irrSet p d with hIr
  have hIrdeg : ∀ β ∈ Ir, β.Monic ∧ Irreducible β ∧ β.natDegree = d := fun β hβ =>
    mem_irrSet_iff.1 hβ
  set a : (ZMod p)[X] → ℕ → ℝ := fun β j =>
    ((Sset p (compMat (β ^ j) (j * β.natDegree))).card * (antisymm (j * β.natDegree) p).card : ℝ)
    with ha
  set u : (ZMod p)[X] → ℕ → ℝ := fun β j =>
    ((p : ℝ) ^ ((j * β.natDegree) * ((j * β.natDegree) + 1) / 2))⁻¹ with hu
  set v : (ZMod p)[X] → ℕ → ℝ := fun β j => (p : ℝ) ^ (j * β.natDegree) with hv
  set c : (ZMod p)[X] → ℕ → ℝ := fun β j => cGram p (j * β.natDegree) with hc
  set T : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) / 8) + ∑ β ∈ Ir, ((p : ℝ) ^ (k * β.natDegree))⁻¹ *
    (1 + ∑ j ∈ Finset.Icc 1 k, a β j * (u β j + v β j * c β j ^ n) * (1 + |ε n|)) with hT
  set L : ℝ := ∑ β ∈ Ir, ((p : ℝ) ^ (k * β.natDegree))⁻¹ *
    (1 + ∑ j ∈ Finset.Icc 1 k, a β j * u β j) with hL
  have hRj : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.Icc 1 k, (p, j * d) ∈ Rn (1 / 4) n := by
    rw [Filter.eventually_all_finset]
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact eventually_mem_Rn (by norm_num) (by norm_num) hp.out (Nat.mul_pos (by omega) hd)
  have hbound : ∀ᶠ n : ℕ in atTop, prob (fun ω : Pairs n → Bool =>
      ∃ β ∈ Ir, β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly) ≤ T n := by
    filter_upwards [hev, hRj, prob_not_noShort (δ := 1 / 4) (by norm_num) le_rfl] with n hn hR hN
    have hsplit : prob (fun ω : Pairs n → Bool =>
        ∃ β ∈ Ir, β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly) ≤
        prob (fun ω : Pairs n → Bool => ¬ NoShort (1 / 4) n ω) +
          prob (fun ω : Pairs n → Bool =>
            ∃ β ∈ Ir, β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly ∧ NoShort (1 / 4) n ω) := by
      refine (prob_mono fun ω h => ?_).trans (prob_or_le _ _)
      by_cases hN' : NoShort (1 / 4) n ω
      · right
        obtain ⟨β, hβ, h⟩ := h
        exact ⟨β, hβ, h, hN'⟩
      · left
        exact hN'
    have hβbound : ∀ β ∈ Ir, prob (fun ω : Pairs n → Bool =>
        β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly ∧ NoShort (1 / 4) n ω) ≤
        ((p : ℝ) ^ (k * β.natDegree))⁻¹ *
          (1 + ∑ j ∈ Finset.Icc 1 k, a β j * (u β j + v β j * c β j ^ n) * (1 + |ε n|)) := by
      intro β hβ
      obtain ⟨hβm, hβi, hβd⟩ := hIrdeg β hβ
      have hR' : ∀ j ∈ Finset.Icc 1 k, (p, j * β.natDegree) ∈ Rn (1 / 4) n := by
        intro j hj; rw [hβd]; exact hR j hj
      refine (prob_tight_beta_le hβi hβm hR').trans ?_
      have hpk : (0 : ℝ) ≤ ((p : ℝ) ^ (k * β.natDegree))⁻¹ := by positivity
      refine mul_le_mul_of_nonneg_left (add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_)) hpk
      have hj' := Finset.mem_Icc.1 hj
      have hD1 : 1 ≤ j * β.natDegree := Nat.mul_pos hj'.1 hβi.natDegree_pos
      refine sum_tFrames_prob_le n hD1 (by positivity) fun V hV => ?_
      rw [mem_tFrames_iff] at hV
      have hrob : IsRobust (sDelta (1 / 4) n) (V.map (ZMod.cast : ZMod p → ZMod p)) := by
        have : V.map (ZMod.cast : ZMod p → ZMod p) = V := by
          ext i l; exact ZMod.cast_id p (V i l)
        rw [this]; exact hV.1
      obtain ⟨-, -, hR2, hR3⟩ := hR' j hj
      have h := hn p 1 p (j * β.natDegree) (pow_one p).symm le_rfl hD1 hR2 hR3 V hrob
        (V * compMat (β ^ j) (j * β.natDegree))
      refine h.trans ?_
      gcongr
      exact le_abs_self _
    have hNle := hN
    calc prob (fun ω : Pairs n → Bool => ∃ β ∈ Ir, β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly)
        ≤ prob (fun ω : Pairs n → Bool => ¬ NoShort (1 / 4) n ω) +
          prob (fun ω : Pairs n → Bool =>
            ∃ β ∈ Ir, β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly ∧ NoShort (1 / 4) n ω) := hsplit
      _ ≤ Real.exp (-(n : ℝ) / 8) + ∑ β ∈ Ir, prob (fun ω : Pairs n → Bool =>
            β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly ∧ NoShort (1 / 4) n ω) :=
          add_le_add hNle (prob_exists_le_sum Ir (fun β ω =>
            β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly ∧ NoShort (1 / 4) n ω))
      _ ≤ T n := by
          rw [hT]
          dsimp only
          exact add_le_add le_rfl (Finset.sum_le_sum hβbound)
  have hlim : Tendsto T atTop (𝓝 (0 + L)) := by
    have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) / 8)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_div_const (show (0 : ℝ) < 8 by norm_num))
      refine this.congr fun n => ?_
      simp only [Function.comp]; ring_nf
    rw [hT, hL]
    refine hexp.add (tendsto_finsetSum _ fun β hβ => ?_)
    refine Tendsto.const_mul _ (tendsto_const_nhds.add (tendsto_finsetSum _ fun j hj => ?_))
    have hj' := Finset.mem_Icc.1 hj
    have hD1 : 1 ≤ j * β.natDegree := Nat.mul_pos hj'.1 (hIrdeg β hβ).2.1.natDegree_pos
    obtain ⟨hc0, hc1, -⟩ := cGram_bounds (q := p) (r := j * β.natDegree) hp.out.two_le hD1
    exact tendsto_tight_term (a β j) (u β j) (v β j) (c β j) hc0 hc1 hε
  have hLle : L ≤ (k + 1) * piCount p d * ((p : ℝ) ^ (k / 2 * d))⁻¹ := by
    have hterm : ∀ β ∈ Ir, ((p : ℝ) ^ (k * β.natDegree))⁻¹ *
        (1 + ∑ j ∈ Finset.Icc 1 k, a β j * u β j) ≤ (k + 1) * ((p : ℝ) ^ (k / 2 * d))⁻¹ := by
      intro β hβ
      obtain ⟨hβm, hβi, hβd⟩ := hIrdeg β hβ
      have hj : ∀ j ∈ Finset.Icc 1 k, a β j * u β j ≤ (p : ℝ) ^ ((k - k / 2) * d) := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        have h := card_Sset_antisymm_le hβi hβm hj.1 hj.2
        rw [hβd] at h
        simp only [ha, hu]
        rw [← hβd] at h ⊢
        exact h
      have hsum : ∑ j ∈ Finset.Icc 1 k, a β j * u β j ≤ k * (p : ℝ) ^ ((k - k / 2) * d) := by
        calc ∑ j ∈ Finset.Icc 1 k, a β j * u β j
            ≤ ∑ _j ∈ Finset.Icc 1 k, (p : ℝ) ^ ((k - k / 2) * d) := Finset.sum_le_sum hj
          _ = k * (p : ℝ) ^ ((k - k / 2) * d) := by
              rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
              simp
      have hone : (1 : ℝ) ≤ (p : ℝ) ^ ((k - k / 2) * d) := one_le_pow₀ hp1
      have hsplit : (p : ℝ) ^ (k * d) = (p : ℝ) ^ (k / 2 * d) * (p : ℝ) ^ ((k - k / 2) * d) := by
        rw [← pow_add, ← add_mul]
        congr 2
        omega
      rw [hβd, hsplit, mul_inv]
      have hB : (0 : ℝ) < (p : ℝ) ^ ((k - k / 2) * d) := by positivity
      have hA : (0 : ℝ) < (p : ℝ) ^ (k / 2 * d) := by positivity
      calc ((p : ℝ) ^ (k / 2 * d))⁻¹ * ((p : ℝ) ^ ((k - k / 2) * d))⁻¹ *
            (1 + ∑ j ∈ Finset.Icc 1 k, a β j * u β j)
          ≤ ((p : ℝ) ^ (k / 2 * d))⁻¹ * ((p : ℝ) ^ ((k - k / 2) * d))⁻¹ *
            ((k + 1) * (p : ℝ) ^ ((k - k / 2) * d)) := by
            gcongr
            linarith
        _ = (k + 1) * ((p : ℝ) ^ (k / 2 * d))⁻¹ := by field_simp
    calc L ≤ ∑ _β ∈ Ir, (k + 1) * ((p : ℝ) ^ (k / 2 * d))⁻¹ := Finset.sum_le_sum hterm
      _ = (k + 1) * piCount p d * ((p : ℝ) ^ (k / 2 * d))⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul, piCount, hIr]
          ring
  have hlt : 0 + L < L + η := by linarith
  filter_upwards [hbound, (tendsto_order.1 hlim).2 (L + η) hlt] with n h1 h2
  linarith

end PropA

end DGS
