module

public import DGS.S03_Prelim.SignVectors
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.FieldTheory.Minpoly.MinpolyDiv
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.FieldTheory.PrimitiveElement

@[expose] public section

open Matrix Polynomial Module

namespace DGS

section PolyMatrix

variable {m : ℕ}

theorem isInvariant_aeval {F : Type*} [Field F] {M : Matrix (Fin m) (Fin m) F}
    {W : Submodule F (Fin m → F)} (hW : IsInvariant M W) (f : F[X]) :
    ∀ u ∈ W, aeval M f *ᵥ u ∈ W := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    intro u hu
    rw [map_add, add_mulVec]
    exact W.add_mem (hp u hu) (hq u hu)
  | monomial n a =>
    intro u hu
    rw [aeval_monomial, ← mulVec_mulVec, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec]
    apply W.smul_mem
    induction n with
    | zero => simpa using hu
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec]
      exact hW _ ih

theorem pow_mulVec_of_eigen {F : Type*} [Field F] {N : Matrix (Fin m) (Fin m) F} {w : Fin m → F}
    {μ : F} (h : N *ᵥ w = μ • w) (k : ℕ) : N ^ k *ᵥ w = μ ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, h, smul_smul, pow_succ]

theorem aeval_mulVec_of_eigen {R F : Type*} [CommRing R] [Field F] [Algebra R F]
    {N : Matrix (Fin m) (Fin m) F} {w : Fin m → F} {μ : F} (h : N *ᵥ w = μ • w) (f : R[X]) :
    aeval N f *ᵥ w = aeval μ f • w := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, add_mulVec, hp, hq, add_smul]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, ← mulVec_mulVec, pow_mulVec_of_eigen h,
      Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec, mul_smul, algebraMap_smul]

theorem aeval_mul_comm {S A : Type*} [CommSemiring S] [Semiring A] [Algebra S A] (x : A) (f : S[X]) :
    aeval x f * x = x * aeval x f := by
  have h := congrArg (aeval x) (mul_comm f X)
  rwa [map_mul, map_mul, aeval_X] at h

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem aeval_map_matrix (N : Matrix (Fin m) (Fin m) K) (f : K[X]) :
    aeval (N.map (algebraMap K L)) f = (aeval N f).map (algebraMap K L) := by
  have e : ∀ Y : Matrix (Fin m) (Fin m) K,
      (Algebra.ofId K L).mapMatrix Y = Y.map (algebraMap K L) := fun Y => by
    ext i j
    simp [Algebra.ofId_apply]
  rw [← e, ← e]
  exact Polynomial.aeval_algHom_apply _ _ _

variable (K) in
def liftVec (v : Fin m → K) : Fin m → L := fun i => algebraMap K L (v i)

@[simp] theorem liftVec_apply (v : Fin m → K) (i : Fin m) :
    (liftVec K v : Fin m → L) i = algebraMap K L (v i) := rfl

theorem liftVec_mulVec (N : Matrix (Fin m) (Fin m) K) (v : Fin m → K) :
    (liftVec K (N *ᵥ v) : Fin m → L) = N.map (algebraMap K L) *ᵥ liftVec K v := by
  funext i
  simp [liftVec, mulVec, dotProduct, map_sum]

theorem liftVec_dotProduct (y v : Fin m → K) :
    algebraMap K L (y ⬝ᵥ v) = (liftVec K y : Fin m → L) ⬝ᵥ liftVec K v := by
  simp [dotProduct, map_sum]

end PolyMatrix

section Types

variable {F : Type*} [Field F] {m : ℕ}

theorem exists_hasType_aux (M : Matrix (Fin m) (Fin m) F) {U : Submodule F (Fin m → F)}
    (hU : IsSimpleInvariant M U) : ∃ β : F[X], HasType M U β := by
  classical
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.2.1
  have key : ∀ f : F[X], f ≠ 0 → ∀ u ∈ U, u ≠ 0 → aeval M f *ᵥ u = 0 →
      ∃ β : F[X], Irreducible β ∧ ∃ u' ∈ U, u' ≠ 0 ∧ aeval M β *ᵥ u' = 0 := by
    intro f
    induction f using WfDvdMonoid.induction_on_irreducible with
    | zero => intro h; exact absurd rfl h
    | unit c hc =>
      intro _ u _ hu0 hcu
      exfalso
      obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.1 hc
      rw [aeval_C, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec] at hcu
      exact hu0 ((smul_eq_zero.1 hcu).resolve_left hr.ne_zero)
    | mul a i ha hi ih =>
      intro _ u huU hu0 hiu
      by_cases hau : aeval M a *ᵥ u = 0
      · exact ih ha u huU hu0 hau
      · refine ⟨i, hi, aeval M a *ᵥ u, isInvariant_aeval hU.1 a u huU, hau, ?_⟩
        rw [mulVec_mulVec, ← map_mul]
        exact hiu
  obtain ⟨β₀, hβ₀, u', hu'U, hu'0, hβ₀u'⟩ :=
    key M.charpoly (Matrix.charpoly_monic M).ne_zero u huU hu0
      (by rw [Matrix.aeval_self_charpoly, zero_mulVec])
  have hne : β₀ ≠ 0 := hβ₀.ne_zero
  set β := β₀ * C β₀.leadingCoeff⁻¹ with hβdef
  have hβirr : Irreducible β :=
    (irreducible_mul_isUnit (Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2
      (inv_ne_zero (leadingCoeff_ne_zero.2 hne))))).2 hβ₀
  have hβu' : aeval M β *ᵥ u' = 0 := by
    rw [hβdef, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one,
      smul_mulVec, hβ₀u', smul_zero]
  let W : Submodule F (Fin m → F) := U ⊓ LinearMap.ker (aeval M β).mulVecLin
  have hWinv : IsInvariant M W := by
    intro x hx
    refine ⟨hU.1 x hx.1, ?_⟩
    have hx2 : aeval M β *ᵥ x = 0 := hx.2
    show (aeval M β).mulVecLin (M *ᵥ x) = 0
    rw [mulVecLin_apply, mulVec_mulVec, aeval_mul_comm, ← mulVec_mulVec, hx2, mulVec_zero]
  have hW : W = U := (hU.2.2 W hWinv inf_le_left).resolve_left (fun hb => hu'0 (by
    have : u' ∈ W := ⟨hu'U, hβu'⟩
    rw [hb] at this
    exact this))
  refine ⟨β, Polynomial.monic_mul_leadingCoeff_inv hne, hβirr, fun x hx => ?_⟩
  have : x ∈ W := hW ▸ hx
  exact this.2

theorem hasType_unique_aux (M : Matrix (Fin m) (Fin m) F) {U : Submodule F (Fin m → F)}
    (hU0 : U ≠ ⊥) {β β' : F[X]} (hβ : HasType M U β) (hβ' : HasType M U β') : β = β' := by
  classical
  by_contra hne
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hnd : ¬ β ∣ β' := fun hd =>
    hne (eq_of_monic_of_associated hβ.1 hβ'.1 (hβ.2.1.associated_of_dvd hβ'.2.1 hd))
  obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hβ.2.1).2 hnd
  apply hu0
  have h1 := congrArg (fun f => aeval M f *ᵥ u) hab
  simp only [map_add, map_mul, map_one, add_mulVec, one_mulVec, ← mulVec_mulVec, hβ.2.2 u huU,
    hβ'.2.2 u huU, mulVec_zero, add_zero] at h1
  exact h1.symm

end Types

section Trace

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {m : ℕ}

variable (K) in
noncomputable def trVec : (Fin m → L) →ₗ[K] (Fin m → K) :=
  LinearMap.pi fun i => (Algebra.trace K L).comp (LinearMap.proj i)

@[simp] theorem trVec_apply (w : Fin m → L) (i : Fin m) :
    trVec K w i = Algebra.trace K L (w i) := rfl

noncomputable def eigsp (M : Matrix (Fin m) (Fin m) K) (μ : L) : Submodule L (Fin m → L) :=
  Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap K L))) μ

theorem mem_eigsp {M : Matrix (Fin m) (Fin m) K} {μ : L} {w : Fin m → L} :
    w ∈ eigsp M μ ↔ M.map (algebraMap K L) *ᵥ w = μ • w := by
  rw [eigsp, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

theorem smul_mem_eigsp {M : Matrix (Fin m) (Fin m) K} {μ : L} {w : Fin m → L} (hw : w ∈ eigsp M μ)
    (c : L) : c • w ∈ eigsp M μ :=
  (eigsp M μ).smul_mem c hw

variable (K) in
noncomputable def trMul (w : Fin m → L) : L →ₗ[K] (Fin m → K) where
  toFun c := trVec K (c • w)
  map_add' c c' := by rw [add_smul, map_add]
  map_smul' a c := by simp only [smul_assoc, map_smul, RingHom.id_apply]

variable (K) in
noncomputable def Uw (w : Fin m → L) : Submodule K (Fin m → K) :=
  LinearMap.range (trMul K w)

theorem mem_Uw {w : Fin m → L} {u : Fin m → K} : u ∈ Uw K w ↔ ∃ c : L, trVec K (c • w) = u :=
  Iff.rfl

theorem trVec_mem_Uw (w : Fin m → L) (c : L) : trVec K (c • w) ∈ Uw K w := ⟨c, rfl⟩

theorem trVec_mulVec_map (N : Matrix (Fin m) (Fin m) K) (w : Fin m → L) :
    trVec K (N.map (algebraMap K L) *ᵥ w) = N *ᵥ trVec K w := by
  funext i
  simp only [trVec_apply, mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem trVec_aeval_smul {M : Matrix (Fin m) (Fin m) K} {μ : L} {w : Fin m → L}
    (hw : w ∈ eigsp M μ) (f : K[X]) : trVec K (aeval μ f • w) = aeval M f *ᵥ trVec K w := by
  rw [← aeval_mulVec_of_eigen (mem_eigsp.1 hw) f, aeval_map_matrix, trVec_mulVec_map]

theorem dotProduct_trVec (y : Fin m → K) (w : Fin m → L) (c : L) :
    y ⬝ᵥ trVec K (c • w) = Algebra.trace K L (c * (liftVec K y ⬝ᵥ w)) := by
  simp only [dotProduct, trVec_apply, Pi.smul_apply, smul_eq_mul, liftVec_apply, Finset.mul_sum,
    map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show c * (algebraMap K L (y k) * w k) = y k • (c * w k) by
    rw [Algebra.smul_def]; ring, LinearMap.map_smul, smul_eq_mul]

structure IsGenRoot (β : K[X]) (μ : L) : Prop where
  monic : β.Monic
  irreducible : Irreducible β
  aeval_eq_zero : aeval μ β = 0
  finrank_eq : finrank K L = β.natDegree

namespace IsGenRoot

variable {β : K[X]} {μ : L} (h : IsGenRoot β μ)
include h

theorem minpoly_eq : minpoly K μ = β :=
  (minpoly.eq_of_irreducible_of_monic h.irreducible h.aeval_eq_zero h.monic).symm

variable [FiniteDimensional K L]

theorem adjoin_eq_top : IntermediateField.adjoin K {μ} = ⊤ :=
  (Field.primitive_element_iff_minpoly_natDegree_eq K μ).2 (by rw [h.minpoly_eq, h.finrank_eq])

noncomputable def powerBasis : PowerBasis K L :=
  PowerBasis.ofAdjoinSimpleEqTop (IsIntegral.of_finite K μ) h.adjoin_eq_top

theorem powerBasis_gen : h.powerBasis.gen = μ :=
  PowerBasis.ofAdjoinSimpleEqTop_gen _ _

theorem exists_aeval (c : L) : ∃ f : K[X], aeval μ f = c := by
  obtain ⟨f, hf⟩ := h.powerBasis.exists_eq_aeval' c
  exact ⟨f, by rw [hf, h.powerBasis_gen]⟩

theorem algEquiv_ext {σ τ : L ≃ₐ[K] L} (hστ : σ μ = τ μ) : σ = τ := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply h.powerBasis.algHom_ext
  simpa [h.powerBasis_gen] using hστ

variable [Algebra.IsSeparable K L]

omit [FiniteDimensional K L] in
theorem derivative_ne_zero : aeval μ (derivative β) ≠ 0 := by
  have hs : IsSeparable K μ := Algebra.IsSeparable.isSeparable K μ
  rw [IsSeparable, h.minpoly_eq] at hs
  exact hs.aeval_derivative_ne_zero h.aeval_eq_zero

theorem trace_coeff_minpolyDiv (i : ℕ) :
    Algebra.trace K L ((minpolyDiv K μ).coeff i / aeval μ (derivative β)) =
      if i = 0 then 1 else 0 := by
  classical
  by_cases hi : i < h.powerBasis.dim
  · have h1 := Module.Basis.trace_traceDual_mul h.powerBasis.basis ⟨i, hi⟩
      ⟨0, h.powerBasis.dim_pos⟩
    rw [Module.Basis.traceDual_powerBasis_eq] at h1
    simp only [PowerBasis.coe_basis, pow_zero, mul_one, h.powerBasis_gen, h.minpoly_eq,
      Fin.mk.injEq] at h1
    rw [h1]
    by_cases hi0 : i = 0 <;> simp [hi0, eq_comm]
  · have hd : (minpolyDiv K μ).natDegree < i := by
      have h2 := natDegree_minpolyDiv_lt (R := K) (IsIntegral.of_finite K μ)
      rw [h.minpoly_eq, ← h.finrank_eq, h.powerBasis.finrank] at h2
      omega
    have hi0 : i ≠ 0 := by have := h.powerBasis.dim_pos; omega
    rw [coeff_eq_zero_of_natDegree_lt hd, zero_div, map_zero, ite_eq_right hi0]

end IsGenRoot

variable {β : K[X]} {μ : L} {M : Matrix (Fin m) (Fin m) K}

theorem trVec_kills (h : IsGenRoot β μ) {w : Fin m → L} (hw : w ∈ eigsp M μ) :
    aeval M β *ᵥ trVec K w = 0 := by
  rw [← trVec_aeval_smul hw, h.aeval_eq_zero, zero_smul, map_zero]

theorem trVec_smul_self {w : Fin m → L} (hw : w ∈ eigsp M μ) :
    trVec K (μ • w) = M *ᵥ trVec K w := by
  simpa using trVec_aeval_smul hw X

variable [FiniteDimensional K L]

theorem trVec_eq_zero_iff [Algebra.IsSeparable K L] (h : IsGenRoot β μ) {w : Fin m → L}
    (hw : w ∈ eigsp M μ) : trVec K w = 0 ↔ w = 0 := by
  refine ⟨fun h0 => ?_, fun h0 => by rw [h0, map_zero]⟩
  have hc : ∀ c : L, trVec K (c • w) = 0 := by
    intro c
    obtain ⟨f, rfl⟩ := h.exists_aeval c
    rw [trVec_aeval_smul hw, h0, mulVec_zero]
  funext i
  show w i = 0
  refine (traceForm_nondegenerate K L).1 (w i) fun c => ?_
  have h1 := congrFun (hc c) i
  rw [trVec_apply, Pi.smul_apply, smul_eq_mul] at h1
  rw [Algebra.traceForm_apply, mul_comm]
  exact h1

theorem exists_trVec_eq [Algebra.IsSeparable K L] (h : IsGenRoot β μ) {v : Fin m → K}
    (hv : aeval M β *ᵥ v = 0) : ∃ w ∈ eigsp M μ, trVec K w = v := by
  classical
  have hspec : minpolyDiv K μ * (X - C μ) = β.map (algebraMap K L) := by
    rw [minpolyDiv_spec, h.minpoly_eq]
  have hyE : M.map (algebraMap K L) *ᵥ (aeval (M.map (algebraMap K L)) (minpolyDiv K μ) *ᵥ
      liftVec K v) = μ • (aeval (M.map (algebraMap K L)) (minpolyDiv K μ) *ᵥ liftVec K v) := by
    have h1 : aeval (M.map (algebraMap K L)) (minpolyDiv K μ * (X - C μ)) *ᵥ liftVec K v = 0 := by
      rw [hspec, aeval_map_algebraMap, aeval_map_matrix, ← liftVec_mulVec, hv]
      funext i
      simp
    rw [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, mul_sub,
      Matrix.mul_smul, mul_one, sub_mulVec, smul_mulVec, sub_eq_zero] at h1
    rw [mulVec_mulVec, ← aeval_mul_comm, h1]
  refine ⟨(aeval μ (derivative β))⁻¹ • (aeval (M.map (algebraMap K L)) (minpolyDiv K μ) *ᵥ
    liftVec K v), ?_, ?_⟩
  · rw [mem_eigsp, mulVec_smul, hyE, smul_comm]
  · have key : ∀ (c : L) (a : K), Algebra.trace K L ((aeval μ (derivative β))⁻¹ *
        (c * algebraMap K L a)) = a * Algebra.trace K L (c / aeval μ (derivative β)) := by
      intro c a
      rw [show (aeval μ (derivative β))⁻¹ * (c * algebraMap K L a) =
        a • (c / aeval μ (derivative β)) by rw [Algebra.smul_def, div_eq_mul_inv]; ring,
        LinearMap.map_smul, smul_eq_mul]
    have hcoord : ∀ (i : Fin m) (j : ℕ), (((minpolyDiv K μ).coeff j •
        (M.map (algebraMap K L)) ^ j) *ᵥ liftVec K v) i =
          (minpolyDiv K μ).coeff j * algebraMap K L ((M ^ j *ᵥ v) i) := by
      intro i j
      rw [← Matrix.map_pow, smul_mulVec, ← liftVec_mulVec]
      rfl
    funext i
    rw [trVec_apply, Pi.smul_apply, smul_eq_mul,
      aeval_eq_sum_range (p := minpolyDiv K μ) (M.map (algebraMap K L)), Matrix.sum_mulVec,
      Finset.sum_apply]
    simp only [hcoord]
    rw [Finset.mul_sum, map_sum,
      Finset.sum_eq_single 0 (fun j _ hj => ?_) (fun h0 => absurd (Finset.mem_range.2
        (Nat.succ_pos _)) h0)]
    · rw [key, h.trace_coeff_minpolyDiv, ite_eq_left rfl, mul_one, pow_zero, one_mulVec]
    · rw [key, h.trace_coeff_minpolyDiv, ite_eq_right hj, mul_zero]

theorem lem_simple_a_iso [Algebra.IsSeparable K L] (h : IsGenRoot β μ)
    (M : Matrix (Fin m) (Fin m) K) :
    (∀ w ∈ eigsp M μ, aeval M β *ᵥ trVec K w = 0) ∧
      (∀ w ∈ eigsp M μ, trVec K (μ • w) = M *ᵥ trVec K w) ∧
      (∀ w ∈ eigsp M μ, ∀ w' ∈ eigsp M μ, trVec K w = trVec K w' → w = w') ∧
      (∀ v : Fin m → K, aeval M β *ᵥ v = 0 → ∃ w ∈ eigsp M μ, trVec K w = v) := by
  refine ⟨fun w hw => trVec_kills h hw, fun w hw => trVec_smul_self hw, ?_,
    fun v hv => exists_trVec_eq h hv⟩
  intro w hw w' hw' hww'
  have hd : w - w' ∈ eigsp M μ := (eigsp M μ).sub_mem hw hw'
  exact sub_eq_zero.1 ((trVec_eq_zero_iff h hd).1 (by rw [map_sub, hww', sub_self]))

omit [FiniteDimensional K L] in
theorem Uw_isInvariant {w : Fin m → L} (hw : w ∈ eigsp M μ) : IsInvariant M (Uw K w) := by
  rintro _ ⟨c, rfl⟩
  refine ⟨μ * c, ?_⟩
  show trVec K ((μ * c) • w) = M *ᵥ trVec K (c • w)
  rw [mul_smul, trVec_smul_self (smul_mem_eigsp hw c)]

omit [FiniteDimensional K L] in
theorem Uw_kills (h : IsGenRoot β μ) {w : Fin m → L} (hw : w ∈ eigsp M μ) :
    ∀ u ∈ Uw K w, aeval M β *ᵥ u = 0 := by
  rintro _ ⟨c, rfl⟩
  exact trVec_kills h (smul_mem_eigsp hw c)

variable [Algebra.IsSeparable K L]

theorem trMul_injective (h : IsGenRoot β μ) {w : Fin m → L} (hw : w ∈ eigsp M μ) (hw0 : w ≠ 0) :
    Function.Injective (trMul K w) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have h1 : c • w = 0 := (trVec_eq_zero_iff h (smul_mem_eigsp hw c)).1 hc
  exact (smul_eq_zero.1 h1).resolve_right hw0

theorem finrank_Uw (h : IsGenRoot β μ) {w : Fin m → L} (hw : w ∈ eigsp M μ) (hw0 : w ≠ 0) :
    finrank K (Uw K w) = β.natDegree := by
  rw [Uw, LinearMap.finrank_range_of_inj (trMul_injective h hw hw0), h.finrank_eq]

theorem Uw_isSimple (h : IsGenRoot β μ) {w : Fin m → L} (hw : w ∈ eigsp M μ) (hw0 : w ≠ 0) :
    IsSimpleInvariant M (Uw K w) := by
  refine ⟨Uw_isInvariant hw, ?_, ?_⟩
  · intro hbot
    have h1 : trVec K ((1 : L) • w) ∈ Uw K w := trVec_mem_Uw w 1
    rw [hbot, Submodule.mem_bot, one_smul, trVec_eq_zero_iff h hw] at h1
    exact hw0 h1
  · intro W hW hWU
    by_cases hb : W = ⊥
    · exact Or.inl hb
    right
    apply le_antisymm hWU
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨c, rfl⟩ := mem_Uw.1 (hWU hxW)
    have hc : c ≠ 0 := by
      rintro rfl
      rw [zero_smul, map_zero] at hx0
      exact hx0 rfl
    rintro _ ⟨c', rfl⟩
    obtain ⟨f, hf⟩ := h.exists_aeval (c' / c)
    have h1 : c' • w = aeval μ f • (c • w) := by rw [hf, smul_smul, div_mul_cancel₀ _ hc]
    show trVec K (c' • w) ∈ W
    rw [h1, trVec_aeval_smul (smul_mem_eigsp hw c)]
    exact isInvariant_aeval hW f _ hxW

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
theorem Uw_hasType (h : IsGenRoot β μ) {w : Fin m → L} (hw : w ∈ eigsp M μ) :
    HasType M (Uw K w) β :=
  ⟨h.monic, h.irreducible, Uw_kills h hw⟩

theorem eq_Uw_of_hasType (h : IsGenRoot β μ) {U : Submodule K (Fin m → K)}
    (hU : IsSimpleInvariant M U) (hβ : HasType M U β) :
    ∃ w ∈ eigsp M μ, w ≠ 0 ∧ U = Uw K w := by
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.2.1
  obtain ⟨w, hw, rfl⟩ := exists_trVec_eq h (hβ.2.2 _ huU)
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hu0 (map_zero _)
  refine ⟨w, hw, hw0, ?_⟩
  have hmem : trVec K w ∈ Uw K w := by simpa using trVec_mem_Uw (K := K) w 1
  have hinv : IsInvariant M (U ⊓ Uw K w) := fun x hx => ⟨hU.1 x hx.1, Uw_isInvariant hw x hx.2⟩
  have h1 : U ⊓ Uw K w = U := (hU.2.2 _ hinv inf_le_left).resolve_left (fun hb => hu0 (by
    have h2 : trVec K w ∈ U ⊓ Uw K w := ⟨huU, hmem⟩
    rw [hb] at h2
    exact h2))
  exact ((Uw_isSimple h hw hw0).2.2 U hU.1 (inf_eq_left.1 h1)).resolve_left hU.2.1

theorem Uw_eq_Uw_iff (h : IsGenRoot β μ) {w w' : Fin m → L} (hw : w ∈ eigsp M μ)
    (hw' : w' ∈ eigsp M μ) (hw0' : w' ≠ 0) :
    Uw K w = Uw K w' ↔ ∃ c : L, w' = c • w := by
  constructor
  · intro heq
    have h1 : trVec K ((1 : L) • w') ∈ Uw K w := by rw [heq]; exact trVec_mem_Uw w' 1
    obtain ⟨c, hc⟩ := mem_Uw.1 h1
    refine ⟨c, ?_⟩
    have hd : c • w - w' ∈ eigsp M μ := (eigsp M μ).sub_mem (smul_mem_eigsp hw c) hw'
    have h2 : trVec K (c • w - w') = 0 := by rw [map_sub, hc, one_smul, sub_self]
    exact (sub_eq_zero.1 ((trVec_eq_zero_iff h hd).1 h2)).symm
  · rintro ⟨c, rfl⟩
    have hc : c ≠ 0 := by
      rintro rfl
      exact hw0' (zero_smul _ _)
    apply le_antisymm
    · rintro _ ⟨c', rfl⟩
      exact ⟨c' / c, show trVec K ((c' / c) • c • w) = trVec K (c' • w) by
        rw [smul_smul, div_mul_cancel₀ _ hc]⟩
    · rintro _ ⟨c', rfl⟩
      exact ⟨c' * c, show trVec K ((c' * c) • w) = trVec K (c' • (c • w)) by rw [smul_smul]⟩

theorem lem_simple_a (h : IsGenRoot β μ) (M : Matrix (Fin m) (Fin m) K) :
    (∀ w ∈ eigsp M μ, w ≠ 0 →
      IsSimpleInvariant M (Uw K w) ∧ HasType M (Uw K w) β ∧ finrank K (Uw K w) = β.natDegree) ∧
    (∀ U : Submodule K (Fin m → K), IsSimpleInvariant M U → HasType M U β →
      ∃ w ∈ eigsp M μ, w ≠ 0 ∧ U = Uw K w) ∧
    (∀ w ∈ eigsp M μ, ∀ w' ∈ eigsp M μ, w ≠ 0 → w' ≠ 0 →
      (Uw K w = Uw K w' ↔ ∃ c : L, w' = c • w)) :=
  ⟨fun _ hw hw0 => ⟨Uw_isSimple h hw hw0, Uw_hasType h hw, finrank_Uw h hw hw0⟩,
    fun _ hU hβ => eq_Uw_of_hasType h hU hβ,
    fun _ hw _ hw' _ hw0' => Uw_eq_Uw_iff h hw hw' hw0'⟩

theorem dotProduct_eq_zero_of_eigen {F : Type*} [Field F] {N : Matrix (Fin m) (Fin m) F}
    (hN : Nᵀ = N) {x y : Fin m → F} {a b : F} (hx : N *ᵥ x = a • x) (hy : N *ᵥ y = b • y)
    (hab : a ≠ b) : x ⬝ᵥ y = 0 := by
  have h1 : (N *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (N *ᵥ y) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hN]
  have h2 : a * (x ⬝ᵥ y) = b * (x ⬝ᵥ y) := by
    rw [← smul_eq_mul, ← smul_eq_mul, ← smul_dotProduct, ← dotProduct_smul, ← hx, ← hy, h1]
  by_contra hxy
  exact hab (mul_right_cancel₀ hxy h2)

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
theorem map_algEquiv_mem_eigsp {w : Fin m → L} (hw : w ∈ eigsp M μ) (σ : L ≃ₐ[K] L) :
    (fun k => σ (w k)) ∈ eigsp M (σ μ) := by
  rw [mem_eigsp] at hw ⊢
  funext i
  have h1 := congrArg σ (congrFun hw i)
  simpa [mulVec, dotProduct, map_sum, map_mul, AlgEquiv.commutes] using h1

omit [Algebra.IsSeparable K L] in
theorem trVec_dotProduct_trVec [Finite L] (h : IsGenRoot β μ) (hM : M.IsSymm) {w : Fin m → L}
    (hw : w ∈ eigsp M μ) (c c' : L) :
    trVec K (c • w) ⬝ᵥ trVec K (c' • w) = Algebra.trace K L (c * c' * (w ⬝ᵥ w)) := by
  classical
  apply (algebraMap K L).injective
  have hMb : (M.map (algebraMap K L))ᵀ = M.map (algebraMap K L) := by rw [← transpose_map, hM.eq]
  have hx := smul_mem_eigsp hw c
  have hy := smul_mem_eigsp hw c'
  have hxy : c * c' * (w ⬝ᵥ w) = (c • w) ⬝ᵥ (c' • w) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  have expand : algebraMap K L (trVec K (c • w) ⬝ᵥ trVec K (c' • w)) =
      ∑ σ : L ≃ₐ[K] L, ∑ τ : L ≃ₐ[K] L,
        (fun k => σ ((c • w) k)) ⬝ᵥ (fun k => τ ((c' • w) k)) := by
    simp only [dotProduct, map_sum, map_mul, trVec_apply, trace_eq_sum_automorphisms,
      Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm]
  rw [expand, hxy, trace_eq_sum_automorphisms]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single σ (fun τ _ hτ => dotProduct_eq_zero_of_eigen hMb
    (mem_eigsp.1 (map_algEquiv_mem_eigsp hx σ)) (mem_eigsp.1 (map_algEquiv_mem_eigsp hy τ))
    (fun he => hτ (h.algEquiv_ext he).symm)) (fun h0 => absurd (Finset.mem_univ σ) h0)]
  simp [dotProduct, map_sum, map_mul]

theorem lem_simple_b [Finite L] (h : IsGenRoot β μ) (hM : M.IsSymm) {w : Fin m → L}
    (hw : w ∈ eigsp M μ) :
    (∀ c c' : L, trVec K (c • w) ⬝ᵥ trVec K (c' • w) = Algebra.trace K L (c * c' * (w ⬝ᵥ w))) ∧
      (IsTotallyIsotropic (Uw K w) ↔ w ⬝ᵥ w = 0) := by
  refine ⟨trVec_dotProduct_trVec h hM hw, ⟨fun hiso => ?_, fun h0 => ?_⟩⟩
  · refine (traceForm_nondegenerate K L).1 (w ⬝ᵥ w) fun c => ?_
    have h1 := hiso _ (trVec_mem_Uw w 1) _ (trVec_mem_Uw w c)
    rw [trVec_dotProduct_trVec h hM hw, one_mul] at h1
    rw [Algebra.traceForm_apply, mul_comm]
    exact h1
  · rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩
    show trVec K (c • w) ⬝ᵥ trVec K (c' • w) = 0
    rw [trVec_dotProduct_trVec h hM hw, h0, mul_zero, map_zero]

theorem Uw_isTotallyIsotropic_iff [Finite L] (h : IsGenRoot β μ) (hM : M.IsSymm) {w : Fin m → L}
    (hw : w ∈ eigsp M μ) : IsTotallyIsotropic (Uw K w) ↔ w ⬝ᵥ w = 0 :=
  (lem_simple_b h hM hw).2

theorem lem_simple_c (y : Fin m → K) (w : Fin m → L) :
    (∀ u ∈ Uw K w, y ⬝ᵥ u = 0) ↔ liftVec K y ⬝ᵥ w = 0 := by
  constructor
  · intro hy
    refine (traceForm_nondegenerate K L).1 _ fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm, ← dotProduct_trVec]
    exact hy _ (trVec_mem_Uw w c)
  · rintro h0 _ ⟨c, rfl⟩
    show y ⬝ᵥ trVec K (c • w) = 0
    rw [dotProduct_trVec, h0, mul_zero, map_zero]

theorem lem_simple_c_prob {Ω : Type*} (ξ : Ω → Fin m → K) (w : Fin m → L) :
    prob (fun ω => ∀ u ∈ Uw K w, ξ ω ⬝ᵥ u = 0) = prob (fun ω => liftVec K (ξ ω) ⬝ᵥ w = 0) :=
  congrArg prob (funext fun ω => propext (lem_simple_c (ξ ω) w))

omit [FiniteDimensional K L] in
theorem lem_simple_d1 (h : IsGenRoot β μ) (M : Matrix (Fin m) (Fin m) K) :
    β ^ 2 ∣ M.charpoly ↔ (X - C μ) ^ 2 ∣ M.charpoly.map (algebraMap K L) := by
  constructor
  · intro hd
    have h1 : X - C μ ∣ β.map (algebraMap K L) := by
      rw [dvd_iff_isRoot, IsRoot, eval_map_algebraMap, h.aeval_eq_zero]
    exact (pow_dvd_pow_of_dvd h1 2).trans (by rw [← Polynomial.map_pow]; exact Polynomial.map_dvd _ hd)
  · intro hd
    have hroot : aeval μ M.charpoly = 0 := by
      have h1 : X - C μ ∣ M.charpoly.map (algebraMap K L) := (dvd_pow_self _ two_ne_zero).trans hd
      rwa [dvd_iff_isRoot, IsRoot, eval_map_algebraMap] at h1
    obtain ⟨g, hg⟩ : β ∣ M.charpoly := by rw [← h.minpoly_eq]; exact minpoly.dvd K μ hroot
    have hgμ : aeval μ g = 0 := by
      have hspec : minpolyDiv K μ * (X - C μ) = β.map (algebraMap K L) := by
        rw [minpolyDiv_spec, h.minpoly_eq]
      rw [hg, Polynomial.map_mul, ← hspec, sq, mul_right_comm] at hd
      have h1 : X - C μ ∣ minpolyDiv K μ * g.map (algebraMap K L) :=
        (mul_dvd_mul_iff_right (X_sub_C_ne_zero μ)).1 hd
      rw [dvd_iff_isRoot, IsRoot, eval_mul, eval_minpolyDiv_self, h.minpoly_eq,
        eval_map_algebraMap] at h1
      exact (mul_eq_zero.1 h1).resolve_left h.derivative_ne_zero
    obtain ⟨g', hg'⟩ : β ∣ g := by rw [← h.minpoly_eq]; exact minpoly.dvd K μ hgμ
    exact ⟨g', by rw [hg, hg', sq, mul_assoc]⟩

theorem sq_dvd_charpoly_iff {F : Type*} [Field F] (N : Matrix (Fin m) (Fin m) F) (hN : Nᵀ = N)
    (μ : F) :
    (X - C μ) ^ 2 ∣ N.charpoly ↔
      2 ≤ finrank F (Module.End.eigenspace (toLin' N) μ) ∨
        (finrank F (Module.End.eigenspace (toLin' N) μ) = 1 ∧ ∀ w ∈ Module.End.eigenspace (toLin' N) μ, w ⬝ᵥ w = 0) := by
  classical
  have hχ : LinearMap.charpoly (toLin' N) = N.charpoly := by
    rw [← LinearMap.charpoly_toMatrix (toLin' N) (Pi.basisFun F (Fin m)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  rw [le_rootMultiplicity_iff (Matrix.charpoly_monic N).ne_zero |>.symm, ← hχ,
    ← LinearMap.finrank_maxGenEigenspace_eq]
  have hψ : ∀ x, (toLin' N - μ • 1) x = N *ᵥ x - μ • x := fun x => by simp
  have hsymm : ∀ x y, ((toLin' N - μ • 1) x) ⬝ᵥ y = x ⬝ᵥ ((toLin' N - μ • 1) y) := by
    intro x y
    rw [hψ, hψ, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul]
    congr 1
    rw [dotProduct_mulVec, ← mulVec_transpose, hN]
  have hE : ∀ x, x ∈ Module.End.eigenspace (toLin' N) μ ↔ (toLin' N - μ • 1) x = 0 := fun x => by
    rw [Module.End.mem_eigenspace_iff, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have hEle : Module.End.eigenspace (toLin' N) μ ≤ Module.End.maxGenEigenspace (toLin' N) μ :=
    Module.End.eigenspace_le_maxGenEigenspace
  constructor
  · intro h2
    by_cases hbig : 2 ≤ finrank F (Module.End.eigenspace (toLin' N) μ)
    · exact Or.inl hbig
    right
    have hz : ∃ z ∈ Module.End.eigenspace (toLin' N) μ, z ≠ 0 ∧ ∃ y, (toLin' N - μ • 1) y = z := by
      by_contra hno
      push Not at hno
      have key : ∀ k : ℕ, ∀ x, ((toLin' N - μ • 1) ^ k) x = 0 → x ∈ Module.End.eigenspace (toLin' N) μ := by
        intro k
        induction k with
        | zero =>
          intro x hx
          rw [pow_zero, Module.End.one_apply] at hx
          rw [hx]
          exact Submodule.zero_mem _
        | succ k ih =>
          intro x hx
          rw [pow_succ, Module.End.mul_apply] at hx
          have h1 := ih _ hx
          by_contra hxE
          exact hno _ h1 (fun h0 => hxE ((hE x).2 h0)) x rfl
      have hle : Module.End.maxGenEigenspace (toLin' N) μ ≤ Module.End.eigenspace (toLin' N) μ := by
        intro x hx
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
        exact key k x hk
      exact hbig (h2.trans (Submodule.finrank_mono hle))
    obtain ⟨z, hzE, hz0, y, rfl⟩ := hz
    have hzz : ((toLin' N - μ • 1) y) ⬝ᵥ ((toLin' N - μ • 1) y) = 0 := by
      rw [hsymm, (hE _).1 hzE, dotProduct_zero]
    have hpos : 1 ≤ finrank F (Module.End.eigenspace (toLin' N) μ) :=
      Submodule.one_le_finrank_iff.2 (fun hb => hz0 (by rw [hb] at hzE; exact hzE))
    have h1 : finrank F (Module.End.eigenspace (toLin' N) μ) = 1 := by omega
    refine ⟨h1, fun w hw => ?_⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨_, hzE⟩ : Module.End.eigenspace (toLin' N) μ)
      (fun h0 => hz0 (congrArg Subtype.val h0))).1 h1 ⟨w, hw⟩
    have hwc : w = c • (toLin' N - μ • 1) y := (congrArg Subtype.val hc).symm
    rw [hwc, smul_dotProduct, dotProduct_smul, hzz, smul_zero, smul_zero]
  · rintro (h2 | ⟨h1, hiso⟩)
    · exact h2.trans (Submodule.finrank_mono hEle)
    · obtain ⟨⟨w₀, hw₀E⟩, hw₀0, hspan⟩ := (finrank_eq_one_iff'.1 h1)
      have hw₀0' : w₀ ≠ 0 := fun h0 => hw₀0 (Subtype.ext h0)
      obtain ⟨V, hV, hVdim⟩ := finrank_orthogonal_dotProduct (Module.End.eigenspace (toLin' N) μ)
      have hker : LinearMap.ker (toLin' N - μ • 1) = Module.End.eigenspace (toLin' N) μ := by
        ext x
        rw [LinearMap.mem_ker, hE]
      have hrange : LinearMap.range (toLin' N - μ • 1) = V := by
        apply Submodule.eq_of_le_of_finrank_eq
        · rintro _ ⟨x, rfl⟩
          rw [hV]
          intro w hw
          rw [hsymm, (hE w).1 hw, dotProduct_zero]
        · have hrk := LinearMap.finrank_range_add_finrank_ker (toLin' N - μ • 1)
          rw [hker, Module.finrank_fin_fun] at hrk
          omega
      have hw₀V : w₀ ∈ V := by
        rw [hV]
        intro w hw
        obtain ⟨c, hc⟩ := hspan ⟨w, hw⟩
        have hwc : w = c • w₀ := (congrArg Subtype.val hc).symm
        rw [hwc, dotProduct_smul, hiso w₀ hw₀E, smul_zero]
      rw [← hrange] at hw₀V
      obtain ⟨x, hx⟩ := hw₀V
      have hxmax : x ∈ Module.End.maxGenEigenspace (toLin' N) μ :=
        (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨2, by
          rw [sq, Module.End.mul_apply, hx]; exact (hE w₀).1 hw₀E⟩
      have hxE : x ∉ Module.End.eigenspace (toLin' N) μ := fun hx' => hw₀0' (by rw [← hx]; exact (hE x).1 hx')
      have hlt : Module.End.eigenspace (toLin' N) μ < Module.End.maxGenEigenspace (toLin' N) μ :=
        lt_of_le_of_ne hEle (fun heq => hxE (heq ▸ hxmax))
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega

omit [FiniteDimensional K L] in
theorem lem_simple_d (h : IsGenRoot β μ) (hM : M.IsSymm) :
    (β ^ 2 ∣ M.charpoly ↔ (X - C μ) ^ 2 ∣ M.charpoly.map (algebraMap K L)) ∧
      ((X - C μ) ^ 2 ∣ M.charpoly.map (algebraMap K L) ↔
        2 ≤ finrank L (eigsp M μ) ∨
          (finrank L (eigsp M μ) = 1 ∧ ∀ w ∈ eigsp M μ, w ⬝ᵥ w = 0)) := by
  refine ⟨lem_simple_d1 h M, ?_⟩
  rw [← Matrix.charpoly_map]
  exact sq_dvd_charpoly_iff _ (by rw [← transpose_map, hM.eq]) μ

theorem lem_simple_d_last [Finite L] (h : IsGenRoot β μ) (hM : M.IsSymm) (hnd : ¬ β ^ 2 ∣ M.charpoly)
    {U : Submodule K (Fin m → K)} (hU : IsSimpleInvariant M U) (hβ : HasType M U β) :
    ¬ IsTotallyIsotropic U := by
  intro hiso
  apply hnd
  obtain ⟨w, hw, hw0, rfl⟩ := eq_Uw_of_hasType h hU hβ
  have hww : w ⬝ᵥ w = 0 := (Uw_isTotallyIsotropic_iff h hM hw).1 hiso
  rw [(lem_simple_d h hM).1, (lem_simple_d h hM).2]
  by_cases h2 : 2 ≤ finrank L (eigsp M μ)
  · exact Or.inl h2
  · right
    have hpos : 1 ≤ finrank L (eigsp M μ) :=
      Submodule.one_le_finrank_iff.2 (fun hb => hw0 (by rw [hb] at hw; exact hw))
    have h1 : finrank L (eigsp M μ) = 1 := by omega
    refine ⟨h1, fun w' hw' => ?_⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hw⟩ : eigsp M μ)
      (fun h0 => hw0 (congrArg Subtype.val h0))).1 h1 ⟨w', hw'⟩
    have hwc : w' = c • w := (congrArg Subtype.val hc).symm
    rw [hwc, smul_dotProduct, dotProduct_smul, hww, smul_zero, smul_zero]

end Trace

section AdjoinRoot

variable {K : Type*} [Field K] {β : K[X]}

theorem isGenRoot_adjoinRoot [Fact (Irreducible β)] (hβ : β.Monic) :
    IsGenRoot β (AdjoinRoot.root β) where
  monic := hβ
  irreducible := Fact.out
  aeval_eq_zero := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  finrank_eq := by rw [(AdjoinRoot.powerBasis hβ.ne_zero).finrank, AdjoinRoot.powerBasis_dim]

theorem finite_adjoinRoot [Finite K] (hβ : β ≠ 0) : Finite (AdjoinRoot β) :=
  haveI : Module.Finite K (AdjoinRoot β) := (AdjoinRoot.powerBasis hβ).finite
  Module.finite_of_finite K

end AdjoinRoot

section TypesFinite

variable {K : Type*} [Field K] [Finite K] {m : ℕ}

theorem exists_hasType (M : Matrix (Fin m) (Fin m) K) (U : Submodule K (Fin m → K))
    (hU : IsSimpleInvariant M U) :
    ∃ β : K[X], HasType M U β ∧ Module.finrank K U = β.natDegree := by
  obtain ⟨β, hβ⟩ := exists_hasType_aux M hU
  refine ⟨β, hβ, ?_⟩
  have : Fact (Irreducible β) := ⟨hβ.2.1⟩
  have : Module.Finite K (AdjoinRoot β) := (AdjoinRoot.powerBasis hβ.1.ne_zero).finite
  have : Finite (AdjoinRoot β) := finite_adjoinRoot hβ.1.ne_zero
  obtain ⟨w, hw, hw0, rfl⟩ := eq_Uw_of_hasType (isGenRoot_adjoinRoot hβ.1) hU hβ
  exact finrank_Uw (isGenRoot_adjoinRoot hβ.1) hw hw0

omit [Finite K] in
theorem hasType_unique (M : Matrix (Fin m) (Fin m) K) (U : Submodule K (Fin m → K))
    (hU : IsSimpleInvariant M U) {β β' : K[X]} (hβ : HasType M U β) (hβ' : HasType M U β') :
    β = β' :=
  hasType_unique_aux M hU.2.1 hβ hβ'

theorem lem_simple_sq_dvd (M : Matrix (Fin m) (Fin m) K) (hM : M.IsSymm)
    (U : Submodule K (Fin m → K)) (hU : IsSimpleInvariant M U) {β : K[X]}
    (hβ : HasType M U β) (hiso : IsTotallyIsotropic U) : β ^ 2 ∣ M.charpoly := by
  have : Fact (Irreducible β) := ⟨hβ.2.1⟩
  have : Module.Finite K (AdjoinRoot β) := (AdjoinRoot.powerBasis hβ.1.ne_zero).finite
  have : Finite (AdjoinRoot β) := finite_adjoinRoot hβ.1.ne_zero
  by_contra hnd
  exact lem_simple_d_last (isGenRoot_adjoinRoot hβ.1) hM hnd hU hβ hiso

end TypesFinite

end DGS
