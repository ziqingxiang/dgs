module

public import DGS.S12_Deg2.SEd
public import DGS.S12_Deg2.TraceRes
public import DGS.S04_Reduction.Reduction

@[expose] public section

open Finset Matrix Polynomial Module
open scoped Real

namespace DGS

section Generic

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {m : ℕ}

variable (F) in
noncomputable def trSub (K : Submodule L (Fin m → L)) : Submodule F (Fin m → F) :=
  LinearMap.range ((trVec F).comp ((K.restrictScalars F).subtype))

theorem trVec_mem_trSub {K : Submodule L (Fin m → L)} {v : Fin m → L} (hv : v ∈ K) :
    trVec F v ∈ trSub F K :=
  ⟨⟨v, hv⟩, rfl⟩

theorem exists_of_mem_trSub {K : Submodule L (Fin m → L)} {u : Fin m → F} (hu : u ∈ trSub F K) :
    ∃ v ∈ K, trVec F v = u := by
  obtain ⟨⟨v, hv⟩, rfl⟩ := hu
  exact ⟨v, hv, rfl⟩

theorem perp_iff_perp_trSub [FiniteDimensional F L] [Algebra.IsSeparable F L] (K : Submodule L (Fin m → L))
    (y : Fin m → F) : (∀ v ∈ K, liftVec F y ⬝ᵥ v = 0) ↔ ∀ u ∈ trSub F K, y ⬝ᵥ u = 0 := by
  constructor
  · intro hv u hu
    obtain ⟨v, hvK, rfl⟩ := exists_of_mem_trSub hu
    have h1 := dotProduct_trVec y v 1
    rw [one_smul, one_mul, hv v hvK, map_zero] at h1
    exact h1
  · intro hu v hvK
    refine (traceForm_nondegenerate F L).1 _ fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm, ← dotProduct_trVec]
    exact hu _ (trVec_mem_trSub (K.smul_mem c hvK))

variable {β : F[X]} {μ : L} {M : Matrix (Fin m) (Fin m) F}

theorem finrank_trSub [FiniteDimensional F L] [Algebra.IsSeparable F L] (h : IsGenRoot β μ)
    (K : Submodule L (Fin m → L)) (hK : K ≤ eigsp M μ) :
    finrank F (trSub F K) = finrank F L * finrank L K := by
  have hinj : Function.Injective ((trVec F).comp ((K.restrictScalars F).subtype)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hvK : (v : Fin m → L) ∈ eigsp M μ := hK v.2
    have h0 : trVec F (v : Fin m → L) = 0 := hv
    exact Subtype.ext ((trVec_eq_zero_iff h hvK).1 h0)
  rw [trSub, LinearMap.finrank_range_of_inj hinj, Module.finrank_mul_finrank F L K]
  rfl

theorem trSub_kills (h : IsGenRoot β μ) {K : Submodule L (Fin m → L)} (hK : K ≤ eigsp M μ) {u : Fin m → F}
    (hu : u ∈ trSub F K) : aeval M β *ᵥ u = 0 := by
  obtain ⟨v, hvK, rfl⟩ := exists_of_mem_trSub hu
  exact trVec_kills h (hK hvK)

end Generic

section Prob

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

theorem ker_shiftedMat_le_eigsp {L : Type*} [Field L] [Algebra (ZMod p) L] (μ : L) (ω : Pairs m → Bool) :
    LinearMap.ker (shiftedMat (F := L) 1 (-1) μ ω).mulVecLin ≤ eigsp (modP p (seidelOf ω)) μ := by
  intro w hw
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
  rw [mem_eigsp]
  have e : (modP p (seidelOf ω)).map (algebraMap (ZMod p) L) = (seidelOf ω).map (Int.castRingHom L) := by
    ext i j
    simp [modP]
  rw [e]
  unfold shiftedMat at hw
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hw
  exact hw

theorem prob_perp_eigsp_le {d : ℕ} {T : Matrix (Fin m) (Fin m) ℤ} (hT : GoodSEd d T) (hp23 : 23 ≤ p)
    (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) (hp4 : 3 ≤ d → (m : ℝ) ^ (0.4 : ℝ) ≤ p)
    {L : Type*} [Field L] [Finite L] [Algebra (ZMod p) L] {β : (ZMod p)[X]} {μ : L} (h : IsGenRoot β μ)
    (hβd : β.natDegree = d) (K : Submodule L (Fin m → L)) (hK : K ≤ eigsp (modP p T) μ) :
    prob (fun ξ : Fin m → Bool => ∀ v ∈ K, twoValued (1 : L) (-1) ξ ⬝ᵥ v = 0) ≤
      ((p : ℝ) ^ (d * finrank L K))⁻¹ + Real.exp (-2 * cSEd * m) := by
  have hp2 : p ≠ 2 := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hev : ∀ ξ : Fin m → Bool, (∀ v ∈ K, twoValued (1 : L) (-1) ξ ⬝ᵥ v = 0) ↔
      ∀ u ∈ trSub (ZMod p) K, twoValued (1 : ZMod p) (-1) ξ ⬝ᵥ u = 0 := by
    intro ξ
    rw [twoValued_eq_liftVec (p := p), ← sgnP_eq_twoValued]
    exact perp_iff_perp_trSub K (sgnP p ξ)
  have hdim : finrank (ZMod p) (trSub (ZMod p) K) = d * finrank L K := by
    rw [finrank_trSub h K hK, h.finrank_eq, hβd]
  rw [prob_congr hev]
  have hbd := prob_perp_le (trSub (ZMod p) K) (ε := Real.exp (-2 * cSEd * m)) (Real.exp_pos _).le
    (fun u hu hu0 => by
      have hker := trSub_kills h hK hu
      have h1 := hT p hp23 hpm hp4 β h.monic hβd u hu0 hker
      have h2 := lem_dilates hp2 u (one_ne_zero (α := ZMod p))
      simp only [one_mul] at h2
      refine h2.trans (Real.exp_le_exp.2 ?_)
      rw [div_le_iff₀ (by positivity)]
      nlinarith)
  rw [hdim] at hbd
  exact hbd

theorem abeta_le_of_goodSEd {d : ℕ} {T : Matrix (Fin m) (Fin m) ℤ} (hT : GoodSEd d T) (hp23 : 23 ≤ p)
    (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) (hp4 : 3 ≤ d → (m : ℝ) ^ (0.4 : ℝ) ≤ p)
    {β : (ZMod p)[X]} (hβm : β.Monic) (hβirr : Irreducible β) (hβd : β.natDegree = d) :
    abeta p T β ≤ ((p : ℝ) ^ d)⁻¹ + Real.exp (-2 * cSEd * m) := by
  have : Fact (Irreducible β) := ⟨hβirr⟩
  have : Module.Finite (ZMod p) (AdjoinRoot β) := (AdjoinRoot.powerBasis hβm.ne_zero).finite
  have : Finite (AdjoinRoot β) := finite_adjoinRoot hβm.ne_zero
  have h := isGenRoot_adjoinRoot hβm
  have hb0 : 0 ≤ ((p : ℝ) ^ d)⁻¹ + Real.exp (-2 * cSEd * m) := by positivity
  refine Real.sSup_le ?_ hb0
  rintro x ⟨U, hU, hβU, rfl⟩
  obtain ⟨w, hw, hw0, rfl⟩ := (lem_simple_a h (modP p T)).2.1 U hU hβU
  have hspan : (AdjoinRoot β ∙ w) ≤ eigsp (modP p T) (AdjoinRoot.root β) :=
    (Submodule.span_singleton_le_iff_mem _ _).2 hw
  have hbd := prob_perp_eigsp_le hT hp23 hpm hp4 h hβd _ hspan
  rw [finrank_span_singleton hw0, mul_one] at hbd
  refine le_trans ?_ hbd
  unfold probPerp
  rw [lem_simple_c_prob (fun ξ : Fin m → Bool => modPVec p (signVec ξ)) w]
  refine prob_mono fun ξ hξ v hv => ?_
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [dotProduct_smul, smul_eq_mul]
  have e : liftVec (ZMod p) (modPVec p (signVec ξ)) = twoValued (1 : AdjoinRoot β) (-1) ξ := by
    rw [modPVec_signVec, ← sgnP_eq_twoValued, twoValued_eq_liftVec (p := p)]
  rw [← e, hξ, mul_zero]

end Prob

end DGS
