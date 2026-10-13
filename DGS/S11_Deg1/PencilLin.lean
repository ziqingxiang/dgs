module

public import DGS.S11_Deg1.RandRank
public import DGS.S03_Prelim.Border
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

open Finset Matrix Module

namespace DGS

variable {F : Type*} [Field F]

section General

variable {V W : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup W]
  [Module F W] [FiniteDimensional F W]

omit [FiniteDimensional F W] in
theorem finrank_map_add_finrank_inf_ker (f : V →ₗ[F] W) (N : Submodule F V) :
    finrank F (N.map f) + finrank F ↥(N ⊓ LinearMap.ker f) = finrank F N := by
  set g : N →ₗ[F] W := f ∘ₗ N.subtype with hg
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 : LinearMap.range g = N.map f := by
    rw [hg, LinearMap.range_comp, Submodule.range_subtype]
  have h3 : finrank F (LinearMap.ker g) = finrank F ↥(N ⊓ LinearMap.ker f) := by
    have hk : LinearMap.ker g = (LinearMap.ker f).comap N.subtype := by
      rw [hg, LinearMap.ker_comp]
    rw [hk, ← Submodule.map_comap_subtype N (LinearMap.ker f)]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective N.subtype N.injective_subtype _)
  rw [← h2, ← h3]
  exact h1

theorem finrank_sup_eq_add_map_mkQ (L N : Submodule F V) :
    finrank F ↥(L ⊔ N) = finrank F L + finrank F (N.map L.mkQ) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq L N
  have h2 := finrank_map_add_finrank_inf_ker L.mkQ N
  rw [Submodule.ker_mkQ, inf_comm] at h2
  omega

end General

section Kmat

variable {m nR nU : ℕ}

def Kmat (QA PA : Matrix (Fin m) (Fin m) F) (eRc : Fin nR → Fin m) (eU : Fin nU → Fin m) :
    Matrix (Fin m) (Fin nR ⊕ Fin nU) F :=
  Matrix.of fun i => Sum.elim (fun a => QA i (eRc a)) (fun b => PA i (eU b))

def diagSet (X : Finset (Fin m)) : Matrix (Fin m) (Fin m) F :=
  Matrix.diagonal fun j => if j ∈ X then 1 else 0

theorem diagSet_mulVec (X : Finset (Fin m)) (v : Fin m → F) (j : Fin m) :
    (diagSet X *ᵥ v) j = if j ∈ X then v j else 0 := by
  rw [diagSet, mulVec_diagonal]
  split_ifs <;> simp

theorem sum_comp_eq_sum_ite {n : ℕ} (e : Fin n → Fin m) (he : Function.Injective e) (P : Fin m → Prop)
    [DecidablePred P] (hP : ∀ j, P j ↔ j ∈ Set.range e) (f : Fin m → F) :
    ∑ a, f (e a) = ∑ j, if P j then f j else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_image (fun a _ b _ h => he h)]
  congr 1
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, hP]
  rfl

theorem finrank_ker_funLeft {n : ℕ} (e : Fin n → Fin m) (he : Function.Injective e) :
    finrank F (LinearMap.ker (LinearMap.funLeft F F e)) + n = m := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.funLeft F F e)
  have h2 : LinearMap.range (LinearMap.funLeft F F e) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro w
    refine ⟨Function.extend e w 0, ?_⟩
    funext a
    simp only [LinearMap.funLeft_apply]
    exact he.extend_apply w 0 a
  rw [h2, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h1
  omega

theorem rank_Kmat_le (QA PA C : Matrix (Fin m) (Fin m) F) (hQC : QA * C = PA) (R U : Finset (Fin m))
    (eRc : Fin nR → Fin m) (heRc : Function.Injective eRc) (hRc : ∀ j, j ∉ R ↔ j ∈ Set.range eRc)
    (eU : Fin nU → Fin m) (heU : Function.Injective eU) (hU : ∀ j, j ∈ U ↔ j ∈ Set.range eU) :
    (Kmat QA PA eRc eU).rank ≤ (diagSet R * C * diagSet U).rank + nR := by
  classical
  set K := Kmat QA PA eRc eU with hK
  set M := diagSet R * C * diagSet U with hM
  let g : (Fin m → F) →ₗ[F] (Fin nR ⊕ Fin nU → F) :=
    { toFun := fun v => Sum.elim (fun a => (C *ᵥ (diagSet U *ᵥ v)) (eRc a)) (fun b => -(v (eU b)))
      map_add' := fun v w => by
        funext s
        cases s with
        | inl a => simp [mulVec_add]
        | inr b => simp [mulVec_add]; ring
      map_smul' := fun c v => by
        funext s
        cases s <;> simp [mulVec_smul] }
  have hg_ker : ∀ v ∈ LinearMap.ker M.mulVecLin, g v ∈ LinearMap.ker K.mulVecLin := by
    intro v hv
    rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
    set y := C *ᵥ (diagSet U *ᵥ v) with hy
    have hyR : ∀ j ∈ R, y j = 0 := by
      intro j hj
      have h1 : M *ᵥ v = diagSet R *ᵥ y := by rw [hM, ← mulVec_mulVec, ← mulVec_mulVec]
      have h2 := congrFun (h1.symm.trans hv) j
      rwa [diagSet_mulVec, ite_eq_left hj] at h2
    funext i
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, hK, Kmat, Matrix.of_apply, Sum.elim_inl,
      Sum.elim_inr, Pi.zero_apply]
    have e1 : ∑ a, QA i (eRc a) * (g v) (Sum.inl a) = (QA *ᵥ y) i := by
      simp only [g, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl]
      rw [sum_comp_eq_sum_ite eRc heRc (fun j => j ∉ R) hRc (fun j => QA i j * y j), mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ R
      · rw [ite_eq_right (not_not.2 hj), hyR j hj, mul_zero]
      · rw [ite_eq_left hj]
    have e2 : ∑ b, PA i (eU b) * (g v) (Sum.inr b) = -(PA *ᵥ (diagSet U *ᵥ v)) i := by
      simp only [g, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr]
      rw [show (fun b => PA i (eU b) * -v (eU b)) = fun b => -(PA i (eU b) * v (eU b)) by
        funext b; ring, Finset.sum_neg_distrib,
        sum_comp_eq_sum_ite eU heU (fun j => j ∈ U) hU (fun j => PA i j * v j), mulVec, dotProduct]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [diagSet_mulVec]
      split_ifs <;> simp
    rw [e1, e2, hy, mulVec_mulVec, hQC]
    ring
  set g' : LinearMap.ker M.mulVecLin →ₗ[F] (Fin nR ⊕ Fin nU → F) := g ∘ₗ (LinearMap.ker M.mulVecLin).subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker g'
  have h2 : finrank F (LinearMap.range g') ≤ finrank F (LinearMap.ker K.mulVecLin) := by
    apply Submodule.finrank_mono
    rintro _ ⟨v, rfl⟩
    exact hg_ker v.1 v.2
  have h3 : finrank F (LinearMap.ker g') ≤ finrank F (LinearMap.ker (LinearMap.funLeft F F eU)) := by
    let ι : LinearMap.ker g' →ₗ[F] (Fin m → F) :=
      (LinearMap.ker M.mulVecLin).subtype ∘ₗ (LinearMap.ker g').subtype
    have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
    rw [← LinearMap.finrank_range_of_inj hι]
    apply Submodule.finrank_mono
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    have hv : g' v = 0 := v.2
    funext b
    have := congrFun hv (Sum.inr b)
    simp only [g', g, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr, Pi.zero_apply, neg_eq_zero] at this
    simpa [ι] using this
  have h4 := finrank_ker_funLeft (F := F) eU heU
  have h5 := LinearMap.finrank_range_add_finrank_ker K.mulVecLin
  have h6 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h5
  rw [Module.finrank_fin_fun] at h6
  have h7 : K.rank = finrank F (LinearMap.range K.mulVecLin) := rfl
  have h8 : M.rank = finrank F (LinearMap.range M.mulVecLin) := rfl
  omega

theorem rank_ge_rows {n : Type*} [Fintype n] {k : ℕ} (K : Matrix (Fin m) n F) (eU : Fin nU → Fin m)
    (e1 : Fin k → Fin m) :
    finrank F (Submodule.span F (Set.range fun b => K (eU b))) +
      finrank F (Submodule.span F (Set.range fun a =>
        (Submodule.span F (Set.range fun b => K (eU b))).mkQ (K (e1 a)))) ≤ K.rank := by
  set L0 := Submodule.span F (Set.range fun b => K (eU b)) with hL0
  set L1 := Submodule.span F (Set.range fun a => K (e1 a)) with hL1
  have h1 := finrank_sup_eq_add_map_mkQ L0 L1
  have h2 : L1.map L0.mkQ = Submodule.span F (Set.range fun a => L0.mkQ (K (e1 a))) := by
    rw [hL1, Submodule.map_span, ← Set.range_comp]
    rfl
  have h3 : L0 ⊔ L1 ≤ Submodule.span F (Set.range K) := by
    refine sup_le (Submodule.span_mono ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨b, rfl⟩
      exact ⟨eU b, rfl⟩
    · rintro _ ⟨a, rfl⟩
      exact ⟨e1 a, rfl⟩
  rw [Matrix.rank_eq_finrank_span_row]
  rw [← h2, ← h1]
  exact Submodule.finrank_mono h3

def PUmat (PA : Matrix (Fin m) (Fin m) F) (eU : Fin nU → Fin m) : Matrix (Fin nU) (Fin nU) F :=
  Matrix.of fun b b' => PA (eU b) (eU b')

def projU : (Fin nR ⊕ Fin nU → F) →ₗ[F] (Fin nU → F) := LinearMap.funLeft F F Sum.inr

theorem projU_Kmat (QA PA : Matrix (Fin m) (Fin m) F) (eRc : Fin nR → Fin m) (eU : Fin nU → Fin m)
    (i : Fin m) : projU (Kmat QA PA eRc eU i) = fun b => PA i (eU b) := by
  funext b
  rfl

theorem nU_le_finrank_L0 (QA PA : Matrix (Fin m) (Fin m) F) (eRc : Fin nR → Fin m) (eU : Fin nU → Fin m) :
    nU ≤ finrank F ((Submodule.span F (Set.range fun b => Kmat QA PA eRc eU (eU b))).map projU) +
      corank (PUmat PA eU) := by
  have h1 : (Submodule.span F (Set.range fun b => Kmat QA PA eRc eU (eU b))).map projU =
      Submodule.span F (Set.range (PUmat PA eU)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have h2 := LinearMap.finrank_range_add_finrank_ker (PUmat PA eU).mulVecLin
  rw [Module.finrank_fin_fun] at h2
  have h3 : (PUmat PA eU).rank = finrank F (Submodule.span F (Set.range (PUmat PA eU))) :=
    Matrix.rank_eq_finrank_span_row _
  have h4 : (PUmat PA eU).rank = finrank F (LinearMap.range (PUmat PA eU).mulVecLin) := rfl
  rw [h1, ← h3]
  unfold corank
  omega

theorem finrank_range_le_Psi {k : ℕ} (L0 : Submodule F (Fin nR ⊕ Fin nU → F))
    (Φ : (Fin k → F) →ₗ[F] (Fin nR ⊕ Fin nU → F)) (hΦ : ∀ v, projU (Φ v) = 0) {r : ℕ}
    (hL0 : finrank F L0 ≤ nU) (hL0U : nU ≤ finrank F (L0.map projU) + r) :
    finrank F (LinearMap.range Φ) ≤ finrank F (LinearMap.range (L0.mkQ ∘ₗ Φ)) + r := by
  have h1 := finrank_map_add_finrank_inf_ker L0.mkQ (LinearMap.range Φ)
  rw [Submodule.ker_mkQ] at h1
  have h2 : LinearMap.range (L0.mkQ ∘ₗ Φ) = (LinearMap.range Φ).map L0.mkQ := LinearMap.range_comp _ _
  have h3 : LinearMap.range Φ ⊓ L0 ≤ L0 ⊓ LinearMap.ker projU := by
    rw [inf_comm]
    refine inf_le_inf_left _ ?_
    rintro _ ⟨v, rfl⟩
    exact hΦ v
  have h4 := Submodule.finrank_mono h3
  have h5 := finrank_map_add_finrank_inf_ker projU L0
  rw [h2]
  omega

theorem setFinrank_le_finrank_range {k : ℕ} (W : Fin k → Fin nR → F) :
    (Set.range W).finrank F ≤ finrank F (LinearMap.range
      (Fintype.linearCombination F (fun c => (Sum.elim (W c) 0 : Fin nR ⊕ Fin nU → F)))) := by
  rw [Fintype.range_linearCombination]
  let ι : (Fin nR → F) →ₗ[F] (Fin nR ⊕ Fin nU → F) :=
    { toFun := fun w => Sum.elim w 0
      map_add' := fun w w' => by funext s; cases s <;> simp
      map_smul' := fun c w => by funext s; cases s <;> simp }
  have hι : Function.Injective ι := by
    intro w w' h
    funext a
    exact congrFun h (Sum.inl a)
  have h2 : Submodule.span F (Set.range fun c => (Sum.elim (W c) 0 : Fin nR ⊕ Fin nU → F)) =
      (Submodule.span F (Set.range W)).map ι := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [h2, ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective ι hι _)]
  rfl

theorem rank_bound_generic {k : ℕ} {X : Type*} [Nonempty X] (K' : X → Matrix (Fin m) (Fin nR ⊕ Fin nU) F)
    (eU : Fin nU → Fin m) (e1 : Fin k → Fin m) (L0 : Submodule F (Fin nR ⊕ Fin nU → F))
    (hL0 : ∀ x, Submodule.span F (Set.range fun b => K' x (eU b)) = L0)
    (PU : Matrix (Fin nU) (Fin nU) F) (hPU : ∀ x b, projU (K' x (eU b)) = PU b)
    (Φ : (Fin k → F) →ₗ[F] (Fin nR ⊕ Fin nU → F)) (hΦ0 : ∀ v, projU (Φ v) = 0)
    (sg : X → Fin k → Fin k → F) (c : Fin k → (Fin nR ⊕ Fin nU → F) ⧸ L0)
    (hrow : ∀ x a, L0.mkQ (K' x (e1 a)) = L0.mkQ (Φ (sg x a)) + c a)
    {t : ℕ} (hrP : corank PU ≤ t) (hW : k ≤ finrank F (LinearMap.range Φ) + t) :
    ∃ ρ, ρ ≤ k ∧ ρ ≤ finrank F (LinearMap.range (L0.mkQ ∘ₗ Φ)) ∧
      ∀ x, (K' x).rank + 4 * t < nU + k →
        t + 1 ≤ ρ ∧ (Set.range fun a => (L0.mkQ ∘ₗ Φ) (sg x a) + c a).finrank F ≤ ρ - t - 1 := by
  obtain ⟨x0⟩ := ‹Nonempty X›
  have hL0card : finrank F L0 ≤ nU := by
    have := finrank_range_le_card (R := F) (fun b => K' x0 (eU b))
    rw [Fintype.card_fin, Set.finrank, hL0 x0] at this
    exact this
  have hL0U : nU ≤ finrank F (L0.map projU) + corank PU := by
    have h1 : L0.map projU = Submodule.span F (Set.range PU) := by
      rw [← hL0 x0, Submodule.map_span, ← Set.range_comp]
      congr 2
      funext b
      exact hPU x0 b
    have h2 := LinearMap.finrank_range_add_finrank_ker PU.mulVecLin
    rw [Module.finrank_fin_fun] at h2
    have h3 : PU.rank = finrank F (Submodule.span F (Set.range PU)) := Matrix.rank_eq_finrank_span_row _
    have h4 : PU.rank = finrank F (LinearMap.range PU.mulVecLin) := rfl
    rw [h1, ← h3]
    unfold corank
    omega
  have hPsi := finrank_range_le_Psi L0 Φ hΦ0 hL0card hL0U
  have hρk : finrank F (LinearMap.range (L0.mkQ ∘ₗ Φ)) ≤ k := by
    have := LinearMap.finrank_range_le (L0.mkQ ∘ₗ Φ)
    rwa [Module.finrank_fin_fun] at this
  refine ⟨finrank F (LinearMap.range (L0.mkQ ∘ₗ Φ)), hρk, le_rfl, fun x hx => ?_⟩
  have h1 := rank_ge_rows (K' x) eU e1
  rw [hL0 x] at h1
  have e : (fun a => L0.mkQ (K' x (e1 a))) = fun a => (L0.mkQ ∘ₗ Φ) (sg x a) + c a := by
    funext a
    rw [hrow x a]
    rfl
  rw [e] at h1
  have h2 : finrank F (L0.map projU) ≤ finrank F L0 := Submodule.finrank_map_le _ _
  change finrank F L0 + (Set.range fun a => (L0.mkQ ∘ₗ Φ) (sg x a) + c a).finrank F ≤ (K' x).rank at h1
  omega

theorem prob_rank_small_generic {k : ℕ} (hF : (1 : F) ≠ -1)
    (K' : (Fin k × Fin k → Bool) → Matrix (Fin m) (Fin nR ⊕ Fin nU) F)
    (eU : Fin nU → Fin m) (e1 : Fin k → Fin m) (L0 : Submodule F (Fin nR ⊕ Fin nU → F))
    (hL0 : ∀ x, Submodule.span F (Set.range fun b => K' x (eU b)) = L0)
    (PU : Matrix (Fin nU) (Fin nU) F) (hPU : ∀ x b, projU (K' x (eU b)) = PU b)
    (W : Fin k → Fin nR → F) (h : Fin k → (Fin nR ⊕ Fin nU → F))
    (hrow : ∀ x a, K' x (e1 a) = Fintype.linearCombination F
      (fun c => (Sum.elim (W c) 0 : Fin nR ⊕ Fin nU → F)) (twoValued (1 : F) (-1) fun c => x (a, c)) + h a)
    {t : ℕ} (hrP : corank PU ≤ t) (hW : k ≤ (Set.range W).finrank F + t) :
    prob (fun x => (K' x).rank + 4 * t < nU + k) ≤ 2 ^ k * ((1 : ℝ) / 2) ^ ((t + 1) * (t + 1)) := by
  set Φ := Fintype.linearCombination F (fun c => (Sum.elim (W c) 0 : Fin nR ⊕ Fin nU → F)) with hΦdef
  have hΦ0 : ∀ v, projU (Φ v) = 0 := by
    intro v
    funext b
    simp [projU, hΦdef, Fintype.linearCombination_apply]
  have hW' : k ≤ finrank F (LinearMap.range Φ) + t := by
    have h1 : (Set.range W).finrank F ≤ finrank F (LinearMap.range Φ) :=
      setFinrank_le_finrank_range (nU := nU) W
    omega
  obtain ⟨ρ, hρk, hρΨ, hρx⟩ := rank_bound_generic K' eU e1 L0 hL0 PU hPU Φ hΦ0
    (fun x a => twoValued (1 : F) (-1) fun c => x (a, c)) (fun a => L0.mkQ (h a))
    (fun x a => by rw [hrow x a, map_add]) hrP hW'
  by_cases hρt : t + 1 ≤ ρ
  · have hbound := prob_setFinrank_le' (k := k) (r := ρ - t - 1) hF (L0.mkQ ∘ₗ Φ)
      (fun a => L0.mkQ (h a)) hρΨ (by omega)
    have hcurry : prob (fun x : Fin k × Fin k → Bool => (K' x).rank + 4 * t < nU + k) ≤
        prob (fun x : Fin k → Fin k → Bool =>
          (Set.range fun a => (L0.mkQ ∘ₗ Φ) (twoValued (1 : F) (-1) (x a)) + L0.mkQ (h a)).finrank F ≤
            ρ - t - 1) := by
      rw [← prob_curry_eq]
      exact prob_mono fun x hx => (hρx x hx).2
    refine hcurry.trans (hbound.trans ?_)
    have h3 : t + 1 ≤ k - (ρ - t - 1) := by omega
    have h4 : (2 : ℝ) ^ (ρ - t - 1) / 2 ^ ρ = ((1 : ℝ) / 2) ^ (t + 1) := by
      rw [_root_.one_div_pow, div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
      congr 1
      omega
    rw [h4, ← pow_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.mul_le_mul le_rfl h3)
  · rw [prob_congr (Q := fun _ => False) fun x => ⟨fun hx => hρt (hρx x hx).1, False.elim⟩, prob_false]
    positivity

end Kmat

end DGS
