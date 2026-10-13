module

public import DGS.S03_Prelim.Apriori
public import DGS.S03_Prelim.SimpleSubmodules

@[expose] public section

open Matrix Polynomial Module

namespace DGS

section KernelDim

variable {K : Type*} [Field K] {m : ℕ}

theorem finrank_ker_mul_le (A B : Matrix (Fin m) (Fin m) K) :
    finrank K (LinearMap.ker (A * B).mulVecLin) ≤
      finrank K (LinearMap.ker A.mulVecLin) + finrank K (LinearMap.ker B.mulVecLin) := by
  have hmaps : ∀ x ∈ LinearMap.ker (A * B).mulVecLin, B.mulVecLin x ∈ LinearMap.ker A.mulVecLin := by
    intro x hx
    rw [mem_ker_mulVecLin] at hx ⊢
    rw [mulVecLin_apply, mulVec_mulVec, hx]
  let f := B.mulVecLin.restrict hmaps
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : finrank K (LinearMap.range f) ≤ finrank K (LinearMap.ker A.mulVecLin) :=
    Submodule.finrank_le _
  let ι : LinearMap.ker f →ₗ[K] (Fin m → K) :=
    (LinearMap.ker (A * B).mulVecLin).subtype ∘ₗ (LinearMap.ker f).subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hrange : LinearMap.range ι ≤ LinearMap.ker B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    have hx : f x = 0 := x.2
    have hx' : B.mulVecLin (x : LinearMap.ker (A * B).mulVecLin) = 0 := congrArg Subtype.val hx
    exact hx'
  have h3 : finrank K (LinearMap.ker f) ≤ finrank K (LinearMap.ker B.mulVecLin) := by
    rw [← LinearMap.finrank_range_of_inj hι]
    exact Submodule.finrank_mono hrange
  omega

theorem finrank_ker_one : finrank K (LinearMap.ker (1 : Matrix (Fin m) (Fin m) K).mulVecLin) = 0 := by
  rw [mulVecLin_one, LinearMap.ker_id, finrank_bot]

theorem finrank_ker_aeval_prod_le (M : Matrix (Fin m) (Fin m) K) (s : Multiset K[X]) :
    finrank K (LinearMap.ker (aeval M s.prod).mulVecLin) ≤
      (s.map fun β => finrank K (LinearMap.ker (aeval M β).mulVecLin)).sum := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.prod_zero, map_one, finrank_ker_one]
    exact Nat.zero_le _
  | cons β s ih =>
    rw [Multiset.prod_cons, map_mul, Multiset.map_cons, Multiset.sum_cons]
    exact (finrank_ker_mul_le _ _).trans (by omega)

theorem finrank_ker_aeval_mul_unit (M : Matrix (Fin m) (Fin m) K) (f : K[X]) (u : (K[X])ˣ) :
    finrank K (LinearMap.ker (aeval M (f * (u : K[X]))).mulVecLin) ≤
      finrank K (LinearMap.ker (aeval M f).mulVecLin) := by
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have hker : finrank K (LinearMap.ker (aeval M (u : K[X])).mulVecLin) = 0 := by
    rw [← hcu, aeval_C, Algebra.algebraMap_eq_smul_one, Submodule.finrank_eq_zero,
      Submodule.eq_bot_iff]
    intro x hx
    rw [mem_ker_mulVecLin, smul_mulVec, one_mulVec] at hx
    exact (smul_eq_zero.1 hx).resolve_left hc.ne_zero
  rw [map_mul]
  have := finrank_ker_mul_le (aeval M f) (aeval M (u : K[X]))
  omega

theorem finrank_ker_aeval_le_of_irreducible [DecidableEq K] (M : Matrix (Fin m) (Fin m) K) {d r : ℕ}
    (h : ∀ β : K[X], β.Monic → Irreducible β → β.natDegree < d →
      finrank K (LinearMap.ker (aeval M β).mulVecLin) ≤ β.natDegree * (r - 1))
    {α : K[X]} (hα : α ≠ 0) (hαd : α.natDegree < d) :
    finrank K (LinearMap.ker (aeval M α).mulVecLin) ≤ (d - 1) * (r - 1) := by
  set s := UniqueFactorizationMonoid.normalizedFactors α with hs
  have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hα
  obtain ⟨u, hu⟩ := hassoc
  have hmonic : ∀ β ∈ s, β.Monic := fun β hβ => by
    have h1 := UniqueFactorizationMonoid.normalize_normalized_factor β hβ
    have h0 : β ≠ 0 := (UniqueFactorizationMonoid.irreducible_of_normalized_factor β hβ).ne_zero
    rw [← h1]
    exact Polynomial.monic_normalize h0
  have hdeg : (s.map natDegree).sum = α.natDegree := by
    rw [← natDegree_multiset_prod_of_monic s hmonic, ← hu]
    exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ⟨u, rfl⟩)
  have hβd : ∀ β ∈ s, β.natDegree < d := fun β hβ => by
    have := natDegree_le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hβ) hα
    omega
  calc finrank K (LinearMap.ker (aeval M α).mulVecLin)
      ≤ finrank K (LinearMap.ker (aeval M s.prod).mulVecLin) := by
        rw [← hu]
        exact finrank_ker_aeval_mul_unit M _ u
    _ ≤ (s.map fun β => finrank K (LinearMap.ker (aeval M β).mulVecLin)).sum :=
        finrank_ker_aeval_prod_le M s
    _ ≤ (s.map fun β => β.natDegree * (r - 1)).sum :=
        Multiset.sum_map_le_sum_map _ _ fun β hβ =>
          h β (hmonic β hβ) (UniqueFactorizationMonoid.irreducible_of_normalized_factor β hβ)
            (hβd β hβ)
    _ = α.natDegree * (r - 1) := by rw [Multiset.sum_map_mul_right, hdeg]
    _ ≤ (d - 1) * (r - 1) := Nat.mul_le_mul_right _ (by omega)

end KernelDim

section KernelTrace

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] {m : ℕ}

theorem finrank_ker_aeval_eq {β : K[X]} {μ : L} (h : IsGenRoot β μ) (M : Matrix (Fin m) (Fin m) K) :
    finrank K (LinearMap.ker (aeval M β).mulVecLin) = β.natDegree * finrank L (eigsp M μ) := by
  let φ : eigsp M μ →ₗ[K] (Fin m → K) :=
    { toFun := fun w => trVec K (w : Fin m → L)
      map_add' := fun w w' => by simp
      map_smul' := fun c w => by
        rw [RingHom.id_apply, ← map_smul]
        rfl }
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext ((trVec_eq_zero_iff h w.2).1 hw)
  have hrange : LinearMap.range φ = LinearMap.ker (aeval M β).mulVecLin := by
    ext v
    rw [LinearMap.mem_range, mem_ker_mulVecLin]
    constructor
    · rintro ⟨w, rfl⟩
      exact trVec_kills h w.2
    · intro hv
      obtain ⟨w, hw, rfl⟩ := exists_trVec_eq h hv
      exact ⟨⟨w, hw⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hφ, ← h.finrank_eq,
    Module.finrank_mul_finrank K L (eigsp M μ)]

end KernelTrace

section KernelPolyProb

variable {a b : ℤ} {p : ℕ} [Fact p.Prime] {m : ℕ}

open Classical in
noncomputable def rootGeomMult (a b : ℤ) (f : (ZMod p)[X]) (ω : Pairs m → Bool) : ℕ :=
  if hf : Irreducible f then
    haveI : Fact (Irreducible f) := ⟨hf⟩
    geomMult a b (AdjoinRoot.root f) ω
  else 0

theorem rootGeomMult_eq (f : (ZMod p)[X]) [hf : Fact (Irreducible f)] (ω : Pairs m → Bool) :
    rootGeomMult a b f ω = geomMult a b (AdjoinRoot.root f) ω := by
  unfold rootGeomMult
  rw [dite_eq_left hf.out]

theorem castMatrix_eq (f : (ZMod p)[X]) [Fact (Irreducible f)] (ω : Pairs m → Bool) :
    (modP p (symOf a b ω)).map (algebraMap (ZMod p) (AdjoinRoot f)) =
      (symOf a b ω).map (Int.castRingHom (AdjoinRoot f)) := by
  refine Matrix.ext fun i j => ?_
  simp only [modP, Matrix.map_apply, eq_intCast, map_intCast]

theorem eigenspace_toLin'_eq {L : Type*} [Field L] (N : Matrix (Fin m) (Fin m) L) (μ : L) :
    Module.End.eigenspace (toLin' N) μ = LinearMap.ker (N - μ • 1).mulVecLin := by
  ext x
  rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, mulVecLin_apply, toLin'_apply, sub_mulVec,
    smul_mulVec, one_mulVec, sub_eq_zero]

theorem finrank_ker_eq_rootGeomMult {β : (ZMod p)[X]} (hβ : β.Monic) (hirr : Irreducible β)
    (ω : Pairs m → Bool) :
    finrank (ZMod p) (LinearMap.ker (aeval (modP p (symOf a b ω)) β).mulVecLin) =
      β.natDegree * rootGeomMult a b β ω := by
  have : Fact (Irreducible β) := ⟨hirr⟩
  have : Module.Finite (ZMod p) (AdjoinRoot β) := (AdjoinRoot.powerBasis hβ.ne_zero).finite
  have : Finite (AdjoinRoot β) := finite_adjoinRoot hβ.ne_zero
  rw [finrank_ker_aeval_eq (isGenRoot_adjoinRoot hβ), rootGeomMult_eq]
  congr 1
  unfold geomMult corank shiftedMat eigsp
  rw [← castMatrix_eq, eigenspace_toLin'_eq]

theorem cast_ne_of_not_dvd (hab : ¬ (p : ℤ) ∣ a - b) (f : (ZMod p)[X]) [Fact (Irreducible f)] :
    ((a : AdjoinRoot f)) ≠ (b : AdjoinRoot f) := by
  intro h
  apply hab
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h1 : algebraMap (ZMod p) (AdjoinRoot f) ((a - b : ℤ) : ZMod p) = 0 := by
    rw [map_intCast, Int.cast_sub, h, sub_self]
  exact (map_eq_zero_iff _ (algebraMap (ZMod p) (AdjoinRoot f)).injective).1 h1

theorem prob_rootGeomMult_le (hab : ¬ (p : ℤ) ∣ a - b) {r : ℕ} (hr : 1 ≤ r) (f : (ZMod p)[X])
    (hfm : f.Monic) :
    prob (fun ω : Pairs m → Bool => r ≤ rootGeomMult a b f ω) ≤
      30 * (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4)) := by
  by_cases hf : Irreducible f
  · have : Fact (Irreducible f) := ⟨hf⟩
    have : Module.Finite (ZMod p) (AdjoinRoot f) := (AdjoinRoot.powerBasis hfm.ne_zero).finite
    simp only [rootGeomMult_eq]
    exact lem_apriori_tail (cast_ne_of_not_dvd hab f) _ m r
  · have h0 : ∀ ω : Pairs m → Bool, ¬ r ≤ rootGeomMult a b f ω := fun ω => by
      unfold rootGeomMult
      rw [dite_eq_right hf]
      omega
    rw [prob_congr (fun ω => iff_false_intro (h0 ω)), prob_false]
    positivity

noncomputable def monicOfDegree (p : ℕ) [Fact p.Prime] (j : ℕ) : Finset (ZMod p)[X] :=
  Finset.univ.image fun v : Fin j → ZMod p => X ^ j + ∑ i : Fin j, C (v i) * X ^ (i : ℕ)

theorem mem_monicOfDegree {f : (ZMod p)[X]} (hf : f.Monic) : f ∈ monicOfDegree p f.natDegree := by
  unfold monicOfDegree
  rw [Finset.mem_image]
  refine ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
  conv_rhs => rw [hf.as_sum]
  rw [Finset.sum_range (fun i => C (f.coeff i) * X ^ i)]

theorem card_monicOfDegree_le (j : ℕ) : (monicOfDegree p j).card ≤ p ^ j := by
  classical
  unfold monicOfDegree
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

omit [Fact (Nat.Prime p)] in
theorem sum_pow_le (hp : 2 ≤ p) (d : ℕ) : ∑ j ∈ Finset.Ico 1 d, p ^ j ≤ 2 * p ^ (d - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega), Nat.add_sub_cancel]
      have h1 : 2 * p ^ (d - 1) ≤ p ^ d := by
        calc 2 * p ^ (d - 1) ≤ p * p ^ (d - 1) := Nat.mul_le_mul_right _ hp
          _ = p ^ d := by rw [← pow_succ', Nat.sub_add_cancel hd]
      omega

theorem cor_kernelpoly (hab : ¬ (p : ℤ) ∣ a - b) (d r : ℕ) (hr : 1 ≤ r) (m : ℕ) :
    prob (fun ω : Pairs m → Bool => ¬ ∀ α : (ZMod p)[X], α ≠ 0 → α.natDegree < d →
      finrank (ZMod p) (LinearMap.ker (aeval (modP p (symOf a b ω)) α).mulVecLin) ≤
        (d - 1) * (r - 1)) ≤ 60 * (p : ℝ) ^ (d - 1) * (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4)) := by
  classical
  set S : Finset (ZMod p)[X] := (Finset.Ico 1 d).biUnion fun j => monicOfDegree p j with hS
  have hbad : ∀ ω : Pairs m → Bool, (¬ ∀ α : (ZMod p)[X], α ≠ 0 → α.natDegree < d →
      finrank (ZMod p) (LinearMap.ker (aeval (modP p (symOf a b ω)) α).mulVecLin) ≤
        (d - 1) * (r - 1)) → ∃ β ∈ S, r ≤ rootGeomMult a b β ω := by
    intro ω hω
    by_contra hno
    push Not at hno
    apply hω
    intro α hα hαd
    refine finrank_ker_aeval_le_of_irreducible _ (fun β hβm hβi hβd => ?_) hα hαd
    rw [finrank_ker_eq_rootGeomMult hβm hβi]
    have hβS : β ∈ S := by
      rw [hS, Finset.mem_biUnion]
      exact ⟨β.natDegree, Finset.mem_Ico.2 ⟨hβi.natDegree_pos, hβd⟩, mem_monicOfDegree hβm⟩
    have := hno β hβS
    exact Nat.mul_le_mul_left _ (by omega)
  have hmonic : ∀ β ∈ S, β.Monic := by
    intro β hβ
    rw [hS, Finset.mem_biUnion] at hβ
    obtain ⟨j, -, hβj⟩ := hβ
    unfold monicOfDegree at hβj
    rw [Finset.mem_image] at hβj
    obtain ⟨v, -, rfl⟩ := hβj
    exact monic_X_pow_add (degree_sum_fin_lt v)
  have hcard : (S.card : ℝ) ≤ 2 * (p : ℝ) ^ (d - 1) := by
    have h1 : S.card ≤ ∑ j ∈ Finset.Ico 1 d, p ^ j :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => card_monicOfDegree_le j)
    have h2 := sum_pow_le (Fact.out : p.Prime).two_le d
    exact_mod_cast h1.trans h2
  calc prob (fun ω : Pairs m → Bool => ¬ ∀ α : (ZMod p)[X], α ≠ 0 → α.natDegree < d →
        finrank (ZMod p) (LinearMap.ker (aeval (modP p (symOf a b ω)) α).mulVecLin) ≤
          (d - 1) * (r - 1))
      ≤ prob (fun ω : Pairs m → Bool => ∃ β ∈ S, r ≤ rootGeomMult a b β ω) := prob_mono hbad
    _ ≤ ∑ β ∈ S, prob (fun ω : Pairs m → Bool => r ≤ rootGeomMult a b β ω) :=
        prob_exists_le_sum S _
    _ ≤ ∑ _β ∈ S, 30 * (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4)) :=
        Finset.sum_le_sum fun β hβ => prob_rootGeomMult_le hab hr β (hmonic β hβ)
    _ = S.card * (30 * (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4))) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (p : ℝ) ^ (d - 1) * (30 * (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4))) := by
        gcongr
    _ = 60 * (p : ℝ) ^ (d - 1) * (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4)) := by ring

end KernelPolyProb

end DGS
