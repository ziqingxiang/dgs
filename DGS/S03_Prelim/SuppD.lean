module

public import DGS.S03_Prelim.KernelPoly
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Matrix Polynomial Module Filter Topology

namespace DGS

section Block

theorem pairs_bound {N : ℕ} (q : Pairs N) : (q.1.1 : ℕ) < q.1.2 ∧ (q.1.2 : ℕ) < N :=
  ⟨Fin.lt_def.1 q.2, q.1.2.isLt⟩

def blockEquiv (n s : ℕ) :
    (Pairs (n + s) → Bool) ≃ (Pairs n → Bool) × (Fin s → Fin n → Bool) × (Pairs s → Bool) where
  toFun ω := (fun q => ω ⟨(Fin.castAdd s q.1.1, Fin.castAdd s q.1.2), by
      rw [Fin.lt_def]; simpa using (pairs_bound q).1⟩,
    fun j i => ω ⟨(Fin.castAdd s i, Fin.natAdd n j), by rw [Fin.lt_def]; simp; omega⟩,
    fun q => ω ⟨(Fin.natAdd n q.1.1, Fin.natAdd n q.1.2), by
      rw [Fin.lt_def]; simpa using (pairs_bound q).1⟩)
  invFun x := fun q =>
    if hj : (q.1.2 : ℕ) < n then
      x.1 ⟨(⟨q.1.1, by have := pairs_bound q; omega⟩, ⟨q.1.2, hj⟩), by
        rw [Fin.lt_def]; exact (pairs_bound q).1⟩
    else if hi : (q.1.1 : ℕ) < n then
      x.2.1 ⟨q.1.2 - n, by have := pairs_bound q; omega⟩ ⟨q.1.1, hi⟩
    else
      x.2.2 ⟨(⟨q.1.1 - n, by have := pairs_bound q; omega⟩,
        ⟨q.1.2 - n, by have := pairs_bound q; omega⟩), by
          rw [Fin.lt_def]; have := pairs_bound q; simp only; omega⟩
  left_inv ω := by
    funext q
    obtain ⟨⟨i, j⟩, hij⟩ := q
    have h1 : (i : ℕ) < j := Fin.lt_def.1 hij
    have h2 : (j : ℕ) < n + s := j.isLt
    dsimp only
    split_ifs with hj hi
    all_goals
      congr 1
      try (ext <;> simp <;> omega)
  right_inv x := by
    obtain ⟨x1, x2, x3⟩ := x
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext q
      have := pairs_bound q
      dsimp only
      split_ifs with hj
      · rfl
      all_goals (simp at hj)
    · funext j i
      dsimp only
      split_ifs with hj hi
      · simp at hj
      · congr 1
        try (ext; simp)
      · simp at hi
    · funext q
      have := pairs_bound q
      dsimp only
      split_ifs with hj hi
      · simp at hj
      · simp at hi
      · congr 1
        try (ext <;> simp)

variable {n s : ℕ} (a b : ℤ)

theorem symOf_block_RR (ω : Pairs (n + s) → Bool) (i i' : Fin n) :
    symOf a b ω (Fin.castAdd s i) (Fin.castAdd s i') = symOf a b (blockEquiv n s ω).1 i i' := by
  rcases lt_trichotomy i i' with h | rfl | h
  · rw [symOf_apply_lt _ _ _ (show Fin.castAdd s i < Fin.castAdd s i' by
      rw [Fin.lt_def, Fin.val_castAdd, Fin.val_castAdd]; exact Fin.lt_def.1 h), symOf_apply_lt _ _ _ h]
    rfl
  · simp
  · rw [symOf_apply_gt _ _ _ (show Fin.castAdd s i' < Fin.castAdd s i by
      rw [Fin.lt_def, Fin.val_castAdd, Fin.val_castAdd]; exact Fin.lt_def.1 h), symOf_apply_gt _ _ _ h]
    rfl

theorem symOf_block_RS (ω : Pairs (n + s) → Bool) (i : Fin n) (j : Fin s) :
    symOf a b ω (Fin.castAdd s i) (Fin.natAdd n j) = twoValued a b ((blockEquiv n s ω).2.1 j) i := by
  rw [symOf_apply_lt _ _ _ (show Fin.castAdd s i < Fin.natAdd n j by
    rw [Fin.lt_def]; simp; omega)]
  rfl

end Block

section Krylov

variable {F : Type*} [Field F] {n s : ℕ}

def topPart (v : Fin (n + s) → F) : Fin n → F := fun i => v (Fin.castAdd s i)

def botPart (v : Fin (n + s) → F) : Fin s → F := fun j => v (Fin.natAdd n j)

def blockD (M : Matrix (Fin (n + s)) (Fin (n + s)) F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i i' => M (Fin.castAdd s i) (Fin.castAdd s i')

def blockC (M : Matrix (Fin (n + s)) (Fin (n + s)) F) : Matrix (Fin n) (Fin s) F :=
  Matrix.of fun i j => M (Fin.castAdd s i) (Fin.natAdd n j)

theorem topPart_mulVec (M : Matrix (Fin (n + s)) (Fin (n + s)) F) (v : Fin (n + s) → F) :
    topPart (M *ᵥ v) = blockD M *ᵥ topPart v + blockC M *ᵥ botPart v := by
  funext i
  simp only [topPart, botPart, blockD, blockC, mulVec, dotProduct, Fin.sum_univ_add,
    Matrix.of_apply, Pi.add_apply]

theorem topPart_sum {ι : Type*} (t : Finset ι) (f : ι → Fin (n + s) → F) :
    topPart (∑ i ∈ t, f i) = ∑ i ∈ t, topPart (f i) := by
  funext k
  simp only [topPart, Finset.sum_apply]

theorem topPart_smul (c : F) (v : Fin (n + s) → F) : topPart (c • v) = c • topPart v := rfl

theorem krylov_of_kernel (M : Matrix (Fin (n + s)) (Fin (n + s)) F) {g : F[X]} (hg : g.Monic)
    {d : ℕ} (hd : g.natDegree = d) (hd1 : 1 ≤ d) {y : Fin (n + s) → F} (hyR : topPart y = 0)
    (hgy : aeval M g *ᵥ y = 0) :
    ∃ z : ℕ → Fin s → F, z (d - 1) = botPart y ∧
      ∑ ℓ ∈ Finset.range d, blockD M ^ ℓ *ᵥ (blockC M *ᵥ z ℓ) = 0 := by
  set D := blockD M with hD
  set C := blockC M with hC
  set u : ℕ → Fin s → F := fun k => botPart (M ^ k *ᵥ y) with hu
  have hw : ∀ k, topPart (M ^ k *ᵥ y) =
      ∑ ℓ ∈ Finset.range k, D ^ ℓ *ᵥ (C *ᵥ u (k - 1 - ℓ)) := by
    intro k
    induction k with
    | zero => simpa using hyR
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, topPart_mulVec, ih, Finset.sum_range_succ', mulVec_sum]
      congr 1
      · refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [mulVec_mulVec, ← pow_succ', show k + 1 - 1 - (ℓ + 1) = k - 1 - ℓ by omega]
      · rw [pow_zero, one_mulVec, show k + 1 - 1 - 0 = k by omega]
  have htop : topPart (aeval M g *ᵥ y) = 0 := by rw [hgy]; rfl
  rw [aeval_eq_sum_range, hd, Matrix.sum_mulVec, topPart_sum] at htop
  simp only [smul_mulVec, topPart_smul, hw, Finset.smul_sum] at htop
  rw [Finset.sum_comm' (t' := Finset.range d) (s' := fun ℓ => Finset.Ico (ℓ + 1) (d + 1))
    (fun k ℓ => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)] at htop
  refine ⟨fun ℓ => ∑ k ∈ Finset.Ico (ℓ + 1) (d + 1), g.coeff k • u (k - 1 - ℓ), ?_, ?_⟩
  · have hcoeff : g.coeff d = 1 := by rw [← hd]; exact hg.coeff_natDegree
    dsimp only
    rw [Nat.sub_add_cancel hd1, Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self, Finset.sum_empty,
      zero_add, hcoeff, one_smul, show d - 1 - (d - 1) = 0 by omega]
    simp [hu]
  · rw [← htop]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [mulVec_sum, mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulVec_smul, mulVec_smul]

end Krylov

section Step3

variable {F : Type*} [Field F] {n s : ℕ}

open Classical in
noncomputable def krylovSpan (D : Matrix (Fin n) (Fin n) F) (c : Fin s → Fin n → F) (d : ℕ)
    (j : Fin s) : Submodule F (Fin n → F) :=
  Submodule.span F (((Finset.Iio j ×ˢ Finset.range d).image fun x => D ^ x.2 *ᵥ c x.1 :
    Finset (Fin n → F)) : Set (Fin n → F))

theorem finrank_krylovSpan_le (D : Matrix (Fin n) (Fin n) F) (c : Fin s → Fin n → F) (d : ℕ)
    (j : Fin s) : finrank F (krylovSpan D c d j) ≤ j * d := by
  classical
  unfold krylovSpan
  refine (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans ?_)
  rw [Finset.card_product, Fin.card_Iio, Finset.card_range]

theorem mem_krylovSpan (D : Matrix (Fin n) (Fin n) F) (c : Fin s → Fin n → F) {d : ℕ} {j j' : Fin s}
    (hj : j' < j) {ℓ : ℕ} (hℓ : ℓ < d) : D ^ ℓ *ᵥ c j' ∈ krylovSpan D c d j := by
  classical
  unfold krylovSpan
  apply Submodule.subset_span
  rw [Finset.coe_image]
  exact ⟨(j', ℓ), by simp [hj, hℓ], rfl⟩

theorem krylovSpan_congr (D : Matrix (Fin n) (Fin n) F) {c c' : Fin s → Fin n → F} (d : ℕ)
    (j : Fin s) (h : ∀ j' < j, c j' = c' j') : krylovSpan D c d j = krylovSpan D c' d j := by
  classical
  unfold krylovSpan
  congr 2
  refine Finset.image_congr fun x hx => ?_
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Iio, Set.mem_Iio] at hx
  simp only [h x.1 hx.1]

theorem exists_monic_mem_krylovSpan (D : Matrix (Fin n) (Fin n) F) (c : Fin s → Fin n → F) {d : ℕ}
    {z : ℕ → Fin s → F} (hz0 : ∃ ℓ < d, ∃ j, z ℓ j ≠ 0)
    (hrel : ∑ ℓ ∈ Finset.range d, D ^ ℓ *ᵥ (∑ j, z ℓ j • c j) = 0) :
    ∃ j : Fin s, ∃ α : F[X], α.Monic ∧ α.natDegree < d ∧ aeval D α *ᵥ c j ∈ krylovSpan D c d j := by
  classical
  set J := Finset.univ.filter (fun j : Fin s => ∃ ℓ < d, z ℓ j ≠ 0) with hJdef
  have hJ : J.Nonempty := by
    obtain ⟨ℓ, hℓ, j, hj⟩ := hz0
    exact ⟨j, by simp [hJdef]; exact ⟨ℓ, hℓ, hj⟩⟩
  set j := J.max' hJ with hjdef
  have hjJ : j ∈ J := Finset.max'_mem J hJ
  have hmax : ∀ j', j < j' → ∀ ℓ < d, z ℓ j' = 0 := by
    intro j' hj' ℓ hℓ
    by_contra h
    have : j' ∈ J := by simp [hJdef]; exact ⟨ℓ, hℓ, h⟩
    exact absurd (Finset.le_max' J j' this) (not_le.2 hj')
  set f : Fin s → Fin n → F := fun j' => ∑ ℓ ∈ Finset.range d, z ℓ j' • (D ^ ℓ *ᵥ c j') with hfdef
  have hsum : ∑ j', f j' = 0 := by
    rw [← hrel, hfdef, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [mulVec_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [mulVec_smul]
  have hrest : ∑ j' ∈ Finset.univ.erase j, f j' ∈ krylovSpan D c d j := by
    refine Submodule.sum_mem _ fun j' hj' => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj') with h | h
    · exact Submodule.sum_mem _ fun ℓ hℓ =>
        Submodule.smul_mem _ _ (mem_krylovSpan D c h (Finset.mem_range.1 hℓ))
    · have : f j' = 0 := Finset.sum_eq_zero fun ℓ hℓ => by
        rw [hmax j' h ℓ (Finset.mem_range.1 hℓ), zero_smul]
      rw [this]
      exact Submodule.zero_mem _
  have hfj : f j ∈ krylovSpan D c d j := by
    have h1 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ j)
    rw [hsum] at h1
    have h2 : f j = -∑ j' ∈ Finset.univ.erase j, f j' := eq_neg_of_add_eq_zero_left h1
    rw [h2]
    exact Submodule.neg_mem _ hrest
  set α0 : F[X] := ∑ ℓ ∈ Finset.range d, C (z ℓ j) * X ^ ℓ with hα0def
  have hα0 : α0 ≠ 0 := by
    have hj' : ∃ ℓ < d, z ℓ j ≠ 0 := by simpa [hJdef] using hjJ
    obtain ⟨ℓ, hℓ, hz⟩ := hj'
    intro h0
    apply hz
    have := congrArg (fun q : F[X] => q.coeff ℓ) h0
    simp only [hα0def, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single ℓ (fun b _ hb => by rw [ite_eq_right (Ne.symm hb)])
      (fun h => absurd (Finset.mem_range.2 hℓ) h), ite_eq_left rfl] at this
    exact this
  have hdeg : α0.natDegree < d := by
    have h1 : α0.natDegree ≤ d - 1 := natDegree_sum_le_of_forall_le _ _ fun ℓ hℓ =>
      (natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.1 hℓ; omega)
    have hd : 0 < d := by
      obtain ⟨ℓ, hℓ, -⟩ := hz0
      omega
    omega
  have haeval : aeval D α0 *ᵥ c j = f j := by
    rw [hα0def, map_sum, Matrix.sum_mulVec, hfdef]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [map_mul, aeval_C, aeval_X_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      Matrix.one_mul, smul_mulVec]
  refine ⟨j, α0 * C α0.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hα0, ?_, ?_⟩
  · rw [natDegree_mul_leadingCoeff_inv _ hα0]
    exact hdeg
  · rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one,
      smul_mulVec, haeval]
    exact Submodule.smul_mem _ _ hfj

theorem finrank_comap_le {N : ℕ} (A : Matrix (Fin N) (Fin N) F) (V : Submodule F (Fin N → F)) :
    finrank F (V.comap A.mulVecLin) ≤ finrank F V + finrank F (LinearMap.ker A.mulVecLin) := by
  have hmaps : ∀ x ∈ V.comap A.mulVecLin, A.mulVecLin x ∈ V := fun x hx => hx
  let f := A.mulVecLin.restrict hmaps
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : finrank F (LinearMap.range f) ≤ finrank F V := Submodule.finrank_le _
  let ι : LinearMap.ker f →ₗ[F] (Fin N → F) := (V.comap A.mulVecLin).subtype ∘ₗ (LinearMap.ker f).subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hrange : LinearMap.range ι ≤ LinearMap.ker A.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    have hx : f x = 0 := x.2
    exact congrArg Subtype.val hx
  have h3 : finrank F (LinearMap.ker f) ≤ finrank F (LinearMap.ker A.mulVecLin) := by
    rw [← LinearMap.finrank_range_of_inj hι]
    exact Submodule.finrank_mono hrange
  omega

end Step3

section Step3Prob

theorem prob_twoValued_mem_le {F : Type*} [Field F] {N : ℕ} {a b : F} (hab : a ≠ b)
    (W : Submodule F (Fin N → F)) :
    prob (fun t : Fin N → Bool => twoValued a b t ∈ W) ≤ (2 : ℝ) ^ finrank F W / 2 ^ N := by
  have hcount := lem_odlyzko a b hab W 0
  have hcongr : prob (fun t : Fin N → Bool => twoValued a b t ∈ W) =
      prob (fun t : Fin N → Bool => twoValued a b t - 0 ∈ W) := prob_congr fun t => by rw [sub_zero]
  rw [hcongr]
  unfold prob
  have hN : Nat.card (Fin N → Bool) = 2 ^ N := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [hN]
  push_cast
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)

variable {p : ℕ} [Fact p.Prime] {n s : ℕ}

theorem prob_mem_krylovSpan_le {a b : ℤ} (hab : (a : ZMod p) ≠ (b : ZMod p))
    (D : Matrix (Fin n) (Fin n) (ZMod p)) (d : ℕ) (j : Fin s) (α : (ZMod p)[X]) {κ : ℕ}
    (hκ : finrank (ZMod p) (LinearMap.ker (aeval D α).mulVecLin) < κ) :
    prob (fun cols : Fin s → Fin n → Bool =>
      aeval D α *ᵥ twoValued (a : ZMod p) (b : ZMod p) (cols j) ∈
        krylovSpan D (fun j' => twoValued (a : ZMod p) (b : ZMod p) (cols j')) d j) ≤
      (2 : ℝ) ^ (j * d + κ) / 2 ^ n := by
  classical
  let e := Equiv.piSplitAt j (fun _ : Fin s => Fin n → Bool)
  rw [← prob_equiv e.symm]
  refine prob_le_of_forall_snd (fun o => ?_) (by positivity)
  set c0 : Fin s → Fin n → ZMod p := fun j' => twoValued (a : ZMod p) (b : ZMod p)
    (if h : j' = j then fun _ => true else o ⟨j', h⟩) with hc0
  have hV : ∀ t, krylovSpan D (fun j' => twoValued (a : ZMod p) (b : ZMod p) (e.symm (t, o) j')) d j =
      krylovSpan D c0 d j := by
    intro t
    apply krylovSpan_congr
    intro j' hj'
    simp [e, Equiv.piSplitAt_symm_apply, hc0, hj'.ne]
  have hj : ∀ t, e.symm (t, o) j = t := fun t => by simp [e, Equiv.piSplitAt_symm_apply]
  simp only [hV, hj]
  set W := (krylovSpan D c0 d j).comap (aeval D α).mulVecLin with hWdef
  have hW : finrank (ZMod p) W ≤ j * d + κ := (finrank_comap_le _ _).trans (by
    have := finrank_krylovSpan_le D c0 d j
    omega)
  calc prob (fun t : Fin n → Bool => aeval D α *ᵥ twoValued (a : ZMod p) (b : ZMod p) t ∈
        krylovSpan D c0 d j)
      = prob (fun t : Fin n → Bool => twoValued (a : ZMod p) (b : ZMod p) t ∈ W) :=
        prob_congr fun t => by rw [hWdef, Submodule.mem_comap, mulVecLin_apply]
    _ ≤ (2 : ℝ) ^ finrank (ZMod p) W / 2 ^ n := prob_twoValued_mem_le hab W
    _ ≤ (2 : ℝ) ^ (j * d + κ) / 2 ^ n := by
        gcongr
        · norm_num

theorem mem_monicOfDegree_iff {k : ℕ} {α : (ZMod p)[X]} (h : α ∈ monicOfDegree p k) :
    α.Monic ∧ α.natDegree = k := by
  unfold monicOfDegree at h
  rw [Finset.mem_image] at h
  obtain ⟨v, -, rfl⟩ := h
  exact ⟨monic_X_pow_add (degree_sum_fin_lt v), by
    rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt v),
      natDegree_X_pow]⟩

omit [Fact (Nat.Prime p)] in
theorem sum_range_pow_le (hp : 2 ≤ p) {d : ℕ} (hd : 1 ≤ d) :
    ∑ k ∈ Finset.range d, p ^ k ≤ 2 * p ^ (d - 1) := by
  induction d with
  | zero => omega
  | succ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd'
    · simp
    · rw [Finset.sum_range_succ, Nat.add_sub_cancel]
      have h1 : 2 * p ^ (d - 1) ≤ p ^ d := by
        calc 2 * p ^ (d - 1) ≤ p * p ^ (d - 1) := Nat.mul_le_mul_right _ hp
          _ = p ^ d := by rw [← pow_succ', Nat.sub_add_cancel hd']
      have := ih hd'
      omega

theorem prob_krylov_dep {a b : ℤ} (hab : (a : ZMod p) ≠ (b : ZMod p))
    (D : Matrix (Fin n) (Fin n) (ZMod p)) {d κ : ℕ} (hd : 1 ≤ d)
    (hD : ∀ α : (ZMod p)[X], α.Monic → α.natDegree < d →
      finrank (ZMod p) (LinearMap.ker (aeval D α).mulVecLin) < κ) :
    prob (fun cols : Fin s → Fin n → Bool => ∃ z : ℕ → Fin s → ZMod p, (∃ ℓ < d, ∃ j, z ℓ j ≠ 0) ∧
      ∑ ℓ ∈ Finset.range d, D ^ ℓ *ᵥ (∑ j, z ℓ j • twoValued (a : ZMod p) (b : ZMod p) (cols j)) = 0) ≤
      s * (2 * (p : ℝ) ^ (d - 1)) * ((2 : ℝ) ^ ((s - 1) * d + κ) / 2 ^ n) := by
  classical
  set T : Finset (ZMod p)[X] := (Finset.range d).biUnion (monicOfDegree p) with hT
  have hTmem : ∀ α ∈ T, α.Monic ∧ α.natDegree < d := by
    intro α hα
    rw [hT, Finset.mem_biUnion] at hα
    obtain ⟨k, hk, hαk⟩ := hα
    obtain ⟨h1, h2⟩ := mem_monicOfDegree_iff hαk
    exact ⟨h1, h2 ▸ Finset.mem_range.1 hk⟩
  have hTcard : (T.card : ℝ) ≤ 2 * (p : ℝ) ^ (d - 1) := by
    have h1 : T.card ≤ ∑ k ∈ Finset.range d, p ^ k :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k _ => card_monicOfDegree_le k)
    have h2 := sum_range_pow_le (Fact.out : p.Prime).two_le hd
    exact_mod_cast h1.trans h2
  have hsub : ∀ cols : Fin s → Fin n → Bool, (∃ z : ℕ → Fin s → ZMod p, (∃ ℓ < d, ∃ j, z ℓ j ≠ 0) ∧
      ∑ ℓ ∈ Finset.range d, D ^ ℓ *ᵥ (∑ j, z ℓ j • twoValued (a : ZMod p) (b : ZMod p) (cols j)) = 0) →
      ∃ j ∈ (Finset.univ : Finset (Fin s)), ∃ α ∈ T,
        aeval D α *ᵥ twoValued (a : ZMod p) (b : ZMod p) (cols j) ∈
          krylovSpan D (fun j' => twoValued (a : ZMod p) (b : ZMod p) (cols j')) d j := by
    rintro cols ⟨z, hz0, hrel⟩
    obtain ⟨j, α, hαm, hαd, hmem⟩ := exists_monic_mem_krylovSpan D _ hz0 hrel
    refine ⟨j, Finset.mem_univ _, α, ?_, hmem⟩
    rw [hT, Finset.mem_biUnion]
    exact ⟨α.natDegree, Finset.mem_range.2 hαd, by simpa using mem_monicOfDegree hαm⟩
  have hbound : ∀ j : Fin s, ∀ α ∈ T, prob (fun cols : Fin s → Fin n → Bool =>
      aeval D α *ᵥ twoValued (a : ZMod p) (b : ZMod p) (cols j) ∈
        krylovSpan D (fun j' => twoValued (a : ZMod p) (b : ZMod p) (cols j')) d j) ≤
      (2 : ℝ) ^ ((s - 1) * d + κ) / 2 ^ n := by
    intro j α hα
    refine (prob_mem_krylovSpan_le hab D d j α (hD α (hTmem α hα).1 (hTmem α hα).2)).trans ?_
    gcongr
    · norm_num
    · have := j.isLt
      omega
  calc prob (fun cols : Fin s → Fin n → Bool => ∃ z : ℕ → Fin s → ZMod p, (∃ ℓ < d, ∃ j, z ℓ j ≠ 0) ∧
        ∑ ℓ ∈ Finset.range d, D ^ ℓ *ᵥ (∑ j, z ℓ j • twoValued (a : ZMod p) (b : ZMod p) (cols j)) = 0)
      ≤ prob (fun cols : Fin s → Fin n → Bool => ∃ j ∈ (Finset.univ : Finset (Fin s)), ∃ α ∈ T,
          aeval D α *ᵥ twoValued (a : ZMod p) (b : ZMod p) (cols j) ∈
            krylovSpan D (fun j' => twoValued (a : ZMod p) (b : ZMod p) (cols j')) d j) :=
        prob_mono hsub
    _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin s)), prob (fun cols : Fin s → Fin n → Bool => ∃ α ∈ T,
          aeval D α *ᵥ twoValued (a : ZMod p) (b : ZMod p) (cols j) ∈
            krylovSpan D (fun j' => twoValued (a : ZMod p) (b : ZMod p) (cols j')) d j) :=
        prob_exists_le_sum _ _
    _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin s)), ∑ _α ∈ T, (2 : ℝ) ^ ((s - 1) * d + κ) / 2 ^ n := by
        refine Finset.sum_le_sum fun j _ => (prob_exists_le_sum _ _).trans ?_
        exact Finset.sum_le_sum fun α hα => hbound j α hα
    _ = s * (T.card * ((2 : ℝ) ^ ((s - 1) * d + κ) / 2 ^ n)) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          nsmul_eq_mul]
    _ ≤ s * (2 * (p : ℝ) ^ (d - 1) * ((2 : ℝ) ^ ((s - 1) * d + κ) / 2 ^ n)) := by
        gcongr
    _ = s * (2 * (p : ℝ) ^ (d - 1)) * ((2 : ℝ) ^ ((s - 1) * d + κ) / 2 ^ n) := by ring

end Step3Prob

section TopBlock

variable {p : ℕ} [Fact p.Prime] {a b : ℤ} {n s : ℕ}

omit [Fact (Nat.Prime p)] in
theorem blockD_modP (ω : Pairs (n + s) → Bool) :
    blockD (modP p (symOf a b ω)) = modP p (symOf a b (blockEquiv n s ω).1) := by
  ext i i'
  simp only [blockD, modP, Matrix.of_apply, Matrix.map_apply, symOf_block_RR]

theorem blockC_modP_mulVec (ω : Pairs (n + s) → Bool) (v : Fin s → ZMod p) :
    blockC (modP p (symOf a b ω)) *ᵥ v =
      ∑ j, v j • twoValued (a : ZMod p) (b : ZMod p) ((blockEquiv n s ω).2.1 j) := by
  funext i
  simp only [blockC, modP, mulVec, dotProduct, Matrix.of_apply, Matrix.map_apply, symOf_block_RS,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, twoValued]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [mul_comm]

theorem botPart_ne_zero {F : Type*} [Field F] {y : Fin (n + s) → F} (hy : y ≠ 0)
    (hyR : topPart y = 0) : botPart y ≠ 0 := by
  intro h
  apply hy
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · exact congrFun hyR i
  · exact congrFun h j

theorem not_dvd_of_ne (hab : (a : ZMod p) ≠ (b : ZMod p)) : ¬ (p : ℤ) ∣ a - b := by
  intro h
  apply hab
  rw [← sub_eq_zero, ← Int.cast_sub]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h

theorem prob_badTop_le (hab : (a : ZMod p) ≠ (b : ZMod p)) {d r0 : ℕ} (hd : 1 ≤ d) (hr0 : 1 ≤ r0) :
    prob (fun ω : Pairs (n + s) → Bool => ∃ g : (ZMod p)[X], g.Monic ∧ g.natDegree = d ∧
      ∃ y : Fin (n + s) → ZMod p, y ≠ 0 ∧ topPart y = 0 ∧ aeval (modP p (symOf a b ω)) g *ᵥ y = 0) ≤
      60 * (p : ℝ) ^ (d - 1) * (2 : ℝ) ^ (-((r0 : ℝ) ^ 2 / 4)) +
        s * (2 * (p : ℝ) ^ (d - 1)) * ((2 : ℝ) ^ ((s - 1) * d + ((d - 1) * (r0 - 1) + 1)) / 2 ^ n) := by
  classical
  set κ := (d - 1) * (r0 - 1) + 1 with hκ
  set be := blockEquiv n s
  let Good : (Pairs n → Bool) → Prop := fun ωR => ∀ α : (ZMod p)[X], α ≠ 0 → α.natDegree < d →
    finrank (ZMod p) (LinearMap.ker (aeval (modP p (symOf a b ωR)) α).mulVecLin) ≤ (d - 1) * (r0 - 1)
  let Dep : (Pairs n → Bool) → (Fin s → Fin n → Bool) → Prop := fun ωR cols =>
    ∃ z : ℕ → Fin s → ZMod p, (∃ ℓ < d, ∃ j, z ℓ j ≠ 0) ∧
      ∑ ℓ ∈ Finset.range d, modP p (symOf a b ωR) ^ ℓ *ᵥ
        (∑ j, z ℓ j • twoValued (a : ZMod p) (b : ZMod p) (cols j)) = 0
  have himp : ∀ ω : Pairs (n + s) → Bool, (∃ g : (ZMod p)[X], g.Monic ∧ g.natDegree = d ∧
      ∃ y : Fin (n + s) → ZMod p, y ≠ 0 ∧ topPart y = 0 ∧ aeval (modP p (symOf a b ω)) g *ᵥ y = 0) →
      ¬ Good (be ω).1 ∨ (Good (be ω).1 ∧ Dep (be ω).1 (be ω).2.1) := by
    rintro ω ⟨g, hgm, hgd, y, hy0, hyR, hgy⟩
    by_cases hG : Good (be ω).1
    · right
      refine ⟨hG, ?_⟩
      obtain ⟨z, hz, hrel⟩ := krylov_of_kernel (modP p (symOf a b ω)) hgm hgd hd hyR hgy
      refine ⟨z, ?_, ?_⟩
      · obtain ⟨j, hj⟩ := Function.ne_iff.1 (botPart_ne_zero hy0 hyR)
        exact ⟨d - 1, by omega, j, by rw [hz]; exact hj⟩
      · rw [← hrel]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [blockD_modP, blockC_modP_mulVec]
    · exact Or.inl hG
  have h1 : prob (fun ω : Pairs (n + s) → Bool => ¬ Good (be ω).1) ≤
      60 * (p : ℝ) ^ (d - 1) * (2 : ℝ) ^ (-((r0 : ℝ) ^ 2 / 4)) := by
    rw [← prob_equiv be.symm]
    simp only [Equiv.apply_symm_apply]
    rw [prob_fst (fun ωR : Pairs n → Bool => ¬ Good ωR)]
    exact cor_kernelpoly (not_dvd_of_ne hab) d r0 hr0 n
  have h2 : prob (fun ω : Pairs (n + s) → Bool => Good (be ω).1 ∧ Dep (be ω).1 (be ω).2.1) ≤
      s * (2 * (p : ℝ) ^ (d - 1)) * ((2 : ℝ) ^ ((s - 1) * d + κ) / 2 ^ n) := by
    rw [← prob_equiv be.symm]
    simp only [Equiv.apply_symm_apply]
    refine prob_le_of_forall_fst (fun ωR => ?_) (by positivity)
    by_cases hG : Good ωR
    · have hD : ∀ α : (ZMod p)[X], α.Monic → α.natDegree < d →
          finrank (ZMod p) (LinearMap.ker (aeval (modP p (symOf a b ωR)) α).mulVecLin) < κ :=
        fun α hαm hαd => by have := hG α hαm.ne_zero hαd; omega
      calc prob (fun x : (Fin s → Fin n → Bool) × (Pairs s → Bool) => Good ωR ∧ Dep ωR x.1)
          = prob (fun cols : Fin s → Fin n → Bool => Dep ωR cols) := by
            rw [← prob_fst (fun cols : Fin s → Fin n → Bool => Dep ωR cols) (Ω' := Pairs s → Bool)]
            exact prob_congr fun x => ⟨fun h => h.2, fun h => ⟨hG, h⟩⟩
        _ ≤ _ := prob_krylov_dep hab _ hd hD
    · calc prob (fun x : (Fin s → Fin n → Bool) × (Pairs s → Bool) => Good ωR ∧ Dep ωR x.1)
          = prob (fun _ : (Fin s → Fin n → Bool) × (Pairs s → Bool) => False) :=
            prob_congr fun x => ⟨fun h => hG h.1, False.elim⟩
        _ = 0 := prob_false
        _ ≤ _ := by positivity
  calc prob (fun ω : Pairs (n + s) → Bool => ∃ g : (ZMod p)[X], g.Monic ∧ g.natDegree = d ∧
        ∃ y : Fin (n + s) → ZMod p, y ≠ 0 ∧ topPart y = 0 ∧ aeval (modP p (symOf a b ω)) g *ᵥ y = 0)
      ≤ prob (fun ω : Pairs (n + s) → Bool => ¬ Good (be ω).1 ∨
          (Good (be ω).1 ∧ Dep (be ω).1 (be ω).2.1)) := prob_mono himp
    _ ≤ prob (fun ω : Pairs (n + s) → Bool => ¬ Good (be ω).1) +
          prob (fun ω : Pairs (n + s) → Bool => Good (be ω).1 ∧ Dep (be ω).1 (be ω).2.1) :=
        prob_or_le _ _
    _ ≤ _ := add_le_add h1 h2

end TopBlock

section Permute

variable {m : ℕ}

def sortPair (u v : Fin m) (h : u ≠ v) : Pairs m :=
  if huv : u < v then ⟨(u, v), huv⟩ else ⟨(v, u), lt_of_le_of_ne (not_lt.1 huv) (Ne.symm h)⟩

theorem sortPair_of_lt {u v : Fin m} (h : u < v) : sortPair u v h.ne = ⟨(u, v), h⟩ := by
  simp [sortPair, h]

theorem sortPair_comm {u v : Fin m} (h : u ≠ v) : sortPair u v h = sortPair v u (Ne.symm h) := by
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [sortPair, h', not_lt.2 h'.le]
  · simp [sortPair, h', not_lt.2 h'.le]

theorem sortPair_ne (q : Pairs m) : q.1.1 ≠ q.1.2 := ne_of_lt q.2

theorem sortPair_map (σ : Equiv.Perm (Fin m)) {u v : Fin m} (h : u ≠ v) :
    sortPair (σ (sortPair u v h).1.1) (σ (sortPair u v h).1.2)
      (σ.injective.ne (sortPair_ne _)) = sortPair (σ u) (σ v) (σ.injective.ne h) := by
  rcases lt_or_gt_of_ne h with h' | h'
  · simp only [sortPair, h', dite_true]
  · simp only [sortPair, not_lt.2 h'.le, dite_false]
    exact sortPair_comm (σ.injective.ne (Ne.symm h))

def permPairs (σ : Equiv.Perm (Fin m)) : Pairs m ≃ Pairs m where
  toFun q := sortPair (σ q.1.1) (σ q.1.2) (σ.injective.ne (sortPair_ne q))
  invFun q := sortPair (σ.symm q.1.1) (σ.symm q.1.2) (σ.symm.injective.ne (sortPair_ne q))
  left_inv q := by
    obtain ⟨⟨i, j⟩, hij⟩ := q
    dsimp only
    rw [sortPair_map σ.symm]
    simp only [Equiv.symm_apply_apply]
    exact sortPair_of_lt hij
  right_inv q := by
    obtain ⟨⟨i, j⟩, hij⟩ := q
    dsimp only
    rw [sortPair_map σ]
    simp only [Equiv.apply_symm_apply]
    exact sortPair_of_lt hij

theorem symOf_sortPair (a b : ℤ) (ω : Pairs m → Bool) {u v : Fin m} (h : u ≠ v) :
    symOf a b ω u v = if ω (sortPair u v h) then a else b := by
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [symOf_apply_lt _ _ _ h']
    simp [sortPair, h']
  · rw [symOf_apply_gt _ _ _ h']
    simp [sortPair, not_lt.2 h'.le]

theorem symOf_comp_permPairs (a b : ℤ) (σ : Equiv.Perm (Fin m)) (ω : Pairs m → Bool) :
    symOf a b (ω ∘ permPairs σ) = (symOf a b ω).submatrix σ σ := by
  ext i j
  rw [submatrix_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [symOf_sortPair a b _ h, symOf_sortPair a b _ (σ.injective.ne h)]
    simp only [Function.comp_apply]
    congr 2
    exact congrArg ω (sortPair_map σ h)

theorem prob_comp_permPairs (σ : Equiv.Perm (Fin m)) (P : (Pairs m → Bool) → Prop) :
    prob (fun ω : Pairs m → Bool => P (ω ∘ permPairs σ)) = prob P :=
  prob_equiv ((permPairs σ).symm.arrowCongr (Equiv.refl Bool)) P

theorem exists_perm_compl {n s : ℕ} (S : Finset (Fin (n + s))) (hS : S.card = s) :
    ∃ σ : Equiv.Perm (Fin (n + s)), ∀ i : Fin n, σ (Fin.castAdd s i) ∉ S := by
  classical
  have hcS : Fintype.card {x // x ∈ S} = s := by rw [Fintype.card_coe, hS]
  have hcR : Fintype.card {x // x ∉ S} = n := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hS, Fintype.card_fin]
    omega
  let eR : Fin n ≃ {x // x ∉ S} := (Fintype.equivFinOfCardEq hcR).symm
  let eS : Fin s ≃ {x // x ∈ S} := (Fintype.equivFinOfCardEq hcS).symm
  let σ : Equiv.Perm (Fin (n + s)) := finSumFinEquiv.symm.trans
    ((eR.sumCongr eS).trans ((Equiv.sumComm _ _).trans (Equiv.sumCompl (· ∈ S))))
  refine ⟨σ, fun i => ?_⟩
  have : σ (Fin.castAdd s i) = (eR i : Fin (n + s)) := by
    simp [σ, finSumFinEquiv_symm_apply_castAdd]
  rw [this]
  exact (eR i).2

end Permute

section AnyS

variable {p : ℕ} [Fact p.Prime] {a b : ℤ}

def BadS (p : ℕ) (a b : ℤ) {m : ℕ} (d : ℕ) (S : Finset (Fin m)) (ω : Pairs m → Bool) : Prop :=
  ∃ g : (ZMod p)[X], g.Monic ∧ g.natDegree = d ∧ ∃ y : Fin m → ZMod p, y ≠ 0 ∧ (∀ i ∉ S, y i = 0) ∧
    aeval (modP p (symOf a b ω)) g *ᵥ y = 0

theorem aeval_submatrix {R : Type*} [CommRing R] {m : ℕ} (σ : Equiv.Perm (Fin m))
    (A : Matrix (Fin m) (Fin m) R) (g : R[X]) :
    aeval (A.submatrix σ σ) g = (aeval A g).submatrix σ σ := by
  have hre : ∀ X : Matrix (Fin m) (Fin m) R,
      X.submatrix σ σ = Matrix.reindexAlgEquiv R R σ.symm X := fun X => by
    rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Equiv.symm_symm]
  rw [hre, hre, aeval_algEquiv, AlgHom.comp_apply]
  rfl

theorem prob_badS_le (hab : (a : ZMod p) ≠ (b : ZMod p)) {m n s d r0 : ℕ} (hm : n + s = m)
    (hd : 1 ≤ d) (hr0 : 1 ≤ r0) (S : Finset (Fin m)) (hS : S.card = s) :
    prob (BadS p a b d S) ≤
      60 * (p : ℝ) ^ (d - 1) * (2 : ℝ) ^ (-((r0 : ℝ) ^ 2 / 4)) +
        s * (2 * (p : ℝ) ^ (d - 1)) * ((2 : ℝ) ^ ((s - 1) * d + ((d - 1) * (r0 - 1) + 1)) / 2 ^ n) := by
  subst hm
  obtain ⟨σ, hσ⟩ := exists_perm_compl S hS
  refine le_trans ?_ (prob_badTop_le (n := n) (s := s) hab hd hr0)
  rw [← prob_comp_permPairs σ.symm]
  apply prob_mono
  rintro ω ⟨g, hgm, hgd, y, hy0, hyS, hgy⟩
  refine ⟨g, hgm, hgd, y ∘ σ, ?_, ?_, ?_⟩
  · intro h
    apply hy0
    funext k
    have := congrFun h (σ.symm k)
    simpa using this
  · funext i
    exact hyS _ (hσ i)
  · have h1 := hgy
    unfold modP at h1 ⊢
    rw [symOf_comp_permPairs, ← Matrix.submatrix_map, aeval_submatrix,
      Matrix.submatrix_mulVec_equiv, Equiv.symm_symm] at h1
    funext k
    have := congrFun h1 (σ k)
    simpa using this

end AnyS

section Estimates

theorem sum_choose_le (m : ℕ) :
    ∑ k ∈ (Finset.range (m + 1)).filter (fun k => 8 * k ≤ m), (m.choose k : ℝ) ≤
      (8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8) := by
  set B := (8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8) with hB
  have hbin : ∑ k ∈ Finset.range (m + 1), ((1 : ℝ) / 8) ^ k * (7 / 8) ^ (m - k) * (m.choose k) = 1 := by
    rw [← add_pow]
    norm_num
  have hterm : ∀ k ∈ (Finset.range (m + 1)).filter (fun k => 8 * k ≤ m),
      (m.choose k : ℝ) ≤ ((1 : ℝ) / 8) ^ k * (7 / 8) ^ (m - k) * (m.choose k) * B := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨j, hj⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
    have hmk : m - k = j := by omega
    have h1 : ((1 : ℝ) / 8) ^ k * (7 / 8) ^ (m - k) * (8 / 7 : ℝ) ^ m = ((7 : ℝ) ^ k)⁻¹ := by
      rw [hmk, hj, pow_add, div_pow, div_pow, div_pow, one_pow]
      field_simp
      rw [← mul_pow]
      norm_num
    have h2 : (7 : ℝ) ^ k ≤ (7 : ℝ) ^ ((m : ℝ) / 8) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (8 : ℝ) * k ≤ m := by exact_mod_cast hk.2
      linarith
    have h7 : (0 : ℝ) < (7 : ℝ) ^ k := by positivity
    have h3 : (1 : ℝ) ≤ ((1 : ℝ) / 8) ^ k * (7 / 8) ^ (m - k) * B := by
      rw [hB, ← mul_assoc, h1, inv_mul_eq_div, le_div_iff₀ h7, one_mul]
      exact h2
    have hc : (0 : ℝ) ≤ m.choose k := Nat.cast_nonneg _
    nlinarith
  calc ∑ k ∈ (Finset.range (m + 1)).filter (fun k => 8 * k ≤ m), (m.choose k : ℝ)
      ≤ ∑ k ∈ (Finset.range (m + 1)).filter (fun k => 8 * k ≤ m),
          ((1 : ℝ) / 8) ^ k * (7 / 8) ^ (m - k) * (m.choose k) * B := Finset.sum_le_sum hterm
    _ = (∑ k ∈ (Finset.range (m + 1)).filter (fun k => 8 * k ≤ m),
          ((1 : ℝ) / 8) ^ k * (7 / 8) ^ (m - k) * (m.choose k)) * B := by rw [Finset.sum_mul]
    _ ≤ (∑ k ∈ Finset.range (m + 1), ((1 : ℝ) / 8) ^ k * (7 / 8) ^ (m - k) * (m.choose k)) * B :=
        mul_le_mul_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => by positivity)) (by positivity)
    _ = B := by rw [hbin, one_mul]

theorem pow_le_exp_of_le {p d m : ℕ} (hp : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (hd : (d : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4)) :
    (p : ℝ) ^ (d - 1) ≤ Real.exp ((m : ℝ) ^ ((3 : ℝ) / 8)) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc (p : ℝ) ^ (d - 1) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) ^ (d - 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg p) hp _
    _ = Real.exp (((d - 1 : ℕ) : ℝ) * (m : ℝ) ^ ((1 : ℝ) / 8)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ ((1 : ℝ) / 8)) := by
        apply Real.exp_le_exp.2
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hm0 _)
        refine le_trans ?_ hd
        exact_mod_cast Nat.sub_le d 1
    _ = Real.exp ((m : ℝ) ^ ((3 : ℝ) / 8)) := by
        rcases eq_or_lt_of_le hm0 with h | h
        · rw [← h, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num),
            Real.zero_rpow (by norm_num), zero_mul]
        · rw [← Real.rpow_add h]
          norm_num

theorem kappa_le {d m : ℕ} (hm : 1 ≤ m) (hd : (d : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4)) :
    (((d - 1) * (2 * (Nat.sqrt m + 1) - 1) : ℕ) : ℝ) ≤ 3 * (m : ℝ) ^ ((3 : ℝ) / 4) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hsq : (Nat.sqrt m : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.nat_sqrt_le_real_sqrt
  have hsq1 : (1 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hm1 (by norm_num)
  have hr : ((2 * (Nat.sqrt m + 1) - 1 : ℕ) : ℝ) ≤ 3 * (m : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [show 2 * (Nat.sqrt m + 1) - 1 = 2 * Nat.sqrt m + 1 by omega]
    push_cast
    linarith
  have hd1 : ((d - 1 : ℕ) : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := by
    refine le_trans ?_ hd
    exact_mod_cast Nat.sub_le d 1
  calc (((d - 1) * (2 * (Nat.sqrt m + 1) - 1) : ℕ) : ℝ)
      = ((d - 1 : ℕ) : ℝ) * ((2 * (Nat.sqrt m + 1) - 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (m : ℝ) ^ ((1 : ℝ) / 4) * (3 * (m : ℝ) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul hd1 hr (Nat.cast_nonneg _) (Real.rpow_nonneg hm0.le _)
    _ = 3 * (m : ℝ) ^ ((3 : ℝ) / 4) := by
        rw [mul_comm, mul_assoc, ← Real.rpow_add hm0]
        norm_num

end Estimates

section Final

noncomputable def Ybound (m : ℕ) : ℝ :=
  (60 + 4 * m) * Real.exp ((m : ℝ) ^ ((3 : ℝ) / 8)) *
    (2 : ℝ) ^ (3 * (m : ℝ) ^ ((3 : ℝ) / 4) + 1 - 3 * (m : ℝ) / 4)

theorem prob_badS_le_Y {p : ℕ} [Fact p.Prime] {a b : ℤ} (hab : (a : ZMod p) ≠ (b : ZMod p))
    {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hdm : (d : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4))
    (hp : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) (S : Finset (Fin m)) (hS1 : 1 ≤ S.card)
    (hS : 4 * (d + 1) * S.card ≤ m) : prob (BadS p a b d S) ≤ Ybound m := by
  set s := S.card with hs
  set r0 := 2 * (Nat.sqrt m + 1) with hr0def
  have hr0 : 1 ≤ r0 := by omega
  have hsm : s ≤ m := by nlinarith
  have h := prob_badS_le hab (n := m - s) (s := s) (by omega) hd hr0 S rfl
  refine h.trans ?_
  have hpd := pow_le_exp_of_le hp hdm
  have hκ := kappa_le hm hdm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hE : 0 ≤ Real.exp ((m : ℝ) ^ ((3 : ℝ) / 8)) := (Real.exp_pos _).le
  set X : ℝ := 3 * (m : ℝ) ^ ((3 : ℝ) / 4) + 1 - 3 * (m : ℝ) / 4 with hX
  have hm34 : 0 ≤ (m : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  have hr0sq : (m : ℝ) ≤ (r0 : ℝ) ^ 2 / 4 := by
    have h1 : m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := Nat.lt_succ_sqrt m
    have h2 : (m : ℝ) < ((Nat.sqrt m : ℝ) + 1) * ((Nat.sqrt m : ℝ) + 1) := by exact_mod_cast h1
    rw [hr0def]
    push_cast
    nlinarith
  have hT1 : 60 * (p : ℝ) ^ (d - 1) * (2 : ℝ) ^ (-((r0 : ℝ) ^ 2 / 4)) ≤
      60 * Real.exp ((m : ℝ) ^ ((3 : ℝ) / 8)) * (2 : ℝ) ^ X := by
    gcongr
    · norm_num
    · rw [hX]
      linarith
  have hexp : ((((s - 1) * d + ((d - 1) * (r0 - 1) + 1) : ℕ) : ℝ)) - ((m - s : ℕ) : ℝ) ≤ X := by
    have hS' : (4 : ℝ) * (d + 1) * s ≤ m := by exact_mod_cast hS
    have hκ' := hκ
    rw [hX]
    rw [Nat.cast_sub hsm]
    push_cast [Nat.cast_sub hS1]
    push_cast at hκ'
    nlinarith
  have hT2 : (s : ℝ) * (2 * (p : ℝ) ^ (d - 1)) *
      ((2 : ℝ) ^ ((s - 1) * d + ((d - 1) * (r0 - 1) + 1)) / 2 ^ (m - s)) ≤
      m * (2 * Real.exp ((m : ℝ) ^ ((3 : ℝ) / 8))) * (2 : ℝ) ^ X := by
    have h2pow : (2 : ℝ) ^ ((s - 1) * d + ((d - 1) * (r0 - 1) + 1)) / 2 ^ (m - s) =
        (2 : ℝ) ^ ((((s - 1) * d + ((d - 1) * (r0 - 1) + 1) : ℕ) : ℝ) - ((m - s : ℕ) : ℝ)) := by
      rw [Real.rpow_sub two_pos, Real.rpow_natCast, Real.rpow_natCast]
    rw [h2pow]
    have hsm' : (s : ℝ) ≤ m := by exact_mod_cast hsm
    gcongr
    all_goals norm_num
  have hX2 : (2 : ℝ) ^ X ≥ 0 := (Real.rpow_pos_of_pos two_pos _).le
  calc 60 * (p : ℝ) ^ (d - 1) * (2 : ℝ) ^ (-((r0 : ℝ) ^ 2 / 4)) +
        s * (2 * (p : ℝ) ^ (d - 1)) * ((2 : ℝ) ^ ((s - 1) * d + ((d - 1) * (r0 - 1) + 1)) / 2 ^ (m - s))
      ≤ 60 * Real.exp ((m : ℝ) ^ ((3 : ℝ) / 8)) * (2 : ℝ) ^ X +
          m * (2 * Real.exp ((m : ℝ) ^ ((3 : ℝ) / 8))) * (2 : ℝ) ^ X := add_le_add hT1 hT2
    _ ≤ Ybound m := by
        unfold Ybound
        rw [← hX]
        nlinarith [mul_nonneg hE hX2]

theorem exp_one_le_272 : Real.exp 1 ≤ 2.72 := by
  have h := Real.exp_bound (x := 1) (by norm_num) (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, one_pow, abs_one, Nat.factorial] at h
  norm_num at h
  have := (abs_le.1 h).2
  linarith

theorem rate_le : (8 / 7 : ℝ) * (7 : ℝ) ^ ((1 : ℝ) / 8) * (2 : ℝ) ^ (-(3 / 4 : ℝ)) *
    Real.exp (1 / 8) ≤ 0.99 := by
  have hx : 0 ≤ (8 / 7 : ℝ) * (7 : ℝ) ^ ((1 : ℝ) / 8) * (2 : ℝ) ^ (-(3 / 4 : ℝ)) * Real.exp (1 / 8) := by
    positivity
  rw [← pow_le_pow_iff_left₀ hx (by norm_num) (by norm_num : (8 : ℕ) ≠ 0)]
  have h7 : ((7 : ℝ) ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) = 7 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h2 : ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ (8 : ℕ) = 1 / 64 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show (-(3 / 4 : ℝ)) * ((8 : ℕ) : ℝ) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    norm_num
  have he : (Real.exp (1 / 8)) ^ (8 : ℕ) = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [mul_pow, mul_pow, mul_pow, h7, h2, he]
  have := exp_one_le_272
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  nlinarith

theorem eventually_total_le :
    ∀ᶠ m : ℕ in atTop, (Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) + 1) * m *
      ((8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8)) * Ybound m ≤ Real.exp (-(m : ℝ) / 8) := by
  set r : ℝ := 0.995 with hr
  have hF6 : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ 2 * r ^ m < 1 / 256 :=
    (tendsto_order.1 (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
      (by rw [hr]; norm_num : |r| < 1))).2 _ (by norm_num)
  have hF7 : ∀ᶠ m : ℕ in atTop, ((m : ℝ)) ^ (-(1 / 4 : ℝ)) < 1 / 1000 :=
    (tendsto_order.1 ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop)).2 _ (by norm_num)
  filter_upwards [hF6, hF7, eventually_ge_atTop 1] with m h6 h7 hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set u : ℝ := (m : ℝ) ^ ((3 : ℝ) / 4) with hu
  clear_value u r
  have hu0 : 0 ≤ u := by rw [hu]; exact Real.rpow_nonneg hm0.le _
  have h18 : (m : ℝ) ^ ((1 : ℝ) / 8) ≤ u := by
    rw [hu]; exact Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have h38 : (m : ℝ) ^ ((3 : ℝ) / 8) ≤ u := by
    rw [hu]; exact Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hu5 : 5 * u ≤ (m : ℝ) / 200 := by
    have : u = (m : ℝ) * (m : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [hu, show (3 : ℝ) / 4 = 1 + (-(1 / 4 : ℝ)) by norm_num, Real.rpow_add hm0, Real.rpow_one]
    rw [this]
    nlinarith
  have hlogr : Real.log r ≤ -1 / 200 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < r by rw [hr]; norm_num)
    rw [hr] at this ⊢
    linarith
  have hr0 : 0 < r := by rw [hr]; norm_num
  have hrm : r ^ m = Real.exp (m * Real.log r) := by
    rw [← Real.exp_log (pow_pos hr0 m), Real.log_pow]
  have hF7' : Real.exp (5 * u) * r ^ m ≤ 1 := by
    rw [hrm, ← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_le_exp.2
    have h1 : (m : ℝ) * Real.log r ≤ (m : ℝ) * (-1 / 200) := mul_le_mul_of_nonneg_left hlogr hm0.le
    linarith
  have hF6' : 4 * (m : ℝ) * (60 + 4 * m) * r ^ m ≤ 1 := by
    have hrpos : 0 < r ^ m := pow_pos hr0 m
    have h1 : 4 * (m : ℝ) * (60 + 4 * m) ≤ 256 * (m : ℝ) ^ 2 := by nlinarith
    calc 4 * (m : ℝ) * (60 + 4 * m) * r ^ m ≤ 256 * (m : ℝ) ^ 2 * r ^ m :=
          mul_le_mul_of_nonneg_right h1 hrpos.le
      _ = 256 * ((m : ℝ) ^ 2 * r ^ m) := by ring
      _ ≤ 256 * (1 / 256) := by linarith
      _ = 1 := by norm_num
  set q : ℝ := (8 / 7 : ℝ) * (7 : ℝ) ^ ((1 : ℝ) / 8) * (2 : ℝ) ^ (-(3 / 4 : ℝ)) with hq
  have hq0 : 0 ≤ q := by positivity
  have hqm : (8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8) * (2 : ℝ) ^ (-(3 * (m : ℝ) / 4)) = q ^ m := by
    rw [hq, mul_pow, mul_pow, ← Real.rpow_natCast ((7 : ℝ) ^ ((1 : ℝ) / 8)),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-(3 / 4 : ℝ))),
      ← Real.rpow_mul (by norm_num)]
    congr 2 <;> ring_nf
  have hqe : q ≤ 0.99 * Real.exp (-(1 / 8)) := by
    have := rate_le
    rw [← hq] at this
    have he : Real.exp (-(1 / 8)) * Real.exp (1 / 8) = 1 := by rw [← Real.exp_add]; norm_num
    have hpos : 0 < Real.exp (1 / 8) := Real.exp_pos _
    nlinarith
  have hqm' : q ^ m ≤ r ^ m * r ^ m * Real.exp (-(m : ℝ) / 8) := by
    have h1 : q ^ m ≤ (0.99 * Real.exp (-(1 / 8))) ^ m := pow_le_pow_left₀ hq0 hqe m
    have h2 : (0.99 * Real.exp (-(1 / 8)) : ℝ) ^ m = (0.99 : ℝ) ^ m * Real.exp (-(m : ℝ) / 8) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    have h3 : (0.99 : ℝ) ^ m ≤ r ^ m * r ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by norm_num) (by rw [hr]; norm_num) m
    rw [h2] at h1
    have he : 0 ≤ Real.exp (-(m : ℝ) / 8) := (Real.exp_pos _).le
    nlinarith
  have h2X : (2 : ℝ) ^ (3 * u + 1 - 3 * (m : ℝ) / 4) ≤
      2 * Real.exp (3 * u) * (2 : ℝ) ^ (-(3 * (m : ℝ) / 4)) := by
    rw [show 3 * u + 1 - 3 * (m : ℝ) / 4 = 3 * u + 1 + (-(3 * (m : ℝ) / 4)) by ring,
      Real.rpow_add two_pos, Real.rpow_add two_pos, Real.rpow_one]
    have h3u : (2 : ℝ) ^ (3 * u) ≤ Real.exp (3 * u) := by
      rw [Real.rpow_def_of_pos two_pos]
      apply Real.exp_le_exp.2
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      nlinarith
    have hpos : 0 ≤ (2 : ℝ) ^ (-(3 * (m : ℝ) / 4)) := (Real.rpow_pos_of_pos two_pos _).le
    nlinarith
  have hA : Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) + 1 ≤ 2 * Real.exp u := by
    have h1 : Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) ≤ Real.exp u := Real.exp_le_exp.2 h18
    have h2 : 1 ≤ Real.exp u := Real.one_le_exp hu0
    linarith
  have hB : Real.exp ((m : ℝ) ^ ((3 : ℝ) / 8)) ≤ Real.exp u := Real.exp_le_exp.2 h38
  have hexp5 : Real.exp u * Real.exp u * Real.exp (3 * u) = Real.exp (5 * u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hpos1 : 0 ≤ (8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8) := by positivity
  have hpos2 : 0 ≤ Real.exp ((m : ℝ) ^ ((3 : ℝ) / 8)) := (Real.exp_pos _).le
  have hpos3 : 0 ≤ (2 : ℝ) ^ (3 * u + 1 - 3 * (m : ℝ) / 4) := (Real.rpow_pos_of_pos two_pos _).le
  have hpos4 : (0 : ℝ) ≤ 60 + 4 * m := by positivity
  calc (Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) + 1) * m * ((8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8)) *
        Ybound m
      = (Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) + 1) * m * ((8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8)) *
          ((60 + 4 * m) * Real.exp ((m : ℝ) ^ ((3 : ℝ) / 8)) *
            (2 : ℝ) ^ (3 * u + 1 - 3 * (m : ℝ) / 4)) := by rw [Ybound, hu]
    _ ≤ (2 * Real.exp u) * m * ((8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8)) *
          ((60 + 4 * m) * Real.exp u *
            (2 * Real.exp (3 * u) * (2 : ℝ) ^ (-(3 * (m : ℝ) / 4)))) := by
        gcongr
    _ = 4 * m * (60 + 4 * m) * (Real.exp u * Real.exp u * Real.exp (3 * u)) *
          ((8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8) * (2 : ℝ) ^ (-(3 * (m : ℝ) / 4))) := by ring
    _ = 4 * m * (60 + 4 * m) * Real.exp (5 * u) * q ^ m := by rw [hexp5, hqm]
    _ ≤ 4 * m * (60 + 4 * m) * Real.exp (5 * u) * (r ^ m * r ^ m * Real.exp (-(m : ℝ) / 8)) := by
        gcongr
    _ = (4 * m * (60 + 4 * m) * r ^ m) * (Real.exp (5 * u) * r ^ m) * Real.exp (-(m : ℝ) / 8) := by
        ring
    _ ≤ 1 * 1 * Real.exp (-(m : ℝ) / 8) := by
        gcongr
    _ = Real.exp (-(m : ℝ) / 8) := by ring

end Final

section Main

theorem card_sets_le (m : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    (((Finset.univ : Finset (Fin m)).powerset.filter
      (fun S => 1 ≤ S.card ∧ 4 * (d + 1) * S.card ≤ m)).card : ℝ) ≤
      (8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8) := by
  classical
  have h1 : ((Finset.univ : Finset (Fin m)).powerset.filter
      (fun S => 1 ≤ S.card ∧ 4 * (d + 1) * S.card ≤ m)).card ≤
      ((Finset.univ : Finset (Fin m)).powerset.filter (fun S => 8 * S.card ≤ m)).card := by
    apply Finset.card_le_card
    intro S hS
    simp only [Finset.mem_filter] at hS ⊢
    refine ⟨hS.1, ?_⟩
    nlinarith [hS.2.2]
  have h2nat : ((Finset.univ : Finset (Fin m)).powerset.filter (fun S => 8 * S.card ≤ m)).card =
      ∑ k ∈ (Finset.range (m + 1)).filter (fun k => 8 * k ≤ m), m.choose k := by
    rw [Finset.card_filter, Finset.sum_filter]
    have := Finset.sum_powerset_apply_card (fun k => if 8 * k ≤ m then (1 : ℕ) else 0)
      (x := (Finset.univ : Finset (Fin m)))
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [this]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have h2 : (((Finset.univ : Finset (Fin m)).powerset.filter (fun S => 8 * S.card ≤ m)).card : ℝ) =
      ∑ k ∈ (Finset.range (m + 1)).filter (fun k => 8 * k ≤ m), (m.choose k : ℝ) := by
    rw [h2nat]
    push_cast
    rfl
  calc (((Finset.univ : Finset (Fin m)).powerset.filter
        (fun S => 1 ≤ S.card ∧ 4 * (d + 1) * S.card ≤ m)).card : ℝ)
      ≤ (((Finset.univ : Finset (Fin m)).powerset.filter (fun S => 8 * S.card ≤ m)).card : ℝ) := by
        exact_mod_cast h1
    _ = _ := h2
    _ ≤ _ := sum_choose_le m

theorem lem_suppd (a b : ℤ) :
    ∀ᶠ m : ℕ in atTop, prob (fun ω : Pairs m → Bool => ¬ ∀ p : ℕ, p.Prime →
      (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) → ¬ (p : ℤ) ∣ a - b →
      ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) →
      ∀ g : (ZMod p)[X], g.Monic → g.natDegree = d →
      ∀ y : Fin m → ZMod p, y ≠ 0 → aeval (modP p (symOf a b ω)) g *ᵥ y = 0 →
        (m : ℝ) / (4 * (d + 1)) < ((Finset.univ.filter fun i => y i ≠ 0).card : ℝ)) ≤
      Real.exp (-(m : ℝ) / 8) := by
  filter_upwards [eventually_total_le, eventually_ge_atTop 1] with m hm hm1
  classical
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  set B := ⌊Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))⌋₊ with hB
  set Pset := (Finset.range (B + 1)).filter (fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a - b) with hPset
  set Dset := Finset.Icc 1 ⌊(m : ℝ) ^ ((1 : ℝ) / 4)⌋₊ with hDset
  set Sset : ℕ → Finset (Finset (Fin m)) := fun d =>
    (Finset.univ : Finset (Fin m)).powerset.filter
      (fun S => 1 ≤ S.card ∧ 4 * (d + 1) * S.card ≤ m) with hSset
  have hsub : ∀ ω : Pairs m → Bool, (¬ ∀ p : ℕ, p.Prime →
      (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) → ¬ (p : ℤ) ∣ a - b →
      ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) →
      ∀ g : (ZMod p)[X], g.Monic → g.natDegree = d →
      ∀ y : Fin m → ZMod p, y ≠ 0 → aeval (modP p (symOf a b ω)) g *ᵥ y = 0 →
        (m : ℝ) / (4 * (d + 1)) < ((Finset.univ.filter fun i => y i ≠ 0).card : ℝ)) →
      ∃ p ∈ Pset, ∃ d ∈ Dset, ∃ S ∈ Sset d, BadS p a b d S ω := by
    intro ω hω
    push Not at hω
    obtain ⟨p, hp, hpB, hpab, d, hd1, hdm, g, hgm, hgd, y, hy0, hgy, hsupp⟩ := hω
    refine ⟨p, ?_, d, ?_, Finset.univ.filter (fun i => y i ≠ 0), ?_,
      g, hgm, hgd, y, hy0, fun i hi => by simpa using hi, hgy⟩
    · rw [hPset, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpB), hp, hpab⟩
    · rw [hDset, Finset.mem_Icc]
      exact ⟨hd1, Nat.le_floor hdm⟩
    · simp only [hSset, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      constructor
      · obtain ⟨i, hi⟩ := Function.ne_iff.1 hy0
        exact Finset.card_pos.2 ⟨i, by simpa using hi⟩
      · have h4 : (0 : ℝ) < 4 * (d + 1) := by positivity
        rw [le_div_iff₀ h4] at hsupp
        have : ((4 * (d + 1) * (Finset.univ.filter fun i => y i ≠ 0).card : ℕ) : ℝ) ≤ m := by
          push_cast
          linarith
        exact_mod_cast this
  have hY0 : 0 ≤ Ybound m := by unfold Ybound; positivity
  have hcount : ∀ d ∈ Dset, (Sset d).card * Ybound m ≤
      ((8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8)) * Ybound m := by
    intro d hd
    rw [hDset, Finset.mem_Icc] at hd
    exact mul_le_mul_of_nonneg_right (card_sets_le m hd.1) hY0
  have hDcard : (Dset.card : ℝ) ≤ m := by
    rw [hDset, Nat.card_Icc, Nat.add_sub_cancel]
    have h1 : (⌊(m : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) :=
      Nat.floor_le (Real.rpow_nonneg (by linarith) _)
    have h2 : (m : ℝ) ^ ((1 : ℝ) / 4) ≤ (m : ℝ) := by
      calc (m : ℝ) ^ ((1 : ℝ) / 4) ≤ (m : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hm1' (by norm_num)
        _ = m := Real.rpow_one _
    linarith
  have hPcard : (Pset.card : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) + 1 := by
    have h1 : Pset.card ≤ B + 1 := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    have h2 : (B : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) := Nat.floor_le (Real.exp_pos _).le
    have h3 : (Pset.card : ℝ) ≤ B + 1 := by exact_mod_cast h1
    linarith
  have hbound : ∀ p ∈ Pset, ∀ d ∈ Dset, ∀ S ∈ Sset d, prob (BadS p a b d S) ≤ Ybound m := by
    intro p hp d hd S hS
    rw [hPset, Finset.mem_filter, Finset.mem_range] at hp
    rw [hDset, Finset.mem_Icc] at hd
    simp only [hSset, Finset.mem_filter] at hS
    have : Fact p.Prime := ⟨hp.2.1⟩
    have hab : (a : ZMod p) ≠ (b : ZMod p) := by
      intro h
      apply hp.2.2
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, h, sub_self]
    have hpe : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) := by
      have h1 : p ≤ B := Nat.lt_succ_iff.1 hp.1
      have h2 : (B : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) := Nat.floor_le (Real.exp_pos _).le
      have h3 : (p : ℝ) ≤ B := by exact_mod_cast h1
      linarith
    have hdm : (d : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := by
      have h1 : (d : ℝ) ≤ ⌊(m : ℝ) ^ ((1 : ℝ) / 4)⌋₊ := by exact_mod_cast hd.2
      exact h1.trans (Nat.floor_le (Real.rpow_nonneg (by linarith) _))
    exact prob_badS_le_Y hab hm1 hd.1 hdm hpe S hS.2.1 hS.2.2
  calc prob (fun ω : Pairs m → Bool => ¬ ∀ p : ℕ, p.Prime →
        (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) → ¬ (p : ℤ) ∣ a - b →
        ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) →
        ∀ g : (ZMod p)[X], g.Monic → g.natDegree = d →
        ∀ y : Fin m → ZMod p, y ≠ 0 → aeval (modP p (symOf a b ω)) g *ᵥ y = 0 →
          (m : ℝ) / (4 * (d + 1)) < ((Finset.univ.filter fun i => y i ≠ 0).card : ℝ))
      ≤ prob (fun ω : Pairs m → Bool => ∃ p ∈ Pset, ∃ d ∈ Dset, ∃ S ∈ Sset d, BadS p a b d S ω) :=
        prob_mono hsub
    _ ≤ ∑ p ∈ Pset, ∑ d ∈ Dset, ∑ S ∈ Sset d, prob (BadS p a b d S) := by
        refine (prob_exists_le_sum _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        refine (prob_exists_le_sum _ _).trans (Finset.sum_le_sum fun d _ => ?_)
        exact prob_exists_le_sum _ _
    _ ≤ ∑ p ∈ Pset, ∑ d ∈ Dset, ∑ _S ∈ Sset d, Ybound m :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun S hS =>
          hbound p hp d hd S hS
    _ = ∑ p ∈ Pset, ∑ d ∈ Dset, (Sset d).card * Ybound m := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _p ∈ Pset, ∑ _d ∈ Dset, ((8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8)) * Ybound m :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun d hd => hcount d hd
    _ = Pset.card * (Dset.card * (((8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8)) * Ybound m)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) + 1) *
          (m * (((8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8)) * Ybound m)) := by
        gcongr
    _ = (Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) + 1) * m *
          ((8 / 7 : ℝ) ^ m * (7 : ℝ) ^ ((m : ℝ) / 8)) * Ybound m := by ring
    _ ≤ Real.exp (-(m : ℝ) / 8) := hm

end Main

end DGS
