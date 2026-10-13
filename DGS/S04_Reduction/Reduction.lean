module

public import DGS.S04_Reduction.Support
public import DGS.S04_Reduction.Exch
public import DGS.S03_Prelim.SimpleSubmodules
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

open Matrix Polynomial Module Filter Topology
open scoped ENNReal

namespace DGS

section Weights

variable {m : ℕ}

noncomputable def probPerp (p : ℕ) (U : Submodule (ZMod p) (Fin m → ZMod p)) : ℝ :=
  prob (fun ξ : Fin m → Bool => ∀ u ∈ U, modPVec p (signVec ξ) ⬝ᵥ u = 0)

noncomputable def abeta (p : ℕ) (T : Matrix (Fin m) (Fin m) ℤ) (β : (ZMod p)[X]) : ℝ :=
  sSup {x : ℝ | ∃ U, IsSimpleInvariant (modP p T) U ∧ HasType (modP p T) U β ∧ x = probPerp p U}

theorem abeta_nonneg (p : ℕ) (T : Matrix (Fin m) (Fin m) ℤ) (β : (ZMod p)[X]) : 0 ≤ abeta p T β :=
  Real.sSup_nonneg (by rintro x ⟨U, -, -, rfl⟩; exact prob_nonneg _)

theorem probPerp_le_abeta {p : ℕ} {T : Matrix (Fin m) (Fin m) ℤ} {β : (ZMod p)[X]}
    {U : Submodule (ZMod p) (Fin m → ZMod p)} (hU : IsSimpleInvariant (modP p T) U)
    (hβ : HasType (modP p T) U β) : probPerp p U ≤ abeta p T β :=
  le_csSup ⟨1, by rintro x ⟨U, -, -, rfl⟩; exact prob_le_one _⟩ ⟨U, hU, hβ, rfl⟩

theorem modPVec_signVec (p : ℕ) (ξ : Fin m → Bool) :
    modPVec p (signVec ξ) = twoValued (1 : ZMod p) (-1) ξ := by
  funext i
  simp only [modPVec, signVec, twoValued]
  split_ifs <;> simp

theorem abeta_le {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (T : Matrix (Fin m) (Fin m) ℤ)
    (β : (ZMod p)[X]) : abeta p T β ≤ (2 : ℝ)⁻¹ ^ β.natDegree := by
  refine Real.sSup_le ?_ (by positivity)
  rintro x ⟨U, hU, hβ, rfl⟩
  obtain ⟨β', hβ', hdim⟩ := exists_hasType _ U hU
  rw [hasType_unique _ U hU hβ' hβ] at hdim
  have h := lem_odlyzko_perp (1 : ZMod p) (-1) (one_ne_neg_one_zmod hp) U
  rw [hdim] at h
  refine le_trans (le_of_eq ?_) h
  unfold probPerp
  congr 1
  funext ξ
  rw [modPVec_signVec]

open Classical in
noncomputable def NPi (PS : Set (ℕ × ℕ)) (T : Matrix (Fin m) (Fin m) ℤ) : ℝ≥0∞ :=
  ∑' x : (Σ p : ℕ, (ZMod p)[X]),
    if (x.1, x.2.natDegree) ∈ PS ∧ IsRepeatedFactor x.1 T x.2 then ENNReal.ofReal (abeta x.1 T x.2)
    else 0

open Classical in
noncomputable def expectNPi (PS : Set (ℕ × ℕ)) (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℤ)) : ℝ≥0∞ :=
  (∑ ω : Pairs m → Bool, if seidelOf ω ∈ G then NPi PS (seidelOf ω) else 0) /
    (Fintype.card (Pairs m → Bool) : ℝ≥0∞)

end Weights

section ENNProb

theorem ofReal_prob_exists_le_tsum {Ω ι : Type*} [Fintype Ω] (A : ι → Ω → Prop) :
    ENNReal.ofReal (prob (fun ω => ∃ i, A i ω)) ≤ ∑' i, ENNReal.ofReal (prob (A i)) := by
  classical
  let s : Finset ι := (Finset.univ.filter fun ω => ∃ i, A i ω).attach.image
    (fun ω => (Finset.mem_filter.1 ω.2).2.choose)
  have hcover : ∀ ω, (∃ i, A i ω) → ∃ i ∈ s, A i ω := by
    intro ω hω
    have hmem : ω ∈ Finset.univ.filter fun ω => ∃ i, A i ω := Finset.mem_filter.2 ⟨Finset.mem_univ _, hω⟩
    refine ⟨(Finset.mem_filter.1 hmem).2.choose, Finset.mem_image.2 ⟨⟨ω, hmem⟩, Finset.mem_attach _ _, rfl⟩,
      (Finset.mem_filter.1 hmem).2.choose_spec⟩
  calc ENNReal.ofReal (prob (fun ω => ∃ i, A i ω))
      ≤ ENNReal.ofReal (∑ i ∈ s, prob (A i)) :=
        ENNReal.ofReal_le_ofReal ((prob_mono hcover).trans (prob_exists_le_sum s A))
    _ = ∑ i ∈ s, ENNReal.ofReal (prob (A i)) :=
        ENNReal.ofReal_sum_of_nonneg fun i _ => prob_nonneg _
    _ ≤ ∑' i, ENNReal.ofReal (prob (A i)) := ENNReal.sum_le_tsum s

theorem ofReal_prob_eq {Ω : Type*} [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) [DecidablePred P] :
    ENNReal.ofReal (prob P) = (∑ ω, if P ω then (1 : ℝ≥0∞) else 0) / (Fintype.card Ω : ℝ≥0∞) := by
  rw [← expect_indicator P, expect]
  have hpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_sum_of_nonneg (fun ω _ => by split_ifs <;> norm_num),
    ENNReal.ofReal_natCast]
  congr 1
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs <;> simp

theorem ofReal_prob_prod_le {Ω Ω' : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Ω'] (P : Ω × Ω' → Prop)
    (f : Ω → ℝ≥0∞) (hf : ∀ ω, ENNReal.ofReal (prob (fun ω' => P (ω, ω'))) ≤ f ω) :
    ENNReal.ofReal (prob P) ≤ (∑ ω, f ω) / (Fintype.card Ω : ℝ≥0∞) := by
  rw [prob_prod_eq_avg P]
  have hpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_sum_of_nonneg (fun ω _ => prob_nonneg _),
    ENNReal.ofReal_natCast]
  exact ENNReal.div_le_div_right (Finset.sum_le_sum fun ω _ => hf ω) _

end ENNProb

section Algebra

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

theorem modP_map_algebraMap (p : ℕ) {L : Type*} [Field L] [Algebra (ZMod p) L]
    (S : Matrix (Fin m) (Fin m) ℤ) :
    (modP p S).map (algebraMap (ZMod p) L) = S.map (Int.castRingHom L) := by
  ext i j
  simp [modP]

theorem exists_ne_zero_of_finrank_pos {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    {K : Submodule L V} (h : 0 < finrank L K) : ∃ w ∈ K, w ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot (fun hb => by rw [hb, finrank_bot] at h; exact lt_irrefl 0 h)

theorem one_le_of_disj {g : ℕ} {P : Prop} (h : 2 ≤ g ∨ (g = 1 ∧ P)) : 1 ≤ g := by
  rcases h with h | h
  · omega
  · exact h.1.ge

theorem exists_simple_of_repeated {T : Matrix (Fin m) (Fin m) ℤ} (hT : T.IsSymm)
    {β : (ZMod p)[X]} (hβ : IsRepeatedFactor p T β) :
    ∃ U, IsSimpleInvariant (modP p T) U ∧ HasType (modP p T) U β := by
  have : Fact (Irreducible β) := ⟨hβ.2.1⟩
  have : Module.Finite (ZMod p) (AdjoinRoot β) := (AdjoinRoot.powerBasis hβ.1.ne_zero).finite
  have : Finite (AdjoinRoot β) := finite_adjoinRoot hβ.1.ne_zero
  have h := isGenRoot_adjoinRoot hβ.1
  have hM := modP_isSymm p hT
  have hg := one_le_of_disj ((lem_simple_d h hM).2.1 ((lem_simple_d h hM).1.1 hβ.2.2))
  obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_finrank_pos hg
  exact ⟨_, ((lem_simple_a h (modP p T)).1 w hw hw0).1, ((lem_simple_a h (modP p T)).1 w hw hw0).2.1⟩

def FewIso (p : ℕ) (T : Matrix (Fin m) (Fin m) ℤ) (β : (ZMod p)[X]) : Prop :=
  ∃ 𝒰 : Finset (Submodule (ZMod p) (Fin m → ZMod p)), 𝒰.card ≤ 2 ∧
    ∀ U, IsSimpleInvariant (modP p T) U → HasType (modP p T) U β → IsTotallyIsotropic U → U ∈ 𝒰

theorem fewIso_of_finrank {T : Matrix (Fin m) (Fin m) ℤ} (hT : T.IsSymm) {β : (ZMod p)[X]}
    [Fact (Irreducible β)] (hβm : β.Monic)
    (hK : finrank (AdjoinRoot β) (eigsp (modP p T) (AdjoinRoot.root β)) = 1 ∨
      (finrank (AdjoinRoot β) (eigsp (modP p T) (AdjoinRoot.root β)) = 2 ∧
        ∃ w ∈ eigsp (modP p T) (AdjoinRoot.root β), w ⬝ᵥ w ≠ 0)) :
    FewIso p T β := by
  classical
  have : Module.Finite (ZMod p) (AdjoinRoot β) := (AdjoinRoot.powerBasis hβm.ne_zero).finite
  have : Finite (AdjoinRoot β) := finite_adjoinRoot hβm.ne_zero
  have h := isGenRoot_adjoinRoot hβm
  have hM := modP_isSymm p hT
  rcases hK with h1 | ⟨h2, w1, hw1, hq1⟩
  ·
    obtain ⟨w0, hw0, hw00⟩ := exists_ne_zero_of_finrank_pos (h1.symm ▸ Nat.one_pos)
    refine ⟨{Uw (ZMod p) w0}, by simp, fun U hU hβ _ => ?_⟩
    obtain ⟨w, hw, hw0', rfl⟩ := eq_Uw_of_hasType h hU hβ
    rw [Finset.mem_singleton]
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (⟨w0, hw0⟩ : eigsp (modP p T) (AdjoinRoot.root β))
      (fun h0 => hw00 (congrArg Subtype.val h0))).1 h1 ⟨w, hw⟩
    exact ((Uw_eq_Uw_iff h hw0 hw hw0').2 ⟨c, (congrArg Subtype.val hc).symm⟩).symm
  ·
    have hw10 : w1 ≠ 0 := by
      rintro rfl
      exact hq1 (dotProduct_zero _)
    have hK' := finrank_inf_perp_add_one (K := eigsp (modP p T) (AdjoinRoot.root β)) (y := w1) hw1 hq1
    rw [h2] at hK'
    have hK'1 : finrank (AdjoinRoot β)
        ↥(eigsp (modP p T) (AdjoinRoot.root β) ⊓ LinearMap.ker (dotProductLin w1)) = 1 := by omega
    obtain ⟨⟨w2, hw2mem⟩, hw2ne, hw2⟩ := finrank_eq_one_iff'.1 hK'1
    have hw2K : w2 ∈ eigsp (modP p T) (AdjoinRoot.root β) := (Submodule.mem_inf.1 hw2mem).1
    have hw2perp' : w1 ⬝ᵥ w2 = 0 := (Submodule.mem_inf.1 hw2mem).2
    have hdecomp : ∀ w ∈ eigsp (modP p T) (AdjoinRoot.root β), ∃ a c : AdjoinRoot β,
        w = a • w1 + c • w2 := by
      intro w hw
      have hmem : w - ((w1 ⬝ᵥ w) / (w1 ⬝ᵥ w1)) • w1 ∈
          eigsp (modP p T) (AdjoinRoot.root β) ⊓ LinearMap.ker (dotProductLin w1) := by
        refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hw (Submodule.smul_mem _ _ hw1), ?_⟩
        show w1 ⬝ᵥ (w - ((w1 ⬝ᵥ w) / (w1 ⬝ᵥ w1)) • w1) = 0
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hq1, sub_self]
      obtain ⟨c, hc⟩ := hw2 ⟨_, hmem⟩
      set a := (w1 ⬝ᵥ w) / (w1 ⬝ᵥ w1)
      refine ⟨a, c, ?_⟩
      have := congrArg Subtype.val hc
      simp only [SetLike.val_smul] at this
      rw [this]
      abel
    set q1 := w1 ⬝ᵥ w1
    set q2 := w2 ⬝ᵥ w2
    set f : (AdjoinRoot β)[X] := C q1 * X ^ 2 + C q2
    have hf0 : f ≠ 0 := by
      intro h0
      have := congrArg (fun g : (AdjoinRoot β)[X] => g.coeff 2) h0
      simp [f] at this
      exact hq1 this
    have hfeval : ∀ t : AdjoinRoot β, f.eval t = (t • w1 + w2) ⬝ᵥ (t • w1 + w2) := by
      intro t
      have hsymm : w2 ⬝ᵥ w1 = 0 := by rw [dotProduct_comm]; exact hw2perp'
      simp only [f, eval_add, eval_mul, eval_C, eval_pow, eval_X, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hw2perp', hsymm]
      ring
    refine ⟨f.roots.toFinset.image (fun t => Uw (ZMod p) (t • w1 + w2)), ?_, fun U hU hβ hiso => ?_⟩
    · calc (f.roots.toFinset.image (fun t => Uw (ZMod p) (t • w1 + w2))).card
          ≤ f.roots.toFinset.card := Finset.card_image_le
        _ ≤ f.roots.card := Multiset.toFinset_card_le _
        _ ≤ f.natDegree := card_roots' f
        _ ≤ 2 := by
            have : f.natDegree ≤ 2 := by
              have h1 := natDegree_quadratic_le (a := q1) (b := (0 : AdjoinRoot β)) (c := q2)
              simpa [f] using h1
            exact this
    · obtain ⟨w, hw, hw0, rfl⟩ := eq_Uw_of_hasType h hU hβ
      have hww : w ⬝ᵥ w = 0 := (Uw_isTotallyIsotropic_iff h hM hw).1 hiso
      obtain ⟨a, c, rfl⟩ := hdecomp w hw
      have hc0 : c ≠ 0 := by
        rintro rfl
        have : a • w1 ⬝ᵥ a • w1 = a * a * q1 := by
          simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
        rw [zero_smul, add_zero, this] at hww
        have ha : a = 0 := by
          rcases mul_eq_zero.1 hww with h0 | h0
          · exact mul_self_eq_zero.1 h0
          · exact absurd h0 hq1
        exact hw0 (by rw [ha, zero_smul, zero_smul, add_zero])
      set t := a / c
      have hwt : a • w1 + c • w2 = c • (t • w1 + w2) := by
        rw [smul_add, smul_smul, mul_div_cancel₀ _ hc0]
      have htK : t • w1 + w2 ∈ eigsp (modP p T) (AdjoinRoot.root β) :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ hw1) hw2K
      have ht0 : t • w1 + w2 ≠ 0 := by
        intro h0
        apply hw0
        rw [hwt, h0, smul_zero]
      have hroot : t ∈ f.roots.toFinset := by
        rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, hfeval]
        have : (a • w1 + c • w2) ⬝ᵥ (a • w1 + c • w2) = c * c * ((t • w1 + w2) ⬝ᵥ (t • w1 + w2)) := by
          rw [hwt, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
        rw [this] at hww
        exact (mul_eq_zero.1 hww).resolve_left (mul_ne_zero hc0 hc0)
      refine Finset.mem_image.2 ⟨t, hroot, ?_⟩
      exact (Uw_eq_Uw_iff h htK hw hw0).2 ⟨c, hwt⟩

theorem prob_fewIso_le {S : Matrix (Fin m) (Fin m) ℤ} {β : (ZMod p)[X]} (hfew : FewIso p S β) :
    prob (fun b : Fin m → Bool => ∃ U, IsSimpleInvariant (modP p S) U ∧ HasType (modP p S) U β ∧
      IsTotallyIsotropic U ∧ ∀ y ∈ U, modPVec p (signVec b) ⬝ᵥ y = 0) ≤ 2 * abeta p S β := by
  classical
  obtain ⟨𝒰, hcard, hcover⟩ := hfew
  have hsub : ∀ b : Fin m → Bool, (∃ U, IsSimpleInvariant (modP p S) U ∧ HasType (modP p S) U β ∧
      IsTotallyIsotropic U ∧ ∀ y ∈ U, modPVec p (signVec b) ⬝ᵥ y = 0) →
      ∃ U ∈ 𝒰, (IsSimpleInvariant (modP p S) U ∧ HasType (modP p S) U β) ∧
        ∀ y ∈ U, modPVec p (signVec b) ⬝ᵥ y = 0 := by
    rintro b ⟨U, hU, hβ, hiso, horth⟩
    exact ⟨U, hcover U hU hβ hiso, ⟨hU, hβ⟩, horth⟩
  have hab := abeta_nonneg p S β
  calc _ ≤ ∑ U ∈ 𝒰, prob (fun b : Fin m → Bool => (IsSimpleInvariant (modP p S) U ∧
          HasType (modP p S) U β) ∧ ∀ y ∈ U, modPVec p (signVec b) ⬝ᵥ y = 0) :=
        (prob_mono hsub).trans (prob_exists_le_sum _ _)
    _ ≤ ∑ _U ∈ 𝒰, abeta p S β := by
        refine Finset.sum_le_sum fun U _ => ?_
        by_cases hU : IsSimpleInvariant (modP p S) U ∧ HasType (modP p S) U β
        · exact (prob_mono fun b hb => hb.2).trans (probPerp_le_abeta hU.1 hU.2)
        · refine le_trans (le_of_eq ?_) hab
          rw [← prob_false (Ω := Fin m → Bool)]
          exact prob_congr fun b => by simp [hU]
    _ = 𝒰.card * abeta p S β := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * abeta p S β := by
        have : (𝒰.card : ℝ) ≤ 2 := by exact_mod_cast hcard
        nlinarith

end Algebra

section Step2

variable {n : ℕ}

theorem delMat_sub_smul_one {F : Type*} [Field F] (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (i : Fin (n + 1)) (μ : F) : delMat (A - μ • 1) i = delMat A i - μ • 1 := by
  ext j k
  simp only [delMat, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Fin.succAbove_right_inj]

theorem delCol_sub_smul_one {F : Type*} [Field F] (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (i : Fin (n + 1)) (μ : F) : delCol (A - μ • 1) i = delCol A i := by
  funext j
  simp [delCol, Fin.succAbove_ne]

theorem mem_ker_sub_iff {F : Type*} [Field F] {k : ℕ} (A : Matrix (Fin k) (Fin k) F) (μ : F)
    (x : Fin k → F) : x ∈ LinearMap.ker (A - μ • 1).mulVecLin ↔ A *ᵥ x = μ • x := by
  rw [mem_ker_mulVecLin, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]

theorem delMat_isSymm {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hT : T.IsSymm) (i : Fin (n + 1)) :
    (delMat T i).IsSymm := by
  rw [Matrix.IsSymm, delMat_transpose, hT.eq]

open Classical in
theorem many_deletions {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hS : S.IsSymm)
    (hgood : SuppGood S) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {β : (ZMod p)[X]}
    (hβ : IsRepeatedFactor p S β) (hfew : ¬ FewIso p S β) :
    ((n + 1 : ℕ) : ℝ) / 20 < ((Finset.univ.filter fun i => IsRepeatedFactor p (delMat S i) β ∧
      ∀ v, aeval (modP p (delMat S i)) β *ᵥ v = 0 → modPVec p (delCol S i) ⬝ᵥ v = 0).card : ℝ) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Irreducible β) := ⟨hβ.2.1⟩
  have : Module.Finite (ZMod p) (AdjoinRoot β) := (AdjoinRoot.powerBasis hβ.1.ne_zero).finite
  have : Finite (AdjoinRoot β) := finite_adjoinRoot hβ.1.ne_zero
  have h := isGenRoot_adjoinRoot hβ.1
  have hM := modP_isSymm p hS
  have hg := one_le_of_disj ((lem_simple_d h hM).2.1 ((lem_simple_d h hM).1.1 hβ.2.2))
  have hcase : 3 ≤ finrank (AdjoinRoot β) (eigsp (modP p S) (AdjoinRoot.root β)) ∨
      (finrank (AdjoinRoot β) (eigsp (modP p S) (AdjoinRoot.root β)) = 2 ∧
        ∀ w ∈ eigsp (modP p S) (AdjoinRoot.root β), w ⬝ᵥ w = 0) := by
    by_contra hc
    push Not at hc
    apply hfew
    apply fewIso_of_finrank hS hβ.1
    by_cases h1 : finrank (AdjoinRoot β) (eigsp (modP p S) (AdjoinRoot.root β)) = 1
    · exact Or.inl h1
    · right
      have h2 : finrank (AdjoinRoot β) (eigsp (modP p S) (AdjoinRoot.root β)) = 2 := by omega
      exact ⟨h2, hc.2 h2⟩
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) (AdjoinRoot β) :=
    S.map (Int.castRingHom (AdjoinRoot β)) - AdjoinRoot.root β • 1 with hBdef
  have hSL : (modP p S).map (algebraMap (ZMod p) (AdjoinRoot β)) =
      S.map (Int.castRingHom (AdjoinRoot β)) := modP_map_algebraMap p S
  have hBsymm : Bᵀ = B := by
    rw [hBdef, transpose_sub, transpose_smul, transpose_one, ← transpose_map, hS.eq]
  have hkerB : ∀ x, x ∈ LinearMap.ker B.mulVecLin ↔ x ∈ eigsp (modP p S) (AdjoinRoot.root β) := by
    intro x
    rw [hBdef, mem_ker_sub_iff, mem_eigsp, hSL]
  have hkerB' : LinearMap.ker B.mulVecLin = eigsp (modP p S) (AdjoinRoot.root β) := by
    ext x
    exact hkerB x
  set I := Finset.univ.filter fun i => ∃ w ∈ eigsp (modP p S) (AdjoinRoot.root β), w i ≠ 0 with hIdef
  have hIcard : ((n + 1 : ℕ) : ℝ) / 20 < (I.card : ℝ) := by
    obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_finrank_pos (K := eigsp (modP p S) (AdjoinRoot.root β))
      (by omega)
    have hweig : S.map (Int.castRingHom (AdjoinRoot β)) *ᵥ w = AdjoinRoot.root β • w := by
      rw [← hSL]; exact mem_eigsp.1 hw
    refine hgood p hp hp2 (AdjoinRoot β) (AdjoinRoot.root β) w hw0 hweig I fun i hi => ?_
    by_contra hwi
    exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, w, hw, hwi⟩)
  refine lt_of_lt_of_le hIcard ?_
  have hsubset : I ⊆ Finset.univ.filter fun i => IsRepeatedFactor p (delMat S i) β ∧
      ∀ v, aeval (modP p (delMat S i)) β *ᵥ v = 0 → modPVec p (delCol S i) ⬝ᵥ v = 0 := by
    intro i hi
    obtain ⟨w, hw, hwi⟩ := (Finset.mem_filter.1 hi).2
    obtain ⟨hdim, horth, hins⟩ := lem_delete hBsymm i ⟨w, (hkerB w).2 hw, hwi⟩
    have hSLi : (modP p (delMat S i)).map (algebraMap (ZMod p) (AdjoinRoot β)) =
        (delMat S i).map (Int.castRingHom (AdjoinRoot β)) := modP_map_algebraMap p _
    have hdelB : delMat B i =
        (delMat S i).map (Int.castRingHom (AdjoinRoot β)) - AdjoinRoot.root β • 1 := by
      rw [hBdef, delMat_sub_smul_one, delMat_map]
    have hkerBi : ∀ x, x ∈ LinearMap.ker (delMat B i).mulVecLin ↔
        x ∈ eigsp (modP p (delMat S i)) (AdjoinRoot.root β) := by
      intro x
      rw [hdelB, mem_ker_sub_iff, mem_eigsp, hSLi]
    have hkerBi' : LinearMap.ker (delMat B i).mulVecLin =
        eigsp (modP p (delMat S i)) (AdjoinRoot.root β) := by
      ext x
      exact hkerBi x
    have hgi : finrank (AdjoinRoot β) (eigsp (modP p (delMat S i)) (AdjoinRoot.root β)) + 1 =
        finrank (AdjoinRoot β) (eigsp (modP p S) (AdjoinRoot.root β)) := by
      unfold corank at hdim
      rw [hkerBi', hkerB'] at hdim
      exact hdim
    have hMi := modP_isSymm p (delMat_isSymm hS i)
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hβ.1, hβ.2.1, ?_⟩, ?_⟩
    ·
      refine (lem_simple_d h hMi).1.2 ((lem_simple_d h hMi).2.2 ?_)
      rcases hcase with h3 | ⟨h2, hiso⟩
      · exact Or.inl (by omega)
      · refine Or.inr ⟨by omega, fun w' hw' => ?_⟩
        have hmem := (hins (Fin.insertNth i 0 w')).2 ⟨w', (hkerBi w').2 hw', rfl⟩
        have h0 := hiso _ ((hkerB _).1 hmem.1)
        rwa [← insertZero_apply, insertZero_dotProduct] at h0
    ·
      intro v hv
      obtain ⟨w', hw', rfl⟩ := (lem_simple_a_iso h (modP p (delMat S i))).2.2.2 v hv
      have hcol : (liftVec (ZMod p) (modPVec p (delCol S i)) : Fin n → AdjoinRoot β) =
          delCol B i := by
        rw [hBdef, delCol_sub_smul_one]
        funext j
        simp [liftVec, modPVec, delCol]
      have h1 := dotProduct_trVec (K := ZMod p) (modPVec p (delCol S i)) w' 1
      rw [one_smul, one_mul, hcol, horth w' ((hkerBi w').2 hw'), map_zero] at h1
      exact h1
  exact_mod_cast Finset.card_le_card hsubset

end Step2

section Reduction

variable (PS : Set (ℕ × ℕ))

def SwitchedFailure {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (u : Fin N → ℤ) : Prop :=
  ∃ p d : ℕ, (p, d) ∈ PS ∧ ∃ (U : Submodule (ZMod p) (Fin N → ZMod p)) (β : (ZMod p)[X]),
    IsSimpleInvariant (modP p S) U ∧ HasType (modP p S) U β ∧ β.natDegree = d ∧
      IsTotallyIsotropic U ∧ ∀ x ∈ U, modPVec p u ⬝ᵥ x = 0

def PairCond {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (x : Σ p : ℕ, (ZMod p)[X]) : Prop :=
  (x.1, x.2.natDegree) ∈ PS ∧ IsRepeatedFactor x.1 S x.2

def Step1Event {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (u : Fin N → ℤ) (x : Σ p : ℕ, (ZMod p)[X]) :
    Prop :=
  PairCond PS S x ∧ FewIso x.1 S x.2 ∧ ∃ U, IsSimpleInvariant (modP x.1 S) U ∧
    HasType (modP x.1 S) U x.2 ∧ IsTotallyIsotropic U ∧ ∀ y ∈ U, modPVec x.1 u ⬝ᵥ y = 0

def Step2Event {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) : Prop :=
  ∃ x : Σ p : ℕ, (ZMod p)[X], PairCond PS S x ∧ ¬ FewIso x.1 S x.2

def DelEvent {N : ℕ} (T : Matrix (Fin N) (Fin N) ℤ) (s : Fin N → ℤ) : Prop :=
  ∃ x : Σ p : ℕ, (ZMod p)[X], PairCond PS T x ∧
    ∀ v, aeval (modP x.1 T) x.2 *ᵥ v = 0 → modPVec x.1 s ⬝ᵥ v = 0

variable {PS}

theorem probG_eq_switched (hPS : ∀ x ∈ PS, x.1.Prime ∧ x.1 ≠ 2) (N : ℕ) :
    probG N (fun G => ∃ p d : ℕ, (p, d) ∈ PS ∧ E p d G) =
      prob (fun x : (Pairs N → Bool) × (Fin N → Bool) =>
        SwitchedFailure PS (seidelOf x.1) (signVec x.2)) := by
  rw [← lem_switch N (SwitchedFailure PS), probG_eq_prob,
    ← prob_fst (Ω' := Fin N → Bool) (fun G : SimpleGraph (Fin N) => ∃ p d : ℕ, (p, d) ∈ PS ∧ E p d G)]
  refine prob_congr fun x => ?_
  rw [signMat_mulVec_ones]
  unfold SwitchedFailure
  refine exists_congr fun p => exists_congr fun d => ⟨fun ⟨hpd, hE⟩ => ⟨hpd, ?_⟩,
    fun ⟨hpd, hE⟩ => ⟨hpd, ?_⟩⟩
  · have : Fact p.Prime := ⟨(hPS _ hpd).1⟩
    exact ((lem_Epswitch (hPS _ hpd).2 x.1 x.2 d).1).1 hE
  · have : Fact p.Prime := ⟨(hPS _ hpd).1⟩
    exact ((lem_Epswitch (hPS _ hpd).2 x.1 x.2 d).1).2 hE

theorem switchedFailure_cases (hPS : ∀ x ∈ PS, x.1.Prime ∧ x.1 ≠ 2) {N : ℕ}
    {S : Matrix (Fin N) (Fin N) ℤ} (hS : S.IsSymm) {u : Fin N → ℤ}
    (h : SwitchedFailure PS S u) : (∃ x, Step1Event PS S u x) ∨ Step2Event PS S := by
  obtain ⟨p, d, hpd, U, β, hU, hβ, hd, hiso, horth⟩ := h
  have : Fact p.Prime := ⟨(hPS _ hpd).1⟩
  have hrep : IsRepeatedFactor p S β :=
    ⟨hβ.1, hβ.2.1, lem_simple_sq_dvd _ (modP_isSymm p hS) U hU hβ hiso⟩
  have hcond : PairCond PS S ⟨p, β⟩ := ⟨by rw [hd]; exact hpd, hrep⟩
  by_cases hfew : FewIso p S β
  · exact Or.inl ⟨⟨p, β⟩, hcond, hfew, U, hU, hβ, hiso, horth⟩
  · exact Or.inr ⟨⟨p, β⟩, hcond, hfew⟩

theorem ofReal_prob_step1_le (hPS : ∀ x ∈ PS, x.1.Prime ∧ x.1 ≠ 2) {N : ℕ}
    (S : Matrix (Fin N) (Fin N) ℤ) :
    ENNReal.ofReal (prob (fun b : Fin N → Bool => ∃ x, Step1Event PS S (signVec b) x)) ≤
      2 * NPi PS S := by
  classical
  refine (ofReal_prob_exists_le_tsum _).trans ?_
  rw [NPi, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hc : PairCond PS S x
  · have hc' : (x.1, x.2.natDegree) ∈ PS ∧ IsRepeatedFactor x.1 S x.2 := hc
    rw [ite_eq_left hc']
    have : Fact x.1.Prime := ⟨(hPS _ hc.1).1⟩
    by_cases hfew : FewIso x.1 S x.2
    · calc ENNReal.ofReal (prob fun b : Fin N → Bool => Step1Event PS S (signVec b) x)
          ≤ ENNReal.ofReal (2 * abeta x.1 S x.2) := by
            refine ENNReal.ofReal_le_ofReal ((prob_mono fun b hb => hb.2.2).trans ?_)
            exact prob_fewIso_le hfew
        _ = 2 * ENNReal.ofReal (abeta x.1 S x.2) := by
            rw [ENNReal.ofReal_mul (by norm_num)]
            simp
    · have : prob (fun b : Fin N → Bool => Step1Event PS S (signVec b) x) = 0 := by
        rw [← prob_false (Ω := Fin N → Bool)]
        exact prob_congr fun b => by simp [Step1Event, hfew]
      rw [this, ENNReal.ofReal_zero]
      exact zero_le
  · have hc' : ¬ ((x.1, x.2.natDegree) ∈ PS ∧ IsRepeatedFactor x.1 S x.2) := hc
    rw [ite_eq_right hc', mul_zero]
    have : prob (fun b : Fin N → Bool => Step1Event PS S (signVec b) x) = 0 := by
      rw [← prob_false (Ω := Fin N → Bool)]
      exact prob_congr fun b => by simp [Step1Event, hc]
    rw [this, ENNReal.ofReal_zero]

theorem ofReal_prob_delEvent_le (hPS : ∀ x ∈ PS, x.1.Prime ∧ x.1 ≠ 2) {n : ℕ}
    {T : Matrix (Fin n) (Fin n) ℤ} (hT : T.IsSymm) :
    ENNReal.ofReal (prob (fun ξ : Fin n → Bool => DelEvent PS T (signVec ξ))) ≤ NPi PS T := by
  classical
  refine (ofReal_prob_exists_le_tsum _).trans ?_
  rw [NPi]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hc : PairCond PS T x
  · have hc' : (x.1, x.2.natDegree) ∈ PS ∧ IsRepeatedFactor x.1 T x.2 := hc
    rw [ite_eq_left hc']
    have : Fact x.1.Prime := ⟨(hPS _ hc.1).1⟩
    obtain ⟨U, hU, hβ⟩ := exists_simple_of_repeated hT hc.2
    refine ENNReal.ofReal_le_ofReal ((prob_mono fun ξ hξ => ?_).trans (probPerp_le_abeta hU hβ))
    intro y hy
    exact hξ.2 y (hβ.2.2 y hy)
  · have hc' : ¬ ((x.1, x.2.natDegree) ∈ PS ∧ IsRepeatedFactor x.1 T x.2) := hc
    rw [ite_eq_right hc']
    have : prob (fun ξ : Fin n → Bool => PairCond PS T x ∧
        ∀ v, aeval (modP x.1 T) x.2 *ᵥ v = 0 → modPVec x.1 (signVec ξ) ⬝ᵥ v = 0) = 0 := by
      rw [← prob_false (Ω := Fin n → Bool)]
      exact prob_congr fun ξ => by simp [hc]
    rw [this, ENNReal.ofReal_zero]

theorem ofReal_prob_delEvent_avg_le (hPS : ∀ x ∈ PS, x.1.Prime ∧ x.1 ≠ 2) (n : ℕ)
    (G : Set (Matrix (Fin n) (Fin n) ℤ)) :
    ENNReal.ofReal (prob (fun x : (Pairs n → Bool) × (Fin n → Bool) =>
      DelEvent PS (seidelOf x.1) (signVec x.2))) ≤
      ENNReal.ofReal (probSeidel n (fun S => S ∉ G)) + expectNPi PS n G := by
  classical
  have hpt : ∀ ω : Pairs n → Bool,
      ENNReal.ofReal (prob (fun ξ : Fin n → Bool => DelEvent PS (seidelOf ω) (signVec ξ))) ≤
        (if seidelOf ω ∉ G then (1 : ℝ≥0∞) else 0) +
          (if seidelOf ω ∈ G then NPi PS (seidelOf ω) else 0) := by
    intro ω
    by_cases hG : seidelOf ω ∈ G
    · rw [ite_eq_right (not_not.2 hG), ite_eq_left hG, zero_add]
      exact ofReal_prob_delEvent_le hPS (isSeidel_seidelOf ω).1
    · rw [ite_eq_left hG, ite_eq_right hG, add_zero, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (prob_le_one _)
  have h1 := ofReal_prob_prod_le (fun x : (Pairs n → Bool) × (Fin n → Bool) =>
    DelEvent PS (seidelOf x.1) (signVec x.2)) _ hpt
  refine h1.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ENNReal.add_div, probSeidel,
    ofReal_prob_eq (fun ω : Pairs n → Bool => seidelOf ω ∉ G), expectNPi]

end Reduction

section ReductionBound

variable {PS : Set (ℕ × ℕ)}

theorem reduction_bound (hPS : ∀ x ∈ PS, x.1.Prime ∧ x.1 ≠ 2) (n : ℕ)
    (G : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)) (G' : Set (Matrix (Fin n) (Fin n) ℤ)) :
    ENNReal.ofReal (probG (n + 1) (fun G => ∃ p d : ℕ, (p, d) ∈ PS ∧ E p d G)) ≤
      ENNReal.ofReal (probSeidel (n + 1) (fun S => S ∉ G)) + 2 * expectNPi PS (n + 1) G +
        20 * (ENNReal.ofReal (probSeidel n (fun S => S ∉ G')) + expectNPi PS n G') +
        ENNReal.ofReal (probSeidel (n + 1) (fun S => ¬ SuppGood S)) := by
  classical
  rw [probG_eq_switched hPS]
  have hsub : ∀ x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool), SwitchedFailure PS (seidelOf x.1) (signVec x.2) →
      (seidelOf x.1 ∉ G ∨ (seidelOf x.1 ∈ G ∧ ∃ y, Step1Event PS (seidelOf x.1) (signVec x.2) y)) ∨
        ((Step2Event PS (seidelOf x.1) ∧ SuppGood (seidelOf x.1)) ∨ ¬ SuppGood (seidelOf x.1)) := by
    intro x hx
    rcases switchedFailure_cases hPS (isSeidel_seidelOf x.1).1 hx with h1 | h2
    · by_cases hG : seidelOf x.1 ∈ G
      · exact Or.inl (Or.inr ⟨hG, h1⟩)
      · exact Or.inl (Or.inl hG)
    · by_cases hgood : SuppGood (seidelOf x.1)
      · exact Or.inr (Or.inl ⟨h2, hgood⟩)
      · exact Or.inr (Or.inr hgood)
  have hP := prob_mono hsub
  have h1 : prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => seidelOf x.1 ∉ G) = probSeidel (n + 1) (fun S => S ∉ G) :=
    prob_fst (fun ω => seidelOf ω ∉ G)
  have h2 : ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => seidelOf x.1 ∈ G ∧
      ∃ y, Step1Event PS (seidelOf x.1) (signVec x.2) y)) ≤ 2 * expectNPi PS (n + 1) G := by
    have hpt : ∀ ω : Pairs (n + 1) → Bool, ENNReal.ofReal (prob (fun b : Fin (n + 1) → Bool =>
        seidelOf ω ∈ G ∧ ∃ y, Step1Event PS (seidelOf ω) (signVec b) y)) ≤
        if seidelOf ω ∈ G then 2 * NPi PS (seidelOf ω) else 0 := by
      intro ω
      by_cases hG : seidelOf ω ∈ G
      · rw [ite_eq_left hG]
        refine le_trans (ENNReal.ofReal_le_ofReal (prob_mono fun b hb => hb.2)) ?_
        exact ofReal_prob_step1_le hPS _
      · rw [ite_eq_right hG]
        have : prob (fun b : Fin (n + 1) → Bool => seidelOf ω ∈ G ∧
            ∃ y, Step1Event PS (seidelOf ω) (signVec b) y) = 0 := by
          rw [← prob_false (Ω := Fin (n + 1) → Bool)]
          exact prob_congr fun b => by simp [hG]
        rw [this, ENNReal.ofReal_zero]
    refine (ofReal_prob_prod_le (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) =>
      seidelOf x.1 ∈ G ∧ ∃ y, Step1Event PS (seidelOf x.1) (signVec x.2) y) _ hpt).trans ?_
    · rw [expectNPi, ← mul_div_assoc, Finset.mul_sum]
      refine ENNReal.div_le_div_right (le_of_eq (Finset.sum_congr rfl fun ω _ => ?_)) _
      split_ifs <;> simp
  have h3 : ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => Step2Event PS (seidelOf x.1) ∧ SuppGood (seidelOf x.1))) ≤
      20 * (ENNReal.ofReal (probSeidel n (fun S => S ∉ G')) + expectNPi PS n G') := by
    rw [prob_fst (fun ω => Step2Event PS (seidelOf ω) ∧ SuppGood (seidelOf ω))]
    have hE := lem_exch (DelEvent PS) (fun ω => Step2Event PS (seidelOf ω) ∧ SuppGood (seidelOf ω))
      (fun ω hω => by
        obtain ⟨⟨y, hc, hfew⟩, hgood⟩ := hω
        have hy := hPS _ hc.1
        have h1 := many_deletions (n := n) (isSeidel_seidelOf ω).1 hgood (p := y.1) hy.1 hy.2 hc.2 hfew
        refine lt_of_lt_of_le h1 (Nat.cast_le.2 (Finset.card_le_card fun i hi => ?_))
        obtain ⟨-, hrep, horth⟩ := Finset.mem_filter.1 hi
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, y, ⟨hc.1, hrep⟩, horth⟩)
    rw [lem_exch_law] at hE
    calc ENNReal.ofReal (prob fun ω => Step2Event PS (seidelOf ω) ∧ SuppGood (seidelOf ω))
        ≤ ENNReal.ofReal (20 * prob (fun x : (Pairs n → Bool) × (Fin n → Bool) =>
            DelEvent PS (seidelOf x.1) (signVec x.2))) := ENNReal.ofReal_le_ofReal hE
      _ = 20 * ENNReal.ofReal (prob (fun x : (Pairs n → Bool) × (Fin n → Bool) =>
            DelEvent PS (seidelOf x.1) (signVec x.2))) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          simp
      _ ≤ 20 * (ENNReal.ofReal (probSeidel n (fun S => S ∉ G')) + expectNPi PS n G') := by
          gcongr
          exact ofReal_prob_delEvent_avg_le hPS n G'
  have h4 : prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => ¬ SuppGood (seidelOf x.1)) =
      probSeidel (n + 1) (fun S => ¬ SuppGood S) := prob_fst (fun ω => ¬ SuppGood (seidelOf ω))
  calc ENNReal.ofReal (prob fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => SwitchedFailure PS (seidelOf x.1) (signVec x.2))
      ≤ ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => seidelOf x.1 ∉ G) +
          prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => seidelOf x.1 ∈ G ∧ ∃ y, Step1Event PS (seidelOf x.1) (signVec x.2) y) +
          (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => Step2Event PS (seidelOf x.1) ∧ SuppGood (seidelOf x.1)) +
            prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => ¬ SuppGood (seidelOf x.1)))) :=
        ENNReal.ofReal_le_ofReal (hP.trans ((prob_or_le _ _).trans
          (add_le_add (prob_or_le _ _) (prob_or_le _ _))))
    _ = ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => seidelOf x.1 ∉ G)) +
          ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => seidelOf x.1 ∈ G ∧
            ∃ y, Step1Event PS (seidelOf x.1) (signVec x.2) y)) +
          (ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => Step2Event PS (seidelOf x.1) ∧ SuppGood (seidelOf x.1))) +
            ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) => ¬ SuppGood (seidelOf x.1)))) := by
        rw [ENNReal.ofReal_add (add_nonneg (prob_nonneg _) (prob_nonneg _))
            (add_nonneg (prob_nonneg _) (prob_nonneg _)),
          ENNReal.ofReal_add (prob_nonneg _) (prob_nonneg _),
          ENNReal.ofReal_add (prob_nonneg _) (prob_nonneg _)]
    _ ≤ ENNReal.ofReal (probSeidel (n + 1) (fun S => S ∉ G)) + 2 * expectNPi PS (n + 1) G +
          (20 * (ENNReal.ofReal (probSeidel n (fun S => S ∉ G')) + expectNPi PS n G') +
            ENNReal.ofReal (probSeidel (n + 1) (fun S => ¬ SuppGood S))) := by
        rw [h1, h4]
        gcongr
    _ = _ := by ring

theorem prop_reduction (PS : ℕ → Set (ℕ × ℕ)) (hPS : ∀ n, ∀ x ∈ PS n, x.1.Prime ∧ x.1 ≠ 2)
    (G G' : ∀ n, Set (Matrix (Fin n) (Fin n) ℤ))
    (hG : Tendsto (fun n => probSeidel n (fun S => S ∉ G n)) atTop (𝓝 0))
    (hG' : Tendsto (fun n => probSeidel n (fun S => S ∉ G' n)) atTop (𝓝 0))
    (hN : Tendsto (fun n => expectNPi (PS n) n (G n)) atTop (𝓝 0))
    (hN' : Tendsto (fun n => expectNPi (PS (n + 1)) n (G' n)) atTop (𝓝 0)) :
    Tendsto (fun n => probG n (fun G => ∃ p d : ℕ, (p, d) ∈ PS n ∧ E p d G)) atTop (𝓝 0) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  have hS : Tendsto (fun n => probSeidel n (fun S => ¬ SuppGood S)) atTop (𝓝 0) :=
    tendsto_prob_zero_of_le (u := fun m : ℕ => (2 : ℝ) ^ (-(m : ℝ) / 8)) (by
      have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 8 : ℝ)) := by positivity
      have hr1 : (2 : ℝ) ^ (-(1 / 8 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
      refine (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).congr fun m => ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring) lem_support
  have hof : ∀ {u : ℕ → ℝ}, Tendsto u atTop (𝓝 0) → Tendsto (fun n => ENNReal.ofReal (u n)) atTop (𝓝 0) :=
    fun hu => by simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hu
  have hsh : ∀ {u : ℕ → ℝ}, Tendsto u atTop (𝓝 0) → Tendsto (fun n => u (n + 1)) atTop (𝓝 0) :=
    fun hu => hu.comp (tendsto_add_atTop_nat 1)
  have hshE : ∀ {u : ℕ → ℝ≥0∞}, Tendsto u atTop (𝓝 0) → Tendsto (fun n => u (n + 1)) atTop (𝓝 0) :=
    fun hu => hu.comp (tendsto_add_atTop_nat 1)
  have hbound : Tendsto (fun n => ENNReal.ofReal (probSeidel (n + 1) (fun S => S ∉ G (n + 1))) +
      2 * expectNPi (PS (n + 1)) (n + 1) (G (n + 1)) +
      20 * (ENNReal.ofReal (probSeidel n (fun S => S ∉ G' n)) + expectNPi (PS (n + 1)) n (G' n)) +
      ENNReal.ofReal (probSeidel (n + 1) (fun S => ¬ SuppGood S))) atTop (𝓝 0) := by
    have h2 := ENNReal.Tendsto.const_mul (hshE hN) (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    have h20 := ENNReal.Tendsto.const_mul ((hof hG').add hN') (Or.inr (by norm_num : (20 : ℝ≥0∞) ≠ ⊤))
    have := (((hof (hsh hG)).add h2).add h20).add (hof (hsh hS))
    simpa using this
  have hle : ∀ n, ENNReal.ofReal (probG (n + 1) (fun G => ∃ p d : ℕ, (p, d) ∈ PS (n + 1) ∧ E p d G)) ≤
      ENNReal.ofReal (probSeidel (n + 1) (fun S => S ∉ G (n + 1))) +
        2 * expectNPi (PS (n + 1)) (n + 1) (G (n + 1)) +
        20 * (ENNReal.ofReal (probSeidel n (fun S => S ∉ G' n)) + expectNPi (PS (n + 1)) n (G' n)) +
        ENNReal.ofReal (probSeidel (n + 1) (fun S => ¬ SuppGood S)) :=
    fun n => reduction_bound (hPS (n + 1)) n (G (n + 1)) (G' n)
  have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le) hle
  have hreal := (ENNReal.tendsto_toReal (ENNReal.zero_ne_top)).comp hlim
  simp only [ENNReal.toReal_zero] at hreal
  refine hreal.congr fun n => ?_
  rw [Function.comp_apply, ENNReal.toReal_ofReal (by rw [probG_eq_prob]; exact prob_nonneg _)]

end ReductionBound

end DGS
