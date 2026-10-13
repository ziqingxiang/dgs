module

public import DGS.S10_Tools.Halasz
public import DGS.S04_Reduction.Reduction

@[expose] public section

open Finset Matrix
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime]

theorem valMinAbs_two_mul_injective (hp2 : p ≠ 2) :
    Function.Injective fun σ : ZMod p => (2 * σ).valMinAbs := by
  intro a b hab
  have h : 2 * a = 2 * b := ZMod.valMinAbs_inj.1 hab
  exact mul_left_cancel₀ (two_ne_zero_zmod hp2) h

theorem lem_LOp (hp2 : p ≠ 2) {t : ℕ} (ht : 2 ≤ t) :
    (p : ℝ)⁻¹ * ∑ σ : ZMod p, |cosP σ| ^ t ≤ (p : ℝ)⁻¹ * ∑ σ : ZMod p, cosP σ ^ (2 * (t / 2)) ∧
    (p : ℝ)⁻¹ * ∑ σ : ZMod p, cosP σ ^ (2 * (t / 2)) ≤ 1 / p + 1 / √(π * ((t / 2 : ℕ) : ℝ)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set h := t / 2 with hh
  have hh1 : 1 ≤ h := by omega
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh1
  constructor
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) (by positivity)
    rw [← pow_abs_two_mul]
    exact pow_le_pow_of_le_one (abs_nonneg _) (abs_cosP_le_one σ) (by omega)
  · set lam : ℝ := π ^ 2 * h / (p : ℝ) ^ 2 with hlam
    have hlam0 : 0 < lam := by positivity
    have hterm : ∀ σ : ZMod p, cosP σ ^ (2 * h) ≤ gaussW lam (2 * σ).valMinAbs := by
      intro σ
      rw [← pow_abs_two_mul]
      calc |cosP σ| ^ (2 * h)
          ≤ (Real.exp (-(π ^ 2 / 2) * ((((2 * σ).valMinAbs : ℤ) : ℝ) / p) ^ 2)) ^ (2 * h) :=
            pow_le_pow_left₀ (abs_nonneg _) (abs_cosP_le_exp_halasz σ) _
        _ = gaussW lam (2 * σ).valMinAbs := by
            rw [← Real.exp_nat_mul, gaussW, hlam]
            congr 1
            push_cast
            field_simp
    have hsum : ∑ σ : ZMod p, gaussW lam (2 * σ).valMinAbs ≤ 1 + √(π / lam) := by
      rw [← Finset.sum_image (f := gaussW lam) (s := Finset.univ)
        (valMinAbs_two_mul_injective hp2).injOn]
      exact ((summable_gaussW hlam0).sum_le_tsum _ fun z _ => (Real.exp_pos _).le).trans
        (tsum_gaussW_le hlam0)
    have hsq : √(π / lam) = p / √(π * h) := by
      have e : π / lam = (p : ℝ) ^ 2 / (π * h) := by
        rw [hlam]
        field_simp
      rw [e, Real.sqrt_div (by positivity), Real.sqrt_sq hp.le]
    have hpi : 0 < √(π * h) := Real.sqrt_pos.2 (by positivity)
    calc (p : ℝ)⁻¹ * ∑ σ : ZMod p, cosP σ ^ (2 * h)
        ≤ (p : ℝ)⁻¹ * ∑ σ : ZMod p, gaussW lam (2 * σ).valMinAbs :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hterm σ) (by positivity)
      _ ≤ (p : ℝ)⁻¹ * (1 + √(π / lam)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 / p + 1 / √(π * h) := by
          rw [hsq]
          field_simp

section LObases

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

omit [Fintype ι] in
theorem dotProj_bijective (φ : ι → Fin d → ZMod p) (B : Finset ι) (hcard : B.card = d)
    (hspan : Submodule.span (ZMod p) (φ '' (B : Set ι)) = ⊤) :
    Function.Bijective fun τ : Fin d → ZMod p => fun j : B => τ ⬝ᵥ φ j := by
  have hinj : Function.Injective fun τ : Fin d → ZMod p => fun j : B => τ ⬝ᵥ φ j := by
    intro τ τ' h
    let f : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p :=
      { toFun := fun v => (τ - τ') ⬝ᵥ v
        map_add' := fun v w => dotProduct_add _ _ _
        map_smul' := fun c v => by simp [dotProduct_smul] }
    have hle : Submodule.span (ZMod p) (φ '' (B : Set ι)) ≤ LinearMap.ker f := by
      rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      have h1 := congrFun h ⟨j, hj⟩
      simp only at h1
      show (τ - τ') ⬝ᵥ φ j = 0
      rw [sub_dotProduct, h1, sub_self]
    rw [hspan] at hle
    funext i
    have h2 : (τ - τ') ⬝ᵥ Pi.single i 1 = 0 := hle Submodule.mem_top
    rw [dotProduct_single, mul_one, Pi.sub_apply] at h2
    exact sub_eq_zero.1 h2
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩
  simp [ZMod.card, hcard]

theorem lem_LObases_a (hp2 : p ≠ 2) {t : ℕ} (ht : 2 ≤ t) (φ : ι → Fin d → ZMod p)
    (B : Fin t → Finset ι) (hdisj : Pairwise fun c c' => Disjoint (B c) (B c'))
    (hcard : ∀ c, (B c).card = d) (hspan : ∀ c, Submodule.span (ZMod p) (φ '' (B c : Set ι)) = ⊤) :
    rhoG φ ≤ rhoHat φ ∧ rhoHat φ ≤ (1 / p + 1 / √(π * ((t / 2 : ℕ) : ℝ))) ^ d := by
  refine ⟨rhoG_le_rhoHat φ, ?_⟩
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set F : Fin t → (Fin d → ZMod p) → ℝ := fun c τ => ∏ j ∈ B c, |cosP (τ ⬝ᵥ φ j)| with hF
  set S : ℝ := ∑ σ : ZMod p, |cosP σ| ^ t with hS
  have hF0 : ∀ c τ, 0 ≤ F c τ := fun c τ => Finset.prod_nonneg fun j _ => abs_nonneg _
  have h1 : ∀ τ : Fin d → ZMod p, ∏ j, |cosP (τ ⬝ᵥ φ j)| ≤ ∏ c, F c τ := by
    intro τ
    have e : ∏ c, F c τ = ∏ j ∈ Finset.univ.biUnion B, |cosP (τ ⬝ᵥ φ j)| :=
      (Finset.prod_biUnion fun c _ c' _ hcc' => hdisj hcc').symm
    rw [e, ← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.biUnion B))]
    refine mul_le_of_le_one_left (Finset.prod_nonneg fun j _ => abs_nonneg _) ?_
    exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ => abs_cosP_le_one _
  have h2 : ∀ τ, ∏ c, F c τ ≤ ∑ c, (t : ℝ)⁻¹ * F c τ ^ t := by
    intro τ
    have htR : (t : ℝ) ≠ 0 := by positivity
    have := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) (fun _ => (t : ℝ)⁻¹)
      (fun c => F c τ ^ t) (fun _ _ => by positivity)
      (by simp [Finset.card_univ, Fintype.card_fin, htR]) (fun c _ => pow_nonneg (hF0 c τ) t)
    simpa only [Real.pow_rpow_inv_natCast (hF0 _ τ) (by omega : t ≠ 0)] using this
  have h3 : ∀ c, ∑ τ : Fin d → ZMod p, F c τ ^ t = S ^ d := by
    intro c
    have hbij := dotProj_bijective φ (B c) (hcard c) (hspan c)
    calc ∑ τ : Fin d → ZMod p, F c τ ^ t
        = ∑ τ : Fin d → ZMod p, ∏ j : B c, |cosP (τ ⬝ᵥ φ j)| ^ t := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [hF, ← Finset.prod_pow, ← Finset.prod_coe_sort]
      _ = ∑ σ : B c → ZMod p, ∏ j : B c, |cosP (σ j)| ^ t :=
          Fintype.sum_bijective _ hbij _ _ fun τ => rfl
      _ = ∏ j : B c, ∑ x : ZMod p, |cosP x| ^ t :=
          (Fintype.prod_sum (fun (_ : B c) (x : ZMod p) => |cosP x| ^ t)).symm
      _ = S ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, hcard c]
  have hSp : S / p ≤ 1 / p + 1 / √(π * ((t / 2 : ℕ) : ℝ)) := by
    have := (lem_LOp hp2 ht).1.trans (lem_LOp hp2 ht).2
    rwa [hS, div_eq_inv_mul]
  have hS0 : 0 ≤ S / p := div_nonneg (Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _) hp.le
  have htR : (t : ℝ) ≠ 0 := by positivity
  calc rhoHat φ = ((p : ℝ) ^ d)⁻¹ * ∑ τ : Fin d → ZMod p, ∏ j, |cosP (τ ⬝ᵥ φ j)| := rfl
    _ ≤ ((p : ℝ) ^ d)⁻¹ * ∑ τ : Fin d → ZMod p, ∑ c, (t : ℝ)⁻¹ * F c τ ^ t :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => (h1 τ).trans (h2 τ)) (by positivity)
    _ = ((p : ℝ) ^ d)⁻¹ * S ^ d := by
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, h3]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
    _ = (S / p) ^ d := by rw [div_pow, div_eq_inv_mul]
    _ ≤ _ := pow_le_pow_left₀ hS0 hSp d

omit [Fintype ι] in
theorem exists_sub_span_top (φ : ι → Fin d → ZMod p) (R : Finset ι)
    (hR : Submodule.span (ZMod p) (φ '' (R : Set ι)) = ⊤) :
    ∃ B ⊆ R, B.card = d ∧ Submodule.span (ZMod p) (φ '' (B : Set ι)) = ⊤ := by
  set 𝒮 := R.powerset.filter fun B : Finset ι => Submodule.span (ZMod p) (φ '' (B : Set ι)) = ⊤
    with h𝒮
  have hne : 𝒮.Nonempty := ⟨R, mem_filter.2 ⟨mem_powerset_self R, hR⟩⟩
  obtain ⟨B, hB, hmin⟩ := 𝒮.exists_min_image Finset.card hne
  rw [mem_filter, mem_powerset] at hB
  refine ⟨B, hB.1, le_antisymm ?_ ?_, hB.2⟩
  ·
    by_contra hlt
    push Not at hlt
    have hnli : ¬ LinearIndependent (ZMod p) (fun j : B => φ j) := by
      intro hli
      have := hli.fintype_card_le_finrank
      rw [Fintype.card_coe, Module.finrank_fin_fun] at this
      omega
    rw [linearIndependent_iff_notMem_span] at hnli
    push Not at hnli
    obtain ⟨j, hj⟩ := hnli
    have hsub : B.erase j ∈ 𝒮 := by
      rw [mem_filter, mem_powerset]
      refine ⟨(erase_subset _ _).trans hB.1, ?_⟩
      rw [eq_top_iff, ← hB.2, Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      by_cases hij : i = j
      · subst hij
        refine Submodule.span_mono ?_ hj
        rintro _ ⟨i', hi', rfl⟩
        refine ⟨i', ?_, rfl⟩
        rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff]
        refine ⟨i'.2, fun h => ?_⟩
        apply hi'.2
        exact Subtype.ext h
      · exact Submodule.subset_span ⟨i, by simp [hij, hi], rfl⟩
    have := hmin _ hsub
    rw [card_erase_of_mem j.2] at this
    omega
  ·
    have h1 := finrank_span_finset_le_card (R := ZMod p) (B.image φ)
    rw [Set.finrank, coe_image, hB.2, finrank_top, Module.finrank_fin_fun] at h1
    exact h1.trans card_image_le

theorem lem_LObases_b {k : ℕ} (hd : 1 ≤ d) (φ : ι → Fin d → ZMod p)
    (hk : ∀ a : Fin d → ZMod p, a ≠ 0 → k ≤ (Finset.univ.filter fun j => a ⬝ᵥ φ j ≠ 0).card) :
    ∃ B : Fin ((k + d - 1) / d) → Finset ι, (Pairwise fun c c' => Disjoint (B c) (B c')) ∧
      (∀ c, (B c).card = d) ∧ ∀ c, Submodule.span (ZMod p) (φ '' (B c : Set ι)) = ⊤ := by
  suffices H : ∀ c, c ≤ (k + d - 1) / d → ∃ B : Fin c → Finset ι,
      (Pairwise fun c c' => Disjoint (B c) (B c')) ∧ (∀ i, (B i).card = d) ∧
      ∀ i, Submodule.span (ZMod p) (φ '' (B i : Set ι)) = ⊤ from H _ le_rfl
  intro c
  induction c with
  | zero =>
    intro _
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ c ih =>
    intro hc
    obtain ⟨B, hdisj, hcard, hspan⟩ := ih (by omega)
    have hck : c * d < k := by
      have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).1 hc
      rw [Nat.succ_mul] at this
      omega
    set U := Finset.univ.biUnion B with hUdef
    have hU : U.card ≤ c * d := by
      refine card_biUnion_le.trans ?_
      simp [hcard]
    set R := Finset.univ \ U with hRdef
    have hR : Submodule.span (ZMod p) (φ '' (R : Set ι)) = ⊤ := by
      by_contra hne
      obtain ⟨V, hV, hdim⟩ := finrank_orthogonal_dotProduct (Submodule.span (ZMod p) (φ '' (R : Set ι)))
      have hlt := Submodule.finrank_lt hne
      rw [Module.finrank_fin_fun] at hlt
      have hV0 : V ≠ ⊥ := by
        intro h0
        rw [h0, finrank_bot] at hdim
        omega
      obtain ⟨a, haV, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
      have hsub : (Finset.univ.filter fun j => a ⬝ᵥ φ j ≠ 0) ⊆ U := by
        intro j hj
        rw [mem_filter] at hj
        by_contra hjU
        apply hj.2
        have hjR : j ∈ (R : Set ι) := by
          rw [hRdef, Finset.coe_sdiff, Set.mem_sdiff]
          exact ⟨Finset.mem_coe.2 (mem_univ j), hjU⟩
        exact (hV a).1 haV _ (Submodule.subset_span ⟨j, hjR, rfl⟩)
      have := (hk a ha0).trans ((card_le_card hsub).trans hU)
      omega
    obtain ⟨B', hB'R, hB'card, hB'span⟩ := exists_sub_span_top φ R hR
    have hBU : ∀ i, B i ⊆ U := fun i => Finset.subset_biUnion_of_mem B (mem_univ i)
    have hB'U : Disjoint B' U := Finset.disjoint_of_subset_left hB'R Finset.sdiff_disjoint
    let B2 : Fin (c + 1) → Finset ι := fun i => if h : (i : ℕ) < c then B ⟨i, h⟩ else B'
    refine ⟨B2, ?_, ?_, ?_⟩
    · intro i i' hii'
      simp only [B2]
      by_cases hi : (i : ℕ) < c <;> by_cases hi' : (i' : ℕ) < c
      · rw [dite_eq_left hi, dite_eq_left hi']
        refine hdisj fun h => hii' (Fin.ext ?_)
        exact Fin.mk.inj_iff.1 h
      · rw [dite_eq_left hi, dite_eq_right hi']
        exact Finset.disjoint_of_subset_left (hBU _) hB'U.symm
      · rw [dite_eq_right hi, dite_eq_left hi']
        exact Finset.disjoint_of_subset_right (hBU _) hB'U
      · exfalso
        apply hii'
        apply Fin.ext
        omega
    · intro i
      simp only [B2]
      split_ifs
      · exact hcard _
      · exact hB'card
    · intro i
      simp only [B2]
      split_ifs
      · exact hspan _
      · exact hB'span

end LObases

theorem lem_LObases_c (hp2 : p ≠ 2) {m d k : ℕ} (U : Submodule (ZMod p) (Fin m → ZMod p))
    (hd : Module.finrank (ZMod p) U = d)
    (hk : ∀ y ∈ U, y ≠ 0 → k ≤ (Finset.univ.filter fun j => y j ≠ 0).card)
    (ht : 2 ≤ (k + d - 1) / d) :
    probPerp p U ≤ (1 / p + 1 / √(π * (((k + d - 1) / d / 2 : ℕ) : ℝ))) ^ d := by
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      simp at ht
    · exact h
  let b := Module.finBasisOfFinrankEq (ZMod p) U hd
  let φ : Fin m → Fin d → ZMod p := fun j i => (b i : Fin m → ZMod p) j
  have hperp : ∀ ξ : Fin m → Bool,
      (∀ u ∈ U, modPVec p (signVec ξ) ⬝ᵥ u = 0) ↔ sgnSum φ ξ = 0 := by
    intro ξ
    set s := modPVec p (signVec ξ) with hs
    have hcoord : ∀ i, sgnSum φ ξ i = s ⬝ᵥ (b i : Fin m → ZMod p) := by
      intro i
      simp only [sgnSum, Finset.sum_apply, dotProduct, hs, modPVec, signVec, φ,
        zsmul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      cases ξ j <;> simp [sgnZ]
    constructor
    · intro h
      funext i
      rw [hcoord i, Pi.zero_apply]
      exact h _ (b i).2
    · intro h u hu
      have hb : ∀ i, s ⬝ᵥ (b i : Fin m → ZMod p) = 0 := fun i => by
        rw [← hcoord i, h, Pi.zero_apply]
      have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : Fin m → ZMod p) := by
        have := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        exact this.symm
      rw [hu', dotProduct_sum]
      simp [dotProduct_smul, hb]
  have h1 : probPerp p U ≤ rhoG φ := by
    unfold probPerp
    rw [prob_congr hperp]
    exact prob_sgnSum_le_rhoG φ 0
  have hmiss : ∀ a : Fin d → ZMod p, a ≠ 0 →
      k ≤ (Finset.univ.filter fun j => a ⬝ᵥ φ j ≠ 0).card := by
    intro a ha
    set y : Fin m → ZMod p := ∑ i, a i • (b i : Fin m → ZMod p) with hy
    have hyU : y ∈ U := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2
    have hy0 : y ≠ 0 := by
      intro h0
      have h2 : ∑ i, a i • b i = 0 := by
        apply Subtype.ext
        simpa [hy] using h0
      exact ha (funext (Fintype.linearIndependent_iff.1 b.linearIndependent a h2))
    have hyj : ∀ j, y j = a ⬝ᵥ φ j := by
      intro j
      simp [hy, φ, dotProduct, Finset.sum_apply]
    have := hk y hyU hy0
    simpa only [hyj] using this
  obtain ⟨B, hdisj, hcard, hspan⟩ := lem_LObases_b hd1 φ hmiss
  have h2 := lem_LObases_a hp2 ht φ B hdisj hcard hspan
  exact h1.trans (h2.1.trans h2.2)

end DGS
