module

public import DGS.S15_Huge.Dissoc
public import DGS.S15_Huge.LiftInv
public import DGS.S09_Smooth.Smooth

@[expose] public section

open Filter Finset Polynomial

namespace DGS

def NoSmallFactor {m : ℕ} (T : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∀ f : ℤ[X], f.Monic → 1 ≤ f.natDegree → (f.natDegree : ℝ) ≤ (Real.log m) ^ 3 → ¬ f ∣ T.charpoly

theorem acinv_eventually : ∀ᶠ m : ℕ in atTop, 3 ≤ m ∧ 12500 < Real.log m ∧ (Real.log m) ^ 3 < m := by
  have h1 : ∀ᶠ m : ℕ in atTop, 12500 < Real.log m :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 12500)
  have h2 := eventually_mul_log_pow_le_rpow 1 3 (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [eventually_ge_atTop 3, h1, h2] with m hm h1 h2
  refine ⟨hm, h1, ?_⟩
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have h3 : (m : ℝ) ^ (1 / 2 : ℝ) < (m : ℝ) ^ (1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hm1 (by norm_num)
  rw [Real.rpow_one] at h3
  linarith

theorem probPerp_le_rhoG {m p : ℕ} {V : Submodule (ZMod p) (Fin m → ZMod p)} {v : Fin m → ZMod p} (hv : v ∈ V) :
    probPerp p V ≤ rhoG v := by
  refine (prob_mono fun ξ hξ => ?_).trans (prob_sgnSum_le_rhoG v 0)
  rw [sgnSum_eq_twoValued_dot, ← modPVec_signVec]
  exact hξ v hv

theorem probPerp_le_odlyzko {m p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (V : Submodule (ZMod p) (Fin m → ZMod p)) :
    probPerp p V ≤ (2 : ℝ)⁻¹ ^ Module.finrank (ZMod p) V := by
  have h := lem_odlyzko_perp (1 : ZMod p) (-1) (one_ne_neg_one_zmod hp) V
  refine le_trans (le_of_eq ?_) h
  unfold probPerp
  congr 1
  funext ξ
  rw [modPVec_signVec]

theorem lem_acinv : ∀ᶠ m : ℕ in atTop, ∀ T : Matrix (Fin m) (Fin m) ℤ, IsSeidel T → NoSmallFactor T →
    ∀ (p : ℕ) [Fact p.Prime], Real.exp ((Real.log m) ^ 6) < p →
    ∀ V : Submodule (ZMod p) (Fin m → ZMod p), IsInvariant (modP p T) V → V ≠ ⊥ →
      probPerp p V < ((m : ℝ) ^ 3)⁻¹ := by
  filter_upwards [acinv_eventually] with m ⟨hm3, hlog, hlog3⟩
  intro T hT hχ p _ hp V hV hV0
  classical
  set L := Real.log m with hL
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hL0 : 0 < L := by linarith
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hp
    have h1 : 1 ≤ L ^ 6 := one_le_pow₀ (by linarith)
    have h2' := Real.add_one_le_exp (L ^ 6)
    norm_num at hp
    linarith
  have hT1 : ∀ i j, |T i j| ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [hT.2.1]
      norm_num
    · rcases hT.2.2 i j hij with h | h <;> rw [h] <;> norm_num
  set k := Module.finrank (ZMod p) V with hk
  have hm3' : (0 : ℝ) < (m : ℝ) ^ 3 := by positivity
  by_cases hkm : (m : ℝ) ^ 3 < 2 ^ k
  · calc probPerp p V ≤ (2 : ℝ)⁻¹ ^ k := probPerp_le_odlyzko hp2 V
      _ = ((2 : ℝ) ^ k)⁻¹ := inv_pow _ _
      _ < ((m : ℝ) ^ 3)⁻¹ := inv_strictAnti₀ hm3' hkm
  push Not at hkm
  by_contra hcon
  push Not at hcon
  set bV := Module.finBasis (ZMod p) V with hbV
  set v : Fin k → Fin m → ZMod p := fun l => (bV l : Fin m → ZMod p) with hv
  have hvV : ∀ l, v l ∈ V := fun l => (bV l).2
  choose B y hBρ hy hrep using fun l => lem_dissoc hp2 (v l)
  have hB2 : ∀ l, (2 : ℝ) ^ (B l).card ≤ (m : ℝ) ^ 3 := by
    intro l
    have h1 : ((m : ℝ) ^ 3)⁻¹ ≤ rhoG (v l) := hcon.trans (probPerp_le_rhoG (hvV l))
    have h2 : 0 < rhoG (v l) := lt_of_lt_of_le (by positivity) h1
    have h3 := hBρ l
    have h4 : (2 : ℝ) ^ (B l).card ≤ (rhoG (v l))⁻¹ := by
      rw [le_inv_comm₀ (by positivity) h2]
      calc rhoG (v l) = ((2 : ℝ) ^ (B l).card)⁻¹ * ((2 : ℝ) ^ (B l).card * rhoG (v l)) := by field_simp
        _ ≤ ((2 : ℝ) ^ (B l).card)⁻¹ * 1 := by gcongr
        _ = ((2 : ℝ) ^ (B l).card)⁻¹ := mul_one _
    calc (2 : ℝ) ^ (B l).card ≤ (rhoG (v l))⁻¹ := h4
      _ ≤ (((m : ℝ) ^ 3)⁻¹)⁻¹ := inv_anti₀ (by positivity) h1
      _ = (m : ℝ) ^ 3 := inv_inv _
  set s := Nat.log 2 (m ^ 3) with hs
  have hsle : ∀ x : ℕ, (2 : ℝ) ^ x ≤ (m : ℝ) ^ 3 → x ≤ s := by
    intro x hx
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    exact_mod_cast hx
  have hks : k ≤ s := hsle k hkm
  have hBs : ∀ l, (B l).card ≤ s := fun l => hsle _ (hB2 l)
  have hs5 : (s : ℝ) ≤ 5 * L := by
    have h1 : 2 ^ s ≤ m ^ 3 := Nat.pow_log_le_self 2 (by positivity)
    have h2 : (2 : ℝ) ^ s ≤ (m : ℝ) ^ 3 := by exact_mod_cast h1
    have h3 : (s : ℝ) * Real.log 2 ≤ 3 * L := by
      have h3' := Real.log_le_log (by positivity) h2
      rw [Real.log_pow, Real.log_pow] at h3'
      push_cast at h3'
      rw [← hL] at h3'
      exact h3'
    have h4 := Real.log_two_gt_d9
    have h5 : (s : ℝ) * 0.6931471803 ≤ (s : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left h4.le (Nat.cast_nonneg s)
    nlinarith
  set u : (Σ l : Fin k, ↥(B l)) → Fin m → ℤ := fun x => y x.1 x.2 with hu
  have hu1 : ∀ x i, |u x i| ≤ 1 := by
    intro x i
    rcases hy x.1 x.2 i with h | h | h <;> simp [hu, h]
  have hD : Fintype.card (Σ l : Fin k, ↥(B l)) ≤ s * s := by
    rw [Fintype.card_sigma]
    calc ∑ l : Fin k, Fintype.card ↥(B l) = ∑ l : Fin k, (B l).card := by simp
      _ ≤ ∑ _l : Fin k, s := sum_le_sum fun l _ => hBs l
      _ = k * s := by simp
      _ ≤ s * s := Nat.mul_le_mul_right s hks
  have hDR : (Fintype.card (Σ l : Fin k, ↥(B l)) : ℝ) ≤ 25 * L ^ 2 := by
    have h1 : (Fintype.card (Σ l : Fin k, ↥(B l)) : ℝ) ≤ (s : ℝ) * s := by exact_mod_cast hD
    have h2 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    nlinarith
  have hDm : Fintype.card (Σ l : Fin k, ↥(B l)) < m := by
    have h1 : (Fintype.card (Σ l : Fin k, ↥(B l)) : ℝ) < m := by nlinarith
    exact_mod_cast h1
  have hVu : V ≤ Submodule.span (ZMod p) (Set.range fun x i => (u x i : ZMod p)) := by
    have hvu : ∀ l, v l ∈ Submodule.span (ZMod p) (Set.range fun x i => (u x i : ZMod p)) := by
      intro l
      rw [hrep l]
      refine Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨l, ⟨b, hb⟩⟩, ?_⟩)
      rfl
    intro w hw
    have h1 : (⟨w, hw⟩ : V) = ∑ l, (bV.repr ⟨w, hw⟩ l) • bV l := (bV.sum_repr _).symm
    have h2 : w = ∑ l, (bV.repr ⟨w, hw⟩ l) • v l := by
      have h3 := congrArg Subtype.val h1
      rw [Submodule.coe_sum] at h3
      simp only [Submodule.coe_smul] at h3
      exact h3
    rw [h2]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hvu l)
  have hχ' : ∀ f : ℤ[X], f.Monic → 1 ≤ f.natDegree → f.natDegree ≤ Fintype.card (Σ l : Fin k, ↥(B l)) → ¬ f ∣ T.charpoly := by
    intro f hf hf1 hfD
    refine hχ f hf hf1 ?_
    have h1 : (f.natDegree : ℝ) ≤ Fintype.card (Σ l : Fin k, ↥(B l)) := by exact_mod_cast hfD
    nlinarith
  have hU : ∀ W : Submodule ℚ (Fin m → ℚ), IsInvariant (T.map (Int.castRingHom ℚ)) W →
      W ≤ Submodule.span ℚ (Set.range fun x i => (u x i : ℚ)) → W = ⊥ := by
    intro W hW hWU
    refine eq_bot_of_noFactor T hχ' W hW ?_
    exact (Submodule.finrank_mono hWU).trans (finrank_range_le_card _)
  have hpm : p ≤ m ^ (20 * Fintype.card (Σ l : Fin k, ↥(B l)) ^ 2) := by
    by_contra hlt
    push Not at hlt
    exact hV0 (lem_liftinv (by omega) hDm T hT1 u hu1 hU hlt V hV hVu)
  have hlogp : Real.log p ≤ 20 * (Fintype.card (Σ l : Fin k, ↥(B l)) : ℝ) ^ 2 * L := by
    have h1 : (p : ℝ) ≤ (m : ℝ) ^ (20 * Fintype.card (Σ l : Fin k, ↥(B l)) ^ 2) := by exact_mod_cast hpm
    have h2 := Real.log_le_log (by exact_mod_cast (Fact.out : p.Prime).pos) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hlogp' : L ^ 6 < Real.log p := by
    rw [Real.lt_log_iff_exp_lt (by exact_mod_cast (Fact.out : p.Prime).pos)]
    exact hp
  have hD2 : (Fintype.card (Σ l : Fin k, ↥(B l)) : ℝ) ^ 2 ≤ 625 * L ^ 4 := by
    have h0 : (0 : ℝ) ≤ Fintype.card (Σ l : Fin k, ↥(B l)) := Nat.cast_nonneg _
    nlinarith
  have h5 : 20 * (Fintype.card (Σ l : Fin k, ↥(B l)) : ℝ) ^ 2 * L ≤ 12500 * L ^ 5 := by nlinarith
  have h6 : 12500 * L ^ 5 < L ^ 6 := by
    have : 0 < L ^ 5 := by positivity
    nlinarith
  linarith

theorem abeta_lt_of_acinv : ∀ᶠ m : ℕ in atTop, ∀ T : Matrix (Fin m) (Fin m) ℤ, IsSeidel T → NoSmallFactor T →
    ∀ (p : ℕ) [Fact p.Prime], Real.exp ((Real.log m) ^ 6) < p → ∀ β : (ZMod p)[X],
      abeta p T β < ((m : ℝ) ^ 3)⁻¹ := by
  filter_upwards [lem_acinv, eventually_ge_atTop 1] with m hm hm1
  intro T hT hχ p _ hp β
  classical
  have hpos : (0 : ℝ) < ((m : ℝ) ^ 3)⁻¹ := by
    have : (0 : ℝ) < m := by exact_mod_cast hm1
    positivity
  set S := {x : ℝ | ∃ U, IsSimpleInvariant (modP p T) U ∧ HasType (modP p T) U β ∧ x = probPerp p U} with hS
  have hfin : S.Finite := by
    have : Finite (Submodule (ZMod p) (Fin m → ZMod p)) :=
      Finite.of_injective (fun U : Submodule (ZMod p) (Fin m → ZMod p) => (U : Set (Fin m → ZMod p)))
        SetLike.coe_injective
    refine (Set.finite_range fun U : Submodule (ZMod p) (Fin m → ZMod p) => probPerp p U).subset ?_
    rintro x ⟨U, -, -, rfl⟩
    exact ⟨U, rfl⟩
  unfold abeta
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · rw [← hS, hS0, Real.sSup_empty]
    exact hpos
  · obtain ⟨U, hU, -, hx⟩ := hSne.csSup_mem hfin
    rw [← hS, hx]
    exact hm T hT hχ p hp U hU.1 hU.2.1

end DGS
