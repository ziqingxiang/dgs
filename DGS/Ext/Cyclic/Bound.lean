module

public import DGS.Ext.Cyclic.Core
public import DGS.S11_Deg1.Deg1
public import DGS.S11_Deg1.PtrueMain
public import DGS.S12_Deg2.SEdCons
public import DGS.S12_Deg2.SEd
public import DGS.S13_Deg3.Deg5Main
public import Mathlib.NumberTheory.Bertrand

@[expose] public section

open Matrix Polynomial Module Filter Topology Finset
open scoped ENNReal

namespace DGS

def GoodAll {m : ℕ} (T : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  GoodSE T ∧ GoodSEd 2 T ∧ GoodSEd 3 T ∧ GoodSEd 4 T ∧ SuppGoodS T

open Classical in
noncomputable def eigCount (p : ℕ) [Fact p.Prime] {m : ℕ} (ω : Pairs m → Bool) : ℕ :=
  (Finset.univ.filter fun μ : ZMod p => 1 ≤ geomMult (F := ZMod p) 1 (-1) μ ω).card

section Pointwise

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

theorem one_le_geomMult_of_dvd (μ : ZMod p) (ω : Pairs m → Bool)
    (h : X - C μ ∣ (modP p (seidelOf ω)).charpoly) : 1 ≤ geomMult (F := ZMod p) 1 (-1) μ ω := by
  by_contra h0
  have hdet := isUnit_det_of_geomMult_eq_zero μ ω (by omega)
  have hroot : (modP p (seidelOf ω)).charpoly.eval μ = 0 := (dvd_iff_isRoot).1 h
  rw [Matrix.eval_charpoly] at hroot
  have hneg : Matrix.scalar (Fin m) μ - modP p (seidelOf ω) = -shiftedMat (F := ZMod p) 1 (-1) μ ω := by
    rw [shiftedMat_eq_modP, neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [hneg, det_neg] at hroot
  exact isUnit_iff_ne_zero.1 hdet ((mul_eq_zero.1 hroot).resolve_left (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)))

theorem card_factors_le (T : Matrix (Fin m) (Fin m) ℤ) (s : Finset (ZMod p)[X])
    (hs : ∀ β ∈ s, IsFactor p T β) : s.card ≤ m := by
  classical
  have hpair : (s : Set (ZMod p)[X]).Pairwise (Function.onFun IsCoprime id) := by
    intro β hβ β' hβ' hne
    exact isCoprime_of_monic_irreducible (hs β hβ).1 (hs β hβ).2.1 (hs β' hβ').1 (hs β' hβ').2.1 hne
  have hdvd : ∏ β ∈ s, β ∣ (modP p T).charpoly :=
    Finset.prod_dvd_of_coprime hpair fun β hβ => (hs β hβ).2.2
  have hdeg : (∏ β ∈ s, β).natDegree = ∑ β ∈ s, β.natDegree :=
    natDegree_prod _ _ fun β hβ => (hs β hβ).1.ne_zero
  have hle : (∏ β ∈ s, β).natDegree ≤ m := by
    have h1 := natDegree_le_of_dvd hdvd (charpoly_monic _).ne_zero
    rwa [charpoly_natDegree_eq_dim, Fintype.card_fin] at h1
  calc s.card = ∑ _β ∈ s, 1 := by rw [card_eq_sum_ones]
    _ ≤ ∑ β ∈ s, β.natDegree := sum_le_sum fun β hβ => (hs β hβ).2.1.natDegree_pos
    _ = (∏ β ∈ s, β).natDegree := hdeg.symm
    _ ≤ m := hle

theorem eq_X_sub_C_of_monic {β : (ZMod p)[X]} (hβm : β.Monic) (hdeg : β.natDegree = 1) :
    β = X - C (-β.coeff 0) := by
  rw [map_neg, sub_neg_eq_add]
  exact hβm.eq_X_add_C hdeg

noncomputable def bHigh (p N m : ℕ) : ℝ :=
  ((p : ℝ) ^ 2)⁻¹ + Real.exp (-2 * cSEd * m) + (2 * (N : ℝ) ^ (-(1 / 2 - 1 / 20 : ℝ))) ^ 5 + ((N : ℝ) ^ 3)⁻¹

theorem bHigh_nonneg (p N m : ℕ) : 0 ≤ bHigh p N m := by
  unfold bHigh
  positivity

structure HighHyp (N m p : ℕ) : Prop where
  hp2 : p ≠ 2
  hp23 : 23 ≤ p
  hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))
  hmp : m ≤ p
  hm1 : 1 ≤ m
  hN1 : 1 ≤ N
  hL1 : 1 ≤ Real.logb 2 N
  hA : 200 * (Real.logb 2 N) ^ 2 ≤ (N : ℝ) ^ (2 * (1 / 20 : ℝ))
  hC : 2 * (N : ℝ) ^ (2 * (1 / 20 : ℝ)) ≤ (N : ℝ) - 1
  hB : 100 * (Real.logb 2 N) ^ 4 ≤ (N : ℝ)
  hD : 2 ≤ (N : ℝ) ^ (1 / 2 - 1 / 20 : ℝ)
  h32 : 32 ≤ N
  hE : (N : ℝ) ^ (1 / 10 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 8)
  hm : N - 1 ≤ m
  hpN : (N : ℝ) ^ (1 / 2 - 1 / 20 : ℝ) < p
  hpX : (p : ℝ) ≤ Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))

theorem abeta_le_bHigh {N : ℕ} (H : HighHyp N m p) {T : Matrix (Fin m) (Fin m) ℤ} (hG : GoodAll T)
    {β : (ZMod p)[X]} (hβ : IsFactor p T β) (hdeg : β.natDegree ≠ 1) : abeta p T β ≤ bHigh p N m := by
  have hd1 : 1 ≤ β.natDegree := hβ.2.1.natDegree_pos
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have h1 : 0 ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
  have h2 : 0 ≤ Real.exp (-2 * cSEd * m) := (Real.exp_pos _).le
  have h3 : 0 ≤ (2 * (N : ℝ) ^ (-(1 / 2 - 1 / 20 : ℝ))) ^ 5 := by positivity
  have h4 : 0 ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
  unfold bHigh
  by_cases hd4 : β.natDegree ≤ 4
  ·
    have hp4 : 3 ≤ β.natDegree → (m : ℝ) ^ (0.4 : ℝ) ≤ p := by
      intro _
      have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast H.hm1
      calc (m : ℝ) ^ (0.4 : ℝ) ≤ (m : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hm1R (by norm_num)
        _ = m := Real.rpow_one _
        _ ≤ p := by exact_mod_cast H.hmp
    have hgood : GoodSEd β.natDegree T := by
      obtain h | h | h : β.natDegree = 2 ∨ β.natDegree = 3 ∨ β.natDegree = 4 := by omega
      · rw [h]; exact hG.2.1
      · rw [h]; exact hG.2.2.1
      · rw [h]; exact hG.2.2.2.1
    have hb := abeta_le_of_goodSEd hgood H.hp23 H.hpm hp4 hβ.1 hβ.2.1 rfl
    have hpd : ((p : ℝ) ^ β.natDegree)⁻¹ ≤ ((p : ℝ) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ hpR (by omega))
    linarith
  by_cases hdL : (β.natDegree : ℝ) < 3 * Real.logb 2 N
  ·
    have hx : ((⟨p, β⟩ : Σ p : ℕ, (ZMod p)[X]).1, (⟨p, β⟩ : Σ p : ℕ, (ZMod p)[X]).2.natDegree) ∈
        PSdeg5 (1 / 20) N :=
      ⟨Fact.out, H.hp2, H.hpN, H.hpX, (by omega : 5 ≤ β.natDegree), hdL⟩
    have hb := deg5_abeta_le H.hL1 H.hA H.hC H.hB H.hD H.h32 H.hE H.hm hG.2.2.2.2 hx
    linarith
  ·
    have hb := abeta_le_inv_cube H.hp2 T β H.hN1 (not_lt.1 hdL)
    linarith

theorem Nall_le_of_goodAll {N : ℕ} (H : HighHyp N m p) (ω : Pairs m → Bool) (hG : GoodAll (seidelOf ω)) :
    Nall p (seidelOf ω) ≤ ENNReal.ofReal ((1 / (p : ℝ) + Real.exp (-2 * cSE * m)) * eigCount p ω +
      m * bHigh p N m) := by
  classical
  set c₁ : ℝ := 1 / (p : ℝ) + Real.exp (-2 * cSE * m) with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  clear_value c₁
  have hb0 := bHigh_nonneg p N m
  rw [Nall]
  refine tsum_le_of_sum_le' zero_le fun s => ?_
  have key : ∀ β ∈ s, (if IsFactor p (seidelOf ω) β then ENNReal.ofReal (abeta p (seidelOf ω) β) else 0) ≤
      (if IsFactor p (seidelOf ω) β ∧ β.natDegree = 1 then ENNReal.ofReal c₁ else 0) +
      (if IsFactor p (seidelOf ω) β ∧ β.natDegree ≠ 1 then ENNReal.ofReal (bHigh p N m) else 0) := by
    intro β _
    by_cases hf : IsFactor p (seidelOf ω) β
    · by_cases hd : β.natDegree = 1
      · rw [ite_eq_left hf, ite_eq_left ⟨hf, hd⟩, ite_eq_right (fun h => h.2 hd), add_zero,
          eq_X_sub_C_of_monic hf.1 hd, hc₁]
        exact ENNReal.ofReal_le_ofReal (abeta_deg1_le hG.1 H.hp23 H.hpm _)
      · rw [ite_eq_left hf, ite_eq_right (fun h => hd h.2), ite_eq_left ⟨hf, hd⟩, zero_add]
        exact ENNReal.ofReal_le_ofReal (abeta_le_bHigh H hG hf hd)
    · rw [ite_eq_right hf]
      exact zero_le
  refine (Finset.sum_le_sum key).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const_zero,
    add_zero, add_zero, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hcard1 : (s.filter fun β => IsFactor p (seidelOf ω) β ∧ β.natDegree = 1).card ≤ eigCount p ω := by
    unfold eigCount
    refine Finset.card_le_card_of_injOn (fun β => -β.coeff 0) (fun β hβ => ?_) (fun β hβ β' hβ' h => ?_)
    · obtain ⟨-, hfac, hdeg⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hβ)
      have hdvd := hfac.2.2
      rw [eq_X_sub_C_of_monic hfac.1 hdeg] at hdvd
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, one_le_geomMult_of_dvd _ ω hdvd⟩)
    · obtain ⟨-, hfac, hdeg⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hβ)
      obtain ⟨-, hfac', hdeg'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hβ')
      have h' : β.coeff 0 = β'.coeff 0 := neg_inj.1 h
      calc β = X - C (-β.coeff 0) := eq_X_sub_C_of_monic hfac.1 hdeg
        _ = X - C (-β'.coeff 0) := by rw [h']
        _ = β' := (eq_X_sub_C_of_monic hfac'.1 hdeg').symm
  have hcard2 : (s.filter fun β => IsFactor p (seidelOf ω) β ∧ β.natDegree ≠ 1).card ≤ m :=
    card_factors_le _ _ fun β hβ => (Finset.mem_filter.1 hβ).2.1
  calc ((s.filter fun β => IsFactor p (seidelOf ω) β ∧ β.natDegree = 1).card : ℝ≥0∞) * ENNReal.ofReal c₁ +
        ((s.filter fun β => IsFactor p (seidelOf ω) β ∧ β.natDegree ≠ 1).card : ℝ≥0∞) *
          ENNReal.ofReal (bHigh p N m)
      ≤ (eigCount p ω : ℝ≥0∞) * ENNReal.ofReal c₁ + (m : ℝ≥0∞) * ENNReal.ofReal (bHigh p N m) := by
        gcongr
    _ = ENNReal.ofReal (c₁ * eigCount p ω + m * bHigh p N m) := by
        rw [ENNReal.ofReal_add (mul_nonneg hc₁0 (Nat.cast_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) hb0),
          ENNReal.ofReal_mul hc₁0, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_natCast, mul_comm (ENNReal.ofReal c₁)]

theorem expect_eigCount (m : ℕ) :
    expect (fun ω : Pairs m → Bool => (eigCount p ω : ℝ)) =
      ∑ μ : ZMod p, prob (fun ω : Pairs m → Bool => 1 ≤ geomMult (F := ZMod p) 1 (-1) μ ω) := by
  classical
  have h : ∀ ω : Pairs m → Bool, (eigCount p ω : ℝ) =
      ∑ μ : ZMod p, if 1 ≤ geomMult (F := ZMod p) 1 (-1) μ ω then (1 : ℝ) else 0 := by
    intro ω
    rw [eigCount, Finset.sum_boole]
  rw [expect_congr h, expect_sum]
  exact Finset.sum_congr rfl fun μ _ => expect_indicator _

theorem expectNall_le {N : ℕ} (H : HighHyp N m p) :
    expectNall p m {T | GoodAll T} ≤ ENNReal.ofReal ((1 / (p : ℝ) + Real.exp (-2 * cSE * m)) *
      (∑ μ : ZMod p, prob (fun ω : Pairs m → Bool => 1 ≤ geomMult (F := ZMod p) 1 (-1) μ ω)) +
        m * bHigh p N m) := by
  classical
  set c₁ : ℝ := 1 / (p : ℝ) + Real.exp (-2 * cSE * m) with hc₁
  set f : (Pairs m → Bool) → ℝ := fun ω => c₁ * eigCount p ω + m * bHigh p N m with hf
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => by
    have := bHigh_nonneg p N m
    positivity
  have hpt : ∀ ω : Pairs m → Bool, (if seidelOf ω ∈ {T | GoodAll T} then Nall p (seidelOf ω) else 0) ≤
      ENNReal.ofReal (f ω) := by
    intro ω
    split_ifs with hG
    · exact Nall_le_of_goodAll H ω hG
    · exact zero_le
  have hpos : (0 : ℝ) < Fintype.card (Pairs m → Bool) := by exact_mod_cast Fintype.card_pos
  have hexp : expect f = c₁ * ∑ μ : ZMod p, prob (fun ω : Pairs m → Bool =>
      1 ≤ geomMult (F := ZMod p) 1 (-1) μ ω) + m * bHigh p N m := by
    rw [hf, expect_add, expect_const_mul, expect_eigCount, expect_const]
  rw [expectNall, ← hexp, expect, ENNReal.ofReal_div_of_pos hpos,
    ENNReal.ofReal_sum_of_nonneg (fun ω _ => hf0 ω), ENNReal.ofReal_natCast]
  exact ENNReal.div_le_div_right (Finset.sum_le_sum fun ω _ => hpt ω) _

end Pointwise

section Asymptotics

theorem tendsto_pow_mul_exp_neg_nat {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ k * Real.exp (-c * N)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc)
  have h2 := h.const_mul ((c ^ k)⁻¹)
  rw [mul_zero] at h2
  refine h2.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [mul_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hc.ne'), one_mul, neg_mul]

theorem tendsto_pow_mul_exp_neg_pred {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ k * Real.exp (-c * ((N : ℝ) - 1))) atTop (𝓝 0) := by
  have h := (tendsto_pow_mul_exp_neg_nat hc k).const_mul (Real.exp c)
  rw [mul_zero] at h
  refine h.congr fun N => ?_
  rw [show -c * ((N : ℝ) - 1) = c + -c * N by ring, Real.exp_add]
  ring

noncomputable def uBound (N : ℕ) : ℝ :=
  (1 / (N : ℝ) + Real.exp (-2 * cSE * ((N : ℝ) - 1))) *
      (1 + 1.2 / (N : ℝ) + 2 * N * Real.exp (-cRK * ((N : ℝ) - 1))) +
    N * (((N : ℝ) ^ 2)⁻¹ + Real.exp (-2 * cSEd * ((N : ℝ) - 1)) +
      (2 * (N : ℝ) ^ (-(1 / 2 - 1 / 20 : ℝ))) ^ 5 + ((N : ℝ) ^ 3)⁻¹)

theorem tendsto_uBound : Tendsto uBound atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have he1 : Tendsto (fun N : ℕ => Real.exp (-2 * cSE * ((N : ℝ) - 1))) atTop (𝓝 0) := by
    have := tendsto_pow_mul_exp_neg_pred (c := 2 * cSE) (by have := cSE_pos; positivity) 0
    simpa [neg_mul] using this
  have hA : Tendsto (fun N : ℕ => 1 / (N : ℝ) + Real.exp (-2 * cSE * ((N : ℝ) - 1))) atTop (𝓝 0) := by
    simpa using hinv.add he1
  have hB : Tendsto (fun N : ℕ => 1 + 1.2 / (N : ℝ) + 2 * N * Real.exp (-cRK * ((N : ℝ) - 1))) atTop
      (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ => 1.2 / (N : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat 1.2
    have h2 := (tendsto_pow_mul_exp_neg_pred cRK_pos 1).const_mul 2
    have h3 := ((tendsto_const_nhds (x := (1 : ℝ))).add h1).add h2
    rw [add_zero, mul_zero, add_zero] at h3
    refine h3.congr fun N => ?_
    rw [pow_one]
    ring
  have hC1 : Tendsto (fun N : ℕ => (N : ℝ) * ((N : ℝ) ^ 2)⁻¹) atTop (𝓝 0) := by
    refine hinv.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  have hC2 : Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-2 * cSEd * ((N : ℝ) - 1))) atTop (𝓝 0) := by
    have := tendsto_pow_mul_exp_neg_pred (c := 2 * cSEd) (by have := cSEd_pos; positivity) 1
    refine this.congr fun N => ?_
    simp only [pow_one, neg_mul]
  have hC3 : Tendsto (fun N : ℕ => (N : ℝ) * (2 * (N : ℝ) ^ (-(1 / 2 - 1 / 20 : ℝ))) ^ 5) atTop (𝓝 0) := by
    have hd := tendsto_deg5_bound (ε := 1 / 20) (by norm_num)
    have hd3 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (3 * (N : ℝ) ^ 2 * (2 * (N : ℝ) ^ (-(1 / 2 - 1 / 20 : ℝ))) ^ 5 / 3))
        atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul (hd.div_const 3)
      simpa using this
    refine hd3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  have hC4 : Tendsto (fun N : ℕ => (N : ℝ) * ((N : ℝ) ^ 3)⁻¹) atTop (𝓝 0) := by
    have h := hinv.mul hinv
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  have hC : Tendsto (fun N : ℕ => (N : ℝ) * (((N : ℝ) ^ 2)⁻¹ + Real.exp (-2 * cSEd * ((N : ℝ) - 1)) +
      (2 * (N : ℝ) ^ (-(1 / 2 - 1 / 20 : ℝ))) ^ 5 + ((N : ℝ) ^ 3)⁻¹)) atTop (𝓝 0) := by
    have := ((hC1.add hC2).add hC3).add hC4
    simp only [add_zero] at this
    refine this.congr fun N => ?_
    ring
  have := (hA.mul hB).add hC
  rw [zero_mul, zero_add] at this
  exact this

theorem eventually_two_mul_le_exp :
    ∀ᶠ N : ℕ in atTop, 2 * (N : ℝ) ≤ Real.exp (((N : ℝ) - 1) ^ (1 / 10 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (4 * Nat.factorial 20 + 2)] with N hN
  have hF : (0 : ℝ) < (Nat.factorial 20 : ℝ) := by exact_mod_cast Nat.factorial_pos 20
  have hNR : 4 * (Nat.factorial 20 : ℝ) + 2 ≤ N := by exact_mod_cast hN
  have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have hy0 : 0 ≤ ((N : ℝ) - 1) ^ (1 / 10 : ℝ) := Real.rpow_nonneg hN1 _
  have hy20 : (((N : ℝ) - 1) ^ (1 / 10 : ℝ)) ^ 20 = ((N : ℝ) - 1) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN1]
    norm_num
  have h1 := Real.pow_div_factorial_le_exp _ hy0 20
  rw [hy20] at h1
  have h2 : 2 * (N : ℝ) ≤ ((N : ℝ) - 1) ^ 2 / (Nat.factorial 20 : ℝ) := by
    rw [le_div_iff₀ hF]
    have h3 : (4 * (Nat.factorial 20 : ℝ) + 1) * ((N : ℝ) - 1) ≤ ((N : ℝ) - 1) * ((N : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hN1
    nlinarith
  linarith

theorem eventually_highHyp :
    ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p.Prime → N < p → p ≤ 2 * N → N - 1 ≤ m → m ≤ N →
      HighHyp N m p ∧ (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 9)) := by
  filter_upwards [deg5_eventually (ε := 1 / 20) (by norm_num) (by norm_num), eventually_two_mul_le_exp,
    eventually_ge_atTop 32] with N hN h2N hN32
  obtain ⟨hL1, hA, hC, hB, hD, h32, hE⟩ := hN
  intro p m hp hNp hp2N hm hmN
  have hN1R : (31 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (32 : ℝ) ≤ N := by exact_mod_cast hN32
    linarith
  have hmR : (N : ℝ) - 1 ≤ m := by
    have h1 : ((N - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at h1
  have hpR : (p : ℝ) ≤ 2 * N := by exact_mod_cast hp2N
  have hm1R : (1 : ℝ) ≤ m := by linarith
  have h10_9 : ((N : ℝ) - 1) ^ (1 / 10 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 9) :=
    (Real.rpow_le_rpow (by linarith) hmR (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hm1R (by norm_num))
  have h9_8 : (m : ℝ) ^ ((1 : ℝ) / 9) ≤ (m : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hm1R (by norm_num)
  have h10N : ((N : ℝ) - 1) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have hpe : (p : ℝ) ≤ Real.exp (((N : ℝ) - 1) ^ (1 / 10 : ℝ)) := hpR.trans h2N
  have hNp' : (N : ℝ) < p := by exact_mod_cast hNp
  have hN1 : (1 : ℝ) ≤ N := by linarith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hL1, hA, hC, hB, hD, h32, hE, hm, ?_, ?_⟩, ?_⟩
  · omega
  · omega
  · exact hpe.trans (Real.exp_le_exp.2 (h10_9.trans h9_8))
  · omega
  · omega
  · omega
  · calc (N : ℝ) ^ (1 / 2 - 1 / 20 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
      _ < p := hNp'
  · exact hpe.trans (Real.exp_le_exp.2 h10N)
  · exact hpe.trans (Real.exp_le_exp.2 h10_9)

end Asymptotics

section Conclusion

theorem tendsto_prob_not_goodAll :
    Tendsto (fun m : ℕ => probSeidel m (fun T => T ∉ {T : Matrix (Fin m) (Fin m) ℤ | GoodAll T})) atTop (𝓝 0) := by
  have hexp : ∀ {c : ℝ}, 0 < c → Tendsto (fun m : ℕ => Real.exp (-(m : ℝ) / c)) atTop (𝓝 0) := by
    intro c hc
    have := tendsto_pow_mul_exp_neg_nat (c := 1 / c) (by positivity) 0
    refine this.congr fun m => ?_
    rw [pow_zero, one_mul]
    congr 1
    ring
  have h2 : Tendsto (fun m : ℕ => (2 : ℝ) ^ (-(m : ℝ) / 8)) atTop (𝓝 0) := by
    have := hexp (c := 8 / Real.log 2) (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
    refine this.congr fun m => ?_
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    have := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    field_simp
  have hsum : Tendsto (fun m : ℕ => 2 * (2 : ℝ) ^ (-(m : ℝ) / 8) + 3 * Real.exp (-(m : ℝ) / 9) +
      Real.exp (-(m : ℝ) / 8)) atTop (𝓝 0) := by
    have := ((h2.const_mul 2).add ((hexp (by norm_num : (0 : ℝ) < 9)).const_mul 3)).add
      (hexp (by norm_num : (0 : ℝ) < 8))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => prob_nonneg _) ?_
  filter_upwards [thm_SEplus, prop_SEd (d := 2) (by norm_num) (by norm_num),
    prop_SEd (d := 3) (by norm_num) (by norm_num), prop_SEd (d := 4) (by norm_num) (by norm_num),
    prob_not_suppGoodPM] with m h1 h2' h3 h4 h5
  have hsub : ∀ ω : Pairs m → Bool, seidelOf ω ∉ {T : Matrix (Fin m) (Fin m) ℤ | GoodAll T} →
      (¬ GoodSE (seidelOf ω) ∨ ¬ GoodSEd 2 (seidelOf ω)) ∨ (¬ GoodSEd 3 (seidelOf ω) ∨
        ¬ GoodSEd 4 (seidelOf ω)) ∨ ¬ SuppGoodPM ω := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, GoodAll] at hω
    rw [← suppGoodS_seidelOf]
    tauto
  calc probSeidel m (fun T => T ∉ {T : Matrix (Fin m) (Fin m) ℤ | GoodAll T})
      ≤ prob (fun ω : Pairs m → Bool => (¬ GoodSE (seidelOf ω) ∨ ¬ GoodSEd 2 (seidelOf ω)) ∨
          (¬ GoodSEd 3 (seidelOf ω) ∨ ¬ GoodSEd 4 (seidelOf ω)) ∨ ¬ SuppGoodPM ω) := prob_mono hsub
    _ ≤ (probSeidel m (fun T => ¬ GoodSE T) + probSeidel m (fun T => ¬ GoodSEd 2 T)) +
          ((probSeidel m (fun T => ¬ GoodSEd 3 T) + probSeidel m (fun T => ¬ GoodSEd 4 T)) +
            prob (fun ω : Pairs m → Bool => ¬ SuppGoodPM ω)) :=
        (prob_or_le _ _).trans (add_le_add (prob_or_le _ _)
          ((prob_or_le _ _).trans (add_le_add (prob_or_le _ _) le_rfl)))
    _ ≤ (2 * (2 : ℝ) ^ (-(m : ℝ) / 8) + Real.exp (-(m : ℝ) / 9)) +
          ((Real.exp (-(m : ℝ) / 9) + Real.exp (-(m : ℝ) / 9)) + Real.exp (-(m : ℝ) / 8)) := by
        gcongr
    _ = _ := by ring

theorem eventually_expectNall_le :
    ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p.Prime → N < p → p ≤ 2 * N → N - 1 ≤ m → m ≤ N →
      expectNall p m {T | GoodAll T} ≤ ENNReal.ofReal (uBound N) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 thm_rankp
  filter_upwards [eventually_highHyp, eventually_ge_atTop (n₀ + 2)] with N hN hNn₀
  intro p m hp hNp hp2N hm hmN
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, hp9⟩ := hN p m hp hNp hp2N hm hmN
  refine (expectNall_le H).trans (ENNReal.ofReal_le_ofReal ?_)
  have hrank := hn₀ m (by omega) p H.hp23 hp9
  have hNR : (32 : ℝ) ≤ N := by exact_mod_cast H.h32
  have hmR : (N : ℝ) - 1 ≤ m := by
    have h1 : ((N - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at h1
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hpN : (N : ℝ) < p := by exact_mod_cast hNp
  have hp2NR : (p : ℝ) ≤ 2 * N := by exact_mod_cast hp2N
  have hp0 : (0 : ℝ) < p := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hE : ∑ μ : ZMod p, prob (fun ω : Pairs m → Bool => 1 ≤ geomMult (F := ZMod p) 1 (-1) μ ω) ≤
      1 + 1.2 / (N : ℝ) + 2 * N * Real.exp (-cRK * ((N : ℝ) - 1)) := by
    calc ∑ μ : ZMod p, prob (fun ω : Pairs m → Bool => 1 ≤ geomMult (F := ZMod p) 1 (-1) μ ω)
        ≤ ∑ _μ : ZMod p, (1 / (p : ℝ) + 1.2 / (p : ℝ) ^ 2 + Real.exp (-cRK * m)) :=
          Finset.sum_le_sum fun μ _ => (hrank μ).2
      _ = p * (1 / (p : ℝ) + 1.2 / (p : ℝ) ^ 2 + Real.exp (-cRK * m)) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      _ = 1 + 1.2 / (p : ℝ) + p * Real.exp (-cRK * m) := by
          field_simp
      _ ≤ 1 + 1.2 / (N : ℝ) + 2 * N * Real.exp (-cRK * ((N : ℝ) - 1)) := by
          have h1 : 1.2 / (p : ℝ) ≤ 1.2 / (N : ℝ) := div_le_div_of_nonneg_left (by norm_num) hN0 hpN.le
          have h2 : Real.exp (-cRK * m) ≤ Real.exp (-cRK * ((N : ℝ) - 1)) := by
            apply Real.exp_le_exp.2
            have := cRK_pos
            nlinarith
          have h3 : (p : ℝ) * Real.exp (-cRK * m) ≤ 2 * N * Real.exp (-cRK * ((N : ℝ) - 1)) :=
            mul_le_mul hp2NR h2 (Real.exp_pos _).le (by positivity)
          linarith
  have hc₁ : 1 / (p : ℝ) + Real.exp (-2 * cSE * m) ≤ 1 / (N : ℝ) + Real.exp (-2 * cSE * ((N : ℝ) - 1)) := by
    have h1 : 1 / (p : ℝ) ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hN0 hpN.le
    have h2 : Real.exp (-2 * cSE * m) ≤ Real.exp (-2 * cSE * ((N : ℝ) - 1)) := by
      apply Real.exp_le_exp.2
      have := cSE_pos
      nlinarith
    linarith
  have hb : (m : ℝ) * bHigh p N m ≤ N * (((N : ℝ) ^ 2)⁻¹ + Real.exp (-2 * cSEd * ((N : ℝ) - 1)) +
      (2 * (N : ℝ) ^ (-(1 / 2 - 1 / 20 : ℝ))) ^ 5 + ((N : ℝ) ^ 3)⁻¹) := by
    unfold bHigh
    have h1 : ((p : ℝ) ^ 2)⁻¹ ≤ ((N : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) (by gcongr)
    have h2 : Real.exp (-2 * cSEd * m) ≤ Real.exp (-2 * cSEd * ((N : ℝ) - 1)) := by
      apply Real.exp_le_exp.2
      have := cSEd_pos
      nlinarith
    have h0 : 0 ≤ ((p : ℝ) ^ 2)⁻¹ + Real.exp (-2 * cSEd * m) + (2 * (N : ℝ) ^ (-(1 / 2 - 1 / 20 : ℝ))) ^ 5 +
        ((N : ℝ) ^ 3)⁻¹ := by positivity
    calc (m : ℝ) * (((p : ℝ) ^ 2)⁻¹ + Real.exp (-2 * cSEd * m) + (2 * (N : ℝ) ^ (-(1 / 2 - 1 / 20 : ℝ))) ^ 5 +
          ((N : ℝ) ^ 3)⁻¹)
        ≤ N * (((p : ℝ) ^ 2)⁻¹ + Real.exp (-2 * cSEd * m) + (2 * (N : ℝ) ^ (-(1 / 2 - 1 / 20 : ℝ))) ^ 5 +
          ((N : ℝ) ^ 3)⁻¹) := mul_le_mul_of_nonneg_right hmN' h0
      _ ≤ _ := by gcongr
  have hE0 : 0 ≤ ∑ μ : ZMod p, prob (fun ω : Pairs m → Bool => 1 ≤ geomMult (F := ZMod p) 1 (-1) μ ω) :=
    Finset.sum_nonneg fun _ _ => prob_nonneg _
  unfold uBound
  have hc0 : 0 ≤ 1 / (p : ℝ) + Real.exp (-2 * cSE * m) := by positivity
  calc (1 / (p : ℝ) + Real.exp (-2 * cSE * m)) *
        (∑ μ : ZMod p, prob (fun ω : Pairs m → Bool => 1 ≤ geomMult (F := ZMod p) 1 (-1) μ ω)) +
        m * bHigh p N m
      ≤ (1 / (N : ℝ) + Real.exp (-2 * cSE * ((N : ℝ) - 1))) *
          (1 + 1.2 / (N : ℝ) + 2 * N * Real.exp (-cRK * ((N : ℝ) - 1))) +
        N * (((N : ℝ) ^ 2)⁻¹ + Real.exp (-2 * cSEd * ((N : ℝ) - 1)) +
          (2 * (N : ℝ) ^ (-(1 / 2 - 1 / 20 : ℝ))) ^ 5 + ((N : ℝ) ^ 3)⁻¹) := by
        gcongr

noncomputable def corePrime (N : ℕ) : ℕ :=
  if h : 2 ≤ N then Classical.choose (Nat.exists_prime_lt_and_le_two_mul N (by omega)) else 3

theorem corePrime_spec (N : ℕ) : (corePrime N).Prime ∧ corePrime N ≠ 2 ∧
    (2 ≤ N → N < corePrime N ∧ corePrime N ≤ 2 * N) := by
  unfold corePrime
  split_ifs with h
  · obtain ⟨hp, h1, h2⟩ := Classical.choose_spec (Nat.exists_prime_lt_and_le_two_mul N (by omega))
    exact ⟨hp, by omega, fun _ => ⟨h1, h2⟩⟩
  · exact ⟨Nat.prime_three, by norm_num, fun h' => absurd h' h⟩

theorem tendsto_prob_notCyc :
    Tendsto (fun N : ℕ => prob (fun x : (Pairs N → Bool) × (Fin N → Bool) =>
      NotCyc (corePrime N) (seidelOf x.1) (signVec x.2))) atTop (𝓝 0) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  set G : ∀ m, Set (Matrix (Fin m) (Fin m) ℤ) := fun m => {T | GoodAll T} with hG
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
  have hGt := tendsto_prob_not_goodAll
  have hE1 : Tendsto (fun n => expectNall (corePrime (n + 1)) (n + 1) (G (n + 1))) atTop (𝓝 0) := by
    have hlim := hof (hsh tendsto_uBound)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    have hev := (tendsto_add_atTop_nat 1).eventually eventually_expectNall_le
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    obtain ⟨hp, -, hpN⟩ := corePrime_spec (n + 1)
    obtain ⟨h1, h2⟩ := hpN (by omega)
    exact hn _ _ hp h1 h2 (by omega) le_rfl
  have hE0 : Tendsto (fun n => expectNall (corePrime (n + 1)) n (G n)) atTop (𝓝 0) := by
    have hlim := hof (hsh tendsto_uBound)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    have hev := (tendsto_add_atTop_nat 1).eventually eventually_expectNall_le
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    obtain ⟨hp, -, hpN⟩ := corePrime_spec (n + 1)
    obtain ⟨h1, h2⟩ := hpN (by omega)
    exact hn _ _ hp h1 h2 (by omega) (by omega)
  have hbound : Tendsto (fun n => ENNReal.ofReal (probSeidel (n + 1) (fun S => S ∉ G (n + 1))) +
      expectNall (corePrime (n + 1)) (n + 1) (G (n + 1)) +
      20 * (ENNReal.ofReal (probSeidel n (fun S => S ∉ G n)) + expectNall (corePrime (n + 1)) n (G n)) +
      ENNReal.ofReal (probSeidel (n + 1) (fun S => ¬ SuppGood S))) atTop (𝓝 0) := by
    have h20 := ENNReal.Tendsto.const_mul ((hof hGt).add hE0) (Or.inr (by norm_num : (20 : ℝ≥0∞) ≠ ⊤))
    have := (((hof (hsh hGt)).add hE1).add h20).add (hof (hsh hS))
    rw [show (0 : ℝ≥0∞) + 0 + 20 * (0 + 0) + 0 = 0 by simp] at this
    exact this
  have hle : ∀ n, ENNReal.ofReal (prob (fun x : (Pairs (n + 1) → Bool) × (Fin (n + 1) → Bool) =>
      NotCyc (corePrime (n + 1)) (seidelOf x.1) (signVec x.2))) ≤
      ENNReal.ofReal (probSeidel (n + 1) (fun S => S ∉ G (n + 1))) +
        expectNall (corePrime (n + 1)) (n + 1) (G (n + 1)) +
        20 * (ENNReal.ofReal (probSeidel n (fun S => S ∉ G n)) + expectNall (corePrime (n + 1)) n (G n)) +
        ENNReal.ofReal (probSeidel (n + 1) (fun S => ¬ SuppGood S)) := by
    intro n
    obtain ⟨hp, hp2, -⟩ := corePrime_spec (n + 1)
    have : Fact (corePrime (n + 1)).Prime := ⟨hp⟩
    exact core_bound hp2 n (G (n + 1)) (G n)
  have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound (fun _ => zero_le) hle
  have hreal := (ENNReal.tendsto_toReal (ENNReal.zero_ne_top)).comp hlim
  simp only [ENNReal.toReal_zero] at hreal
  refine hreal.congr fun n => ?_
  rw [Function.comp_apply, ENNReal.toReal_ofReal (prob_nonneg _)]

end Conclusion

end DGS
