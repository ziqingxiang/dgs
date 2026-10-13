module

public import DGS.S11_Deg1.Isocond
public import DGS.S04_Reduction.LargeDegrees
public import Mathlib.Analysis.PSeries

@[expose] public section

open Finset Filter Topology Matrix Polynomial
open scoped Real ENNReal

namespace DGS

theorem sgnSum_eq_twoValued_dot {p m : ℕ} (w : Fin m → ZMod p) (ξ : Fin m → Bool) :
    sgnSum w ξ = twoValued (1 : ZMod p) (-1) ξ ⬝ᵥ w := by
  unfold sgnSum dotProduct twoValued
  refine Finset.sum_congr rfl fun j _ => ?_
  cases ξ j <;> simp

theorem abeta_deg1_le {m : ℕ} {T : Matrix (Fin m) (Fin m) ℤ} (hT : GoodSE T) {p : ℕ} [Fact p.Prime]
    (hp23 : 23 ≤ p) (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) (μ : ZMod p) :
    abeta p T (X - C μ) ≤ 1 / p + Real.exp (-2 * cSE * m) := by
  have hb0 : 0 ≤ 1 / (p : ℝ) + Real.exp (-2 * cSE * m) := by positivity
  refine Real.sSup_le ?_ hb0
  rintro x ⟨U, hU, hβ, rfl⟩
  obtain ⟨w, hwU, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.2.1
  have hw : T.map (Int.castRingHom (ZMod p)) *ᵥ w = μ • w := by
    have h := hβ.2.2 w hwU
    rw [aeval_X_sub_C, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at h
    exact h
  calc probPerp p U ≤ prob (fun ξ : Fin m → Bool => sgnSum w ξ = 0) := by
        unfold probPerp
        refine prob_mono fun ξ h => ?_
        have h1 := h w hwU
        rw [modPVec_signVec] at h1
        rw [sgnSum_eq_twoValued_dot]
        exact h1
    _ ≤ rhoG w := prob_sgnSum_le_rhoG w 0
    _ ≤ 1 / p + Real.exp (-2 * cSE * m) := cor_ACplus hT hp23 hpm hw0 hw

open Classical in
noncomputable def wDeg1 {m : ℕ} (Pfin : Finset ℕ) (T : Matrix (Fin m) (Fin m) ℤ)
    (x : Σ p : ℕ, (ZMod p)[X]) : ℝ≥0∞ :=
  if x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = 1 ∧ x.2 ^ 2 ∣ (modP x.1 T).charpoly then
    ENNReal.ofReal (1 / x.1 + Real.exp (-2 * cSE * m)) else 0

theorem NPi_deg1_le {m : ℕ} (PS : Set (ℕ × ℕ)) (Pfin : Finset ℕ) (hPS : ∀ x ∈ PS, x.1 ∈ Pfin ∧ x.2 = 1)
    (hPfin : ∀ p ∈ Pfin, p.Prime ∧ 23 ≤ p ∧ (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    {T : Matrix (Fin m) (Fin m) ℤ} (hT : GoodSE T) :
    NPi PS T ≤ ∑' x, wDeg1 Pfin T x := by
  classical
  unfold NPi
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases h1 : (x.1, x.2.natDegree) ∈ PS ∧ IsRepeatedFactor x.1 T x.2
  · rw [ite_eq_left h1]
    obtain ⟨hP, hdeg⟩ := hPS _ h1.1
    obtain ⟨hmon, -, hdvd⟩ := h1.2
    obtain ⟨hp, hp23, hpm⟩ := hPfin _ hP
    have : Fact x.1.Prime := ⟨hp⟩
    have hcond : x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = 1 ∧ x.2 ^ 2 ∣ (modP x.1 T).charpoly :=
      ⟨hP, hmon, hdeg, hdvd⟩
    unfold wDeg1
    rw [ite_eq_left hcond]
    apply ENNReal.ofReal_le_ofReal
    have hx2 : x.2 = X - C (-(x.2.coeff 0)) := by
      rw [map_neg C, sub_neg_eq_add]
      exact Monic.eq_X_add_C hmon hdeg
    calc abeta x.1 T x.2 = abeta x.1 T (X - C (-(x.2.coeff 0))) := by rw [← hx2]
      _ ≤ 1 / x.1 + Real.exp (-2 * cSE * m) := abeta_deg1_le hT hp23 hpm _
  · rw [ite_eq_right h1]
    exact zero_le

theorem expectNPi_deg1_le {m : ℕ} (PS : Set (ℕ × ℕ)) (Pfin : Finset ℕ)
    (hPS : ∀ x ∈ PS, x.1 ∈ Pfin ∧ x.2 = 1)
    (hPfin : ∀ p ∈ Pfin, p.Prime ∧ 23 ≤ p ∧ (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (B : ℕ → ℝ) (hB : ∀ p ∈ Pfin, ∀ [Fact p.Prime], ∑ μ : ZMod p,
      prob (fun ω : Pairs m → Bool => (X - C μ) ^ 2 ∣ (modP p (seidelOf ω)).charpoly) ≤ B p) :
    expectNPi PS m {T | GoodSE T} ≤
      ∑ p ∈ Pfin, ENNReal.ofReal ((1 / p + Real.exp (-2 * cSE * m)) * B p) := by
  classical
  set card : ℝ≥0∞ := (Fintype.card (Pairs m → Bool) : ℝ≥0∞) with hcard
  set w : (Pairs m → Bool) → (Σ p : ℕ, (ZMod p)[X]) → ℝ≥0∞ := fun ω x => wDeg1 Pfin (seidelOf ω) x with hw
  have hA : ∀ ω : Pairs m → Bool, (if seidelOf ω ∈ {T : Matrix (Fin m) (Fin m) ℤ | GoodSE T}
      then NPi PS (seidelOf ω) else 0) ≤ ∑' x, w ω x := by
    intro ω
    split_ifs with h
    · exact NPi_deg1_le PS Pfin hPS hPfin h
    · exact zero_le
  set c : ℕ → ℝ := fun p => 1 / p + Real.exp (-2 * cSE * m) with hc
  have hc0 : ∀ p, 0 ≤ c p := fun p => by rw [hc]; positivity
  have hC : ∀ x : (Σ p : ℕ, (ZMod p)[X]), (∑ ω, w ω x) / card =
      if x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = 1 then
        ENNReal.ofReal (c x.1) * ENNReal.ofReal
          (prob (fun ω : Pairs m → Bool => x.2 ^ 2 ∣ (modP x.1 (seidelOf ω)).charpoly)) else 0 := by
    intro x
    by_cases hx : x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = 1
    · rw [ite_eq_left hx, ofReal_prob_eq, ← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [hw]
      simp only [wDeg1]
      by_cases hd : x.2 ^ 2 ∣ (modP x.1 (seidelOf ω)).charpoly
      · rw [ite_eq_left ⟨hx.1, hx.2.1, hx.2.2, hd⟩, ite_eq_left hd, mul_one]
      · rw [ite_eq_right (fun h => hd h.2.2.2), ite_eq_right hd, mul_zero]
    · rw [ite_eq_right hx]
      have h0 : ∀ ω, w ω x = 0 := by
        intro ω
        rw [hw]
        simp only [wDeg1]
        rw [ite_eq_right (fun h => hx ⟨h.1, h.2.1, h.2.2.1⟩)]
      simp [h0]
  have hD : ∀ p ∈ Pfin, ∑' β : (ZMod p)[X], (if p ∈ Pfin ∧ β.Monic ∧ β.natDegree = 1 then
      ENNReal.ofReal (c p) * ENNReal.ofReal
        (prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)) else 0) ≤
      ENNReal.ofReal (c p * B p) := by
    intro p hp
    have : Fact p.Prime := ⟨(hPfin p hp).1⟩
    set f : (ZMod p)[X] → ℝ≥0∞ := fun β => if p ∈ Pfin ∧ β.Monic ∧ β.natDegree = 1 then
      ENNReal.ofReal (c p) * ENNReal.ofReal
        (prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)) else 0 with hf
    have hinj : Function.Injective (fun μ : ZMod p => X - C μ) := by
      intro μ μ' h
      have := congrArg (Polynomial.eval 0) h
      simpa using this
    have hsupp : Function.support f ⊆ Set.range (fun μ : ZMod p => X - C μ) := by
      intro β hβ
      rw [Function.mem_support, hf] at hβ
      simp only at hβ
      split_ifs at hβ with h
      · refine ⟨-(β.coeff 0), ?_⟩
        simp only
        rw [map_neg C, sub_neg_eq_add]
        exact (Monic.eq_X_add_C h.2.1 h.2.2).symm
      · exact absurd rfl hβ
    rw [← hinj.tsum_eq hsupp, tsum_fintype]
    have hterm : ∀ μ : ZMod p, f (X - C μ) = ENNReal.ofReal (c p) * ENNReal.ofReal
        (prob (fun ω : Pairs m → Bool => (X - C μ) ^ 2 ∣ (modP p (seidelOf ω)).charpoly)) := by
      intro μ
      rw [hf]
      simp only
      rw [ite_eq_left ⟨hp, monic_X_sub_C μ, natDegree_X_sub_C μ⟩]
    simp only [hterm]
    rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun μ _ => prob_nonneg _),
      ← ENNReal.ofReal_mul (hc0 p)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hB p hp) (hc0 p))
  rw [expectNPi]
  calc (∑ ω : Pairs m → Bool, if seidelOf ω ∈ {T : Matrix (Fin m) (Fin m) ℤ | GoodSE T}
        then NPi PS (seidelOf ω) else 0) / card
      ≤ (∑ ω : Pairs m → Bool, ∑' x, w ω x) / card := by
        gcongr with ω
        exact hA ω
    _ = ∑' x, (∑ ω, w ω x) / card := by
        rw [← Summable.tsum_finsetSum (fun ω _ => ENNReal.summable), div_eq_mul_inv,
          ← ENNReal.tsum_mul_right]
        rfl
    _ = ∑' x : (Σ p : ℕ, (ZMod p)[X]), (if x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = 1 then
          ENNReal.ofReal (c x.1) * ENNReal.ofReal
            (prob (fun ω : Pairs m → Bool => x.2 ^ 2 ∣ (modP x.1 (seidelOf ω)).charpoly)) else 0) := by
        congr 1
        funext x
        exact hC x
    _ = ∑' p : ℕ, ∑' β : (ZMod p)[X], (if p ∈ Pfin ∧ β.Monic ∧ β.natDegree = 1 then
          ENNReal.ofReal (c p) * ENNReal.ofReal
            (prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)) else 0) :=
        ENNReal.tsum_sigma' _
    _ = ∑ p ∈ Pfin, ∑' β : (ZMod p)[X], (if p ∈ Pfin ∧ β.Monic ∧ β.natDegree = 1 then
          ENNReal.ofReal (c p) * ENNReal.ofReal
            (prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)) else 0) := by
        refine tsum_eq_sum fun p hp => ?_
        simp [hp]
    _ ≤ ∑ p ∈ Pfin, ENNReal.ofReal (c p * B p) := Finset.sum_le_sum hD

def PSdeg1 (ε : ℝ) (n : ℕ) : Set (ℕ × ℕ) :=
  {x | x.1.Prime ∧ x.1 ≠ 2 ∧ (n : ℝ) ^ (1 / 2 - ε) < (x.1 : ℝ) ∧
    (x.1 : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧ x.2 = 1}

noncomputable def PfinDeg1 (ε : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Ioo ⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ (⌊Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))⌋₊ + 1)).filter Nat.Prime

theorem mem_PfinDeg1 {ε : ℝ} {N : ℕ} {x : ℕ × ℕ} (hx : x ∈ PSdeg1 ε N) :
    x.1 ∈ PfinDeg1 ε N ∧ x.2 = 1 := by
  obtain ⟨hp, -, h1, h2, h3⟩ := hx
  refine ⟨Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨?_, ?_⟩, hp⟩, h3⟩
  · exact (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg _) _)).2 h1
  · have := Nat.le_floor h2
    omega

theorem expectNPi_deg1_bound {ε : ℝ} {N m : ℕ} (hm1 : 1 ≤ m)
    (hIC : ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 9)) →
      ∑ μ : ZMod p, prob (fun ω : Pairs m → Bool => (X - C μ) ^ 2 ∣ (modP p (seidelOf ω)).charpoly) ≤
        3.5 / p + Real.exp (-cRK * m))
    (h22 : 22 ≤ ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊) (hNm : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 9)) :
    expectNPi (PSdeg1 ε N) m {T | GoodSE T} ≤
      ENNReal.ofReal (7 / (⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ + 1) +
        6 * Real.exp (-cRK * m) * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1)) := by
  classical
  set a := ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ with ha
  set b := ⌊Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))⌋₊ + 1 with hb
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have h98 : (m : ℝ) ^ ((1 : ℝ) / 9) ≤ (m : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hm1R (by norm_num)
  have hPfin : ∀ p ∈ PfinDeg1 ε N, p.Prime ∧ 23 ≤ p ∧ (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 9)) := by
    intro p hp
    obtain ⟨hIoo, hpr⟩ := Finset.mem_filter.1 hp
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.1 hIoo
    refine ⟨hpr, by omega, ?_⟩
    have h3 : p ≤ ⌊Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))⌋₊ := by omega
    have h4 : (p : ℝ) ≤ Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) :=
      (Nat.le_floor_iff (Real.exp_pos _).le).1 h3
    exact h4.trans (Real.exp_le_exp.2 hNm)
  have h := expectNPi_deg1_le (PSdeg1 ε N) (PfinDeg1 ε N) (fun x hx => mem_PfinDeg1 hx)
    (fun p hp => ⟨(hPfin p hp).1, (hPfin p hp).2.1, (hPfin p hp).2.2.trans (Real.exp_le_exp.2 h98)⟩)
    (fun p => 3.5 / p + Real.exp (-cRK * m))
    (fun p hp _ => hIC p (hPfin p hp).2.1 (hPfin p hp).2.2)
  refine h.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  set e := Real.exp (-2 * cSE * m) with he
  set e' := Real.exp (-cRK * m) with he'
  have hee' : e ≤ e' := by
    apply Real.exp_le_exp.2
    have := cRK_le
    have := cRK_pos
    unfold cSE
    nlinarith
  have he'1 : e' ≤ 1 := by
    rw [he']
    apply Real.exp_le_one_iff.2
    have := cRK_pos
    nlinarith
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hterm : ∀ p ∈ PfinDeg1 ε N, (1 / (p : ℝ) + e) * (3.5 / p + e') ≤ 3.5 * ((p : ℝ) ^ 2)⁻¹ + 6 * e' := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hPfin p hp).1.one_lt.le
    have hp0 : (0 : ℝ) < p := by linarith
    have hinv : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; exact hp1
    have hinv0 : 0 ≤ 1 / (p : ℝ) := by positivity
    have e1 : (1 / (p : ℝ) + e) * (3.5 / p + e') = 3.5 * ((p : ℝ) ^ 2)⁻¹ + (1 / p) * e' + 3.5 * (1 / p) * e +
        e * e' := by
      field_simp
      ring
    rw [e1]
    have := mul_le_mul hinv hee' he0 zero_le_one
    nlinarith [mul_le_mul_of_nonneg_left hinv (by linarith : (0 : ℝ) ≤ e'),
      mul_le_mul_of_nonneg_left he'1 he0]
  have hsq : ∑ p ∈ PfinDeg1 ε N, ((p : ℝ) ^ 2)⁻¹ ≤ 2 / (a + 1) := by
    calc ∑ p ∈ PfinDeg1 ε N, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ p ∈ Finset.Ioo a b, ((p : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
      _ ≤ 2 / (a + 1) := sum_Ioo_inv_sq_le a b
  have hcard : ((PfinDeg1 ε N).card : ℝ) ≤ Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1 := by
    have h1 : (PfinDeg1 ε N).card ≤ b := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Nat.card_Ioo]
      omega
    have h2 : (b : ℝ) ≤ Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1 := by
      rw [hb]
      push_cast
      have := Nat.floor_le (Real.exp_pos ((N : ℝ) ^ (1 / 10 : ℝ))).le
      linarith
    exact (by exact_mod_cast h1 : ((PfinDeg1 ε N).card : ℝ) ≤ b).trans h2
  calc ∑ p ∈ PfinDeg1 ε N, (1 / (p : ℝ) + e) * (3.5 / p + e')
      ≤ ∑ p ∈ PfinDeg1 ε N, (3.5 * ((p : ℝ) ^ 2)⁻¹ + 6 * e') := Finset.sum_le_sum hterm
    _ = 3.5 * ∑ p ∈ PfinDeg1 ε N, ((p : ℝ) ^ 2)⁻¹ + (PfinDeg1 ε N).card * (6 * e') := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3.5 * (2 / (a + 1)) + (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) * (6 * e') := by
        gcongr
    _ = 7 / (a + 1) + 6 * e' * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) := by ring

theorem eventually_rpow_tenth_succ_le_mul {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ c * n := by
  filter_upwards [eventually_ge_atTop (⌈2 / c ^ 2⌉₊ + 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have h1 : ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h1
  have h2 : 2 / c ^ 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈2 / c ^ 2⌉₊ ≤ n))
  have h3 : √((n : ℝ) + 1) ≤ c * n := by
    rw [Real.sqrt_le_left (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h2
    nlinarith
  exact h1.trans h3

theorem eventually_rpow_tenth_succ_le_ninth :
    ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 9) := by
  filter_upwards [eventually_ge_atTop 512] with n hn
  have hnR : (512 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (2 * (n : ℝ)) ^ (1 / 10 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h2 : (2 * (n : ℝ)) ^ (1 / 10 : ℝ) = (2 : ℝ) ^ (1 / 10 : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ) :=
    Real.mul_rpow (by norm_num) hn0.le
  have h3 : (2 : ℝ) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 90) := by
    have h := Real.rpow_le_rpow (by norm_num) hnR (by norm_num : (0 : ℝ) ≤ 1 / 90)
    have e : (512 : ℝ) ^ ((1 : ℝ) / 90) = (2 : ℝ) ^ (1 / 10 : ℝ) := by
      rw [show (512 : ℝ) = 2 ^ (9 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [e] at h
  have h4 : (n : ℝ) ^ ((1 : ℝ) / 90) * (n : ℝ) ^ (1 / 10 : ℝ) = (n : ℝ) ^ ((1 : ℝ) / 9) := by
    rw [← Real.rpow_add hn0]
    norm_num
  have h5 : 0 ≤ (n : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg hn0.le _
  calc ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (2 : ℝ) ^ (1 / 10 : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ) := h1.trans (le_of_eq h2)
    _ ≤ (n : ℝ) ^ ((1 : ℝ) / 90) * (n : ℝ) ^ (1 / 10 : ℝ) := mul_le_mul_of_nonneg_right h3 h5
    _ = (n : ℝ) ^ ((1 : ℝ) / 9) := h4

theorem prop_deg1_of
    (hPT : ∀ᶠ m : ℕ in atTop, probSeidel m (fun T => ¬ GoodPT T) ≤ Real.exp (-(m : ℝ) / 200))
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    Tendsto (fun n : ℕ => probG n (fun G => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ) ∧ (p : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧ E p 1 G))
      atTop (𝓝 0) := by
  classical
  set G : ∀ n, Set (Matrix (Fin n) (Fin n) ℤ) := fun n => {T | GoodSE T} with hGdef
  have hG : Tendsto (fun n => probSeidel n (fun S => S ∉ G n)) atTop (𝓝 0) := by
    have hu : Tendsto (fun n : ℕ => 2 * (2 : ℝ) ^ (-(n : ℝ) / 8)) atTop (𝓝 0) := by
      have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 8 : ℝ)) := by positivity
      have hr1 : (2 : ℝ) ^ (-(1 / 8 : ℝ)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul 2
      rw [mul_zero] at h
      refine h.congr fun n => ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 2
      ring
    refine tendsto_prob_zero_of_le hu ?_
    filter_upwards [thm_SEplus] with n hn
    exact le_trans (le_of_eq (prob_congr fun ω => by simp [hGdef])) hn
  set a : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ with ha
  have ha_tend : Tendsto a atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 / 2 - ε)).comp
      tendsto_natCast_atTop_atTop)
  set U : ℕ → ℝ := fun n => 7 / ((a n : ℝ) + 1) + 12 * Real.exp (-(cRK / 2) * n) with hU
  have hU0 : Tendsto U atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => 7 / ((a n : ℝ) + 1)) atTop (𝓝 0) := by
      have : Tendsto (fun n => (a n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp ha_tend)
      exact this.const_div_atTop 7
    have h2 : Tendsto (fun n : ℕ => 12 * Real.exp (-(cRK / 2) * n)) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n : ℕ => -(cRK / 2) * (n : ℝ)) atTop atBot :=
        (tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg (by have := cRK_pos; linarith)
      have h4 := (Real.tendsto_exp_atBot.comp h3).const_mul 12
      rw [mul_zero] at h4
      exact h4
    have := h1.add h2
    rw [add_zero] at this
    exact this
  have hmono : ∀ n, a n ≤ a (n + 1) := by
    intro n
    apply Nat.floor_le_floor
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) (by push_cast; linarith) (by linarith)
  have hev : ∀ᶠ n : ℕ in atTop, 22 ≤ a n ∧ 1 ≤ n ∧
      ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ cRK / 2 * n ∧
      ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 9) := by
    filter_upwards [ha_tend.eventually_ge_atTop 22, eventually_ge_atTop 1,
      eventually_rpow_tenth_succ_le_mul (by have := cRK_pos; positivity : 0 < cRK / 2),
      eventually_rpow_tenth_succ_le_ninth] with n h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hIC := prop_isocond_of hPT
  have hexp : ∀ n : ℕ, ∀ x : ℝ, x ≤ cRK / 2 * n →
      6 * Real.exp (-cRK * n) * (Real.exp x + 1) ≤ 12 * Real.exp (-(cRK / 2) * n) := by
    intro n x hx
    have h1 : Real.exp x + 1 ≤ 2 * Real.exp (cRK / 2 * n) := by
      have h2 : Real.exp x ≤ Real.exp (cRK / 2 * n) := Real.exp_le_exp.2 hx
      have h3 : (1 : ℝ) ≤ Real.exp (cRK / 2 * n) :=
        Real.one_le_exp (by have := cRK_pos; positivity)
      linarith
    have e : Real.exp (-cRK * n) * Real.exp (cRK / 2 * n) = Real.exp (-(cRK / 2) * n) := by
      rw [← Real.exp_add]
      ring_nf
    calc 6 * Real.exp (-cRK * n) * (Real.exp x + 1) ≤ 6 * Real.exp (-cRK * n) * (2 * Real.exp (cRK / 2 * n)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 12 * Real.exp (-(cRK / 2) * n) := by rw [← e]; ring
  have hN : Tendsto (fun n => expectNPi (PSdeg1 ε n) n (G n)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => ENNReal.ofReal (U n)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hU0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hev, hIC] with n hn hIC
    obtain ⟨h22, hn1, h3, -⟩ := hn
    have hNm : (n : ℝ) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 9) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)
    refine (expectNPi_deg1_bound hn1 hIC h22 hNm).trans (ENNReal.ofReal_le_ofReal ?_)
    have h4 : (n : ℝ) ^ (1 / 10 : ℝ) ≤ cRK / 2 * n :=
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by norm_num)).trans h3
    have := hexp n _ h4
    simp only [hU, ha]
    linarith
  have hN' : Tendsto (fun n => expectNPi (PSdeg1 ε (n + 1)) n (G n)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => ENNReal.ofReal (U n)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hU0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hev, hIC] with n hn hIC
    obtain ⟨h22, hn1, h3, h4⟩ := hn
    have h22' : 22 ≤ ⌊((n + 1 : ℕ) : ℝ) ^ (1 / 2 - ε)⌋₊ := h22.trans (hmono n)
    have hNm : ((n + 1 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 9) := by
      push_cast
      exact h4
    refine (expectNPi_deg1_bound hn1 hIC h22' hNm).trans (ENNReal.ofReal_le_ofReal ?_)
    have h5 : ((n + 1 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ cRK / 2 * n := by
      push_cast
      exact h3
    have := hexp n _ h5
    have h6 : 7 / ((⌊((n + 1 : ℕ) : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ≤ 7 / ((a n : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have : a n ≤ ⌊((n + 1 : ℕ) : ℝ) ^ (1 / 2 - ε)⌋₊ := hmono n
      have : (a n : ℝ) ≤ (⌊((n + 1 : ℕ) : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) := by exact_mod_cast this
      linarith
    simp only [hU]
    linarith
  have hmain := prop_reduction (PSdeg1 ε) (fun n x hx => ⟨hx.1, hx.2.1⟩) G G hG hG hN hN'
  refine hmain.congr fun n => prob_congr fun Gr => ?_
  constructor
  · rintro ⟨p, d, ⟨hp, hp2, h1, h2, hd⟩, hE⟩
    simp only at hd
    subst hd
    exact ⟨p, hp, hp2, h1, h2, hE⟩
  · rintro ⟨p, hp, hp2, h1, h2, hE⟩
    exact ⟨p, 1, ⟨hp, hp2, h1, h2, rfl⟩, hE⟩

end DGS
