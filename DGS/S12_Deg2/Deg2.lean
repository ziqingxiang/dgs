module

public import DGS.S12_Deg2.Rank2
public import DGS.S04_Reduction.LargeDegrees
public import Mathlib.Analysis.PSeries

@[expose] public section

open Finset Filter Topology Matrix Polynomial Module
open scoped Real ENNReal

namespace DGS

section Eig

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

theorem eigsp_le_ker_shiftedMat {L : Type*} [Field L] [Algebra (ZMod p) L] (μ : L) (ω : Pairs m → Bool) :
    eigsp (modP p (seidelOf ω)) μ ≤ LinearMap.ker (shiftedMat (F := L) 1 (-1) μ ω).mulVecLin := by
  intro w hw
  rw [mem_eigsp] at hw
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have e : (modP p (seidelOf ω)).map (algebraMap (ZMod p) L) = (seidelOf ω).map (Int.castRingHom L) := by
    ext i j
    simp [modP]
  rw [e] at hw
  unfold shiftedMat
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
  exact hw

theorem one_le_geomMult_of_sq_dvd {β : (ZMod p)[X]} [Fact (Irreducible β)] (hβm : β.Monic)
    (ω : Pairs m → Bool) (hdvd : β ^ 2 ∣ (modP p (seidelOf ω)).charpoly) :
    1 ≤ geomMult (F := AdjoinRoot β) 1 (-1) (AdjoinRoot.root β) ω := by
  have : Module.Finite (ZMod p) (AdjoinRoot β) := (AdjoinRoot.powerBasis hβm.ne_zero).finite
  have : Finite (AdjoinRoot β) := finite_adjoinRoot hβm.ne_zero
  have h := isGenRoot_adjoinRoot hβm
  have hM := modP_seidel_isSymm (p := p) ω
  have hg := one_le_of_disj ((lem_simple_d h hM).2.1 ((lem_simple_d h hM).1.1 hdvd))
  unfold geomMult corank
  exact hg.trans (Submodule.finrank_mono (eigsp_le_ker_shiftedMat (p := p) _ ω))

theorem root_not_mem_range {β : (ZMod p)[X]} [Fact (Irreducible β)] (hβm : β.Monic) (hβd : β.natDegree = 2) :
    AdjoinRoot.root β ∉ Set.range (algebraMap (ZMod p) (AdjoinRoot β)) := by
  have : Module.Finite (ZMod p) (AdjoinRoot β) := (AdjoinRoot.powerBasis hβm.ne_zero).finite
  have : Finite (AdjoinRoot β) := finite_adjoinRoot hβm.ne_zero
  intro hr
  have h1 : (minpoly (ZMod p) (AdjoinRoot.root β)).natDegree = 1 := minpoly.natDegree_eq_one_iff.2 hr
  rw [(isGenRoot_adjoinRoot hβm).minpoly_eq, hβd] at h1
  exact absurd h1 (by norm_num)

theorem finrank_adjoinRoot_two {β : (ZMod p)[X]} [Fact (Irreducible β)] (hβm : β.Monic) (hβd : β.natDegree = 2) :
    finrank (ZMod p) (AdjoinRoot β) = 2 := by
  rw [(AdjoinRoot.powerBasis hβm.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hβd]

end Eig

open Classical in
noncomputable def wDeg2 {m : ℕ} (Pfin : Finset ℕ) (T : Matrix (Fin m) (Fin m) ℤ)
    (x : Σ p : ℕ, (ZMod p)[X]) : ℝ≥0∞ :=
  if x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = 2 ∧ Irreducible x.2 ∧ x.2 ^ 2 ∣ (modP x.1 T).charpoly then
    ENNReal.ofReal (1 / (x.1 : ℝ) ^ 2 + Real.exp (-2 * cSEd * m)) else 0

theorem NPi_deg2_le {m : ℕ} (PS : Set (ℕ × ℕ)) (Pfin : Finset ℕ) (hPS : ∀ x ∈ PS, x.1 ∈ Pfin ∧ x.2 = 2)
    (hPfin : ∀ p ∈ Pfin, p.Prime ∧ 23 ≤ p ∧ (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    {T : Matrix (Fin m) (Fin m) ℤ} (hT : GoodSEd 2 T) :
    NPi PS T ≤ ∑' x, wDeg2 Pfin T x := by
  classical
  unfold NPi
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases h1 : (x.1, x.2.natDegree) ∈ PS ∧ IsRepeatedFactor x.1 T x.2
  · rw [ite_eq_left h1]
    obtain ⟨hP, hdeg⟩ := hPS _ h1.1
    obtain ⟨hmon, hirr, hdvd⟩ := h1.2
    obtain ⟨hp, hp23, hpm⟩ := hPfin _ hP
    have : Fact x.1.Prime := ⟨hp⟩
    have hcond : x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = 2 ∧ Irreducible x.2 ∧
        x.2 ^ 2 ∣ (modP x.1 T).charpoly := ⟨hP, hmon, hdeg, hirr, hdvd⟩
    unfold wDeg2
    rw [ite_eq_left hcond]
    apply ENNReal.ofReal_le_ofReal
    have h := abeta_le_of_goodSEd hT hp23 hpm (fun h => absurd h (by norm_num)) hmon hirr hdeg
    rw [one_div]
    exact h
  · rw [ite_eq_right h1]
    exact zero_le

open Classical in
theorem expectNPi_deg2_le {m : ℕ} (PS : Set (ℕ × ℕ)) (Pfin : Finset ℕ)
    (hPS : ∀ x ∈ PS, x.1 ∈ Pfin ∧ x.2 = 2)
    (hPfin : ∀ p ∈ Pfin, p.Prime ∧ 23 ≤ p ∧ (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (B : ℕ → ℝ) (hB : ∀ p ∈ Pfin, ∀ [Fact p.Prime], ∑ β ∈ monicOfDegree p 2,
      (if Irreducible β then prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)
        else 0) ≤ B p) :
    expectNPi PS m {T | GoodSEd 2 T} ≤
      ∑ p ∈ Pfin, ENNReal.ofReal ((1 / (p : ℝ) ^ 2 + Real.exp (-2 * cSEd * m)) * B p) := by
  classical
  set card : ℝ≥0∞ := (Fintype.card (Pairs m → Bool) : ℝ≥0∞) with hcard
  set w : (Pairs m → Bool) → (Σ p : ℕ, (ZMod p)[X]) → ℝ≥0∞ := fun ω x => wDeg2 Pfin (seidelOf ω) x with hw
  have hA : ∀ ω : Pairs m → Bool, (if seidelOf ω ∈ {T : Matrix (Fin m) (Fin m) ℤ | GoodSEd 2 T}
      then NPi PS (seidelOf ω) else 0) ≤ ∑' x, w ω x := by
    intro ω
    split_ifs with h
    · exact NPi_deg2_le PS Pfin hPS hPfin h
    · exact zero_le
  set c : ℕ → ℝ := fun p => 1 / (p : ℝ) ^ 2 + Real.exp (-2 * cSEd * m) with hc
  have hc0 : ∀ p, 0 ≤ c p := fun p => by rw [hc]; positivity
  have hC : ∀ x : (Σ p : ℕ, (ZMod p)[X]), (∑ ω, w ω x) / card =
      if x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = 2 ∧ Irreducible x.2 then
        ENNReal.ofReal (c x.1) * ENNReal.ofReal
          (prob (fun ω : Pairs m → Bool => x.2 ^ 2 ∣ (modP x.1 (seidelOf ω)).charpoly)) else 0 := by
    intro x
    by_cases hx : x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = 2 ∧ Irreducible x.2
    · rw [ite_eq_left hx, ofReal_prob_eq, ← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [hw]
      simp only [wDeg2]
      by_cases hd : x.2 ^ 2 ∣ (modP x.1 (seidelOf ω)).charpoly
      · rw [ite_eq_left ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2, hd⟩, ite_eq_left hd, mul_one]
      · rw [ite_eq_right (fun h => hd h.2.2.2.2), ite_eq_right hd, mul_zero]
    · rw [ite_eq_right hx]
      have h0 : ∀ ω, w ω x = 0 := by
        intro ω
        rw [hw]
        simp only [wDeg2]
        rw [ite_eq_right (fun h => hx ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)]
      simp [h0]
  have hD : ∀ p ∈ Pfin, ∑' β : (ZMod p)[X], (if p ∈ Pfin ∧ β.Monic ∧ β.natDegree = 2 ∧ Irreducible β then
      ENNReal.ofReal (c p) * ENNReal.ofReal
        (prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)) else 0) ≤
      ENNReal.ofReal (c p * B p) := by
    intro p hp
    have : Fact p.Prime := ⟨(hPfin p hp).1⟩
    rw [tsum_eq_sum (s := monicOfDegree p 2) fun β hβ => by
      rw [ite_eq_right]
      rintro ⟨-, hm, hd, -⟩
      exact hβ (hd ▸ mem_monicOfDegree hm)]
    have e : ∀ β ∈ monicOfDegree p 2, (if p ∈ Pfin ∧ β.Monic ∧ β.natDegree = 2 ∧ Irreducible β then
        ENNReal.ofReal (c p) * ENNReal.ofReal
          (prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)) else 0) =
        ENNReal.ofReal (c p) * ENNReal.ofReal (if Irreducible β then
          prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly) else 0) := by
      intro β hβ
      obtain ⟨hm, hd⟩ := mem_monicOfDegree_iff hβ
      by_cases hi : Irreducible β
      · rw [ite_eq_left ⟨hp, hm, hd, hi⟩, ite_eq_left hi]
      · rw [ite_eq_right (fun h => hi h.2.2.2), ite_eq_right hi, ENNReal.ofReal_zero, mul_zero]
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun β _ => by
      split_ifs
      · exact prob_nonneg _
      · exact le_rfl), ← ENNReal.ofReal_mul (hc0 p)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hB p hp) (hc0 p))
  rw [expectNPi]
  calc (∑ ω : Pairs m → Bool, if seidelOf ω ∈ {T : Matrix (Fin m) (Fin m) ℤ | GoodSEd 2 T}
        then NPi PS (seidelOf ω) else 0) / card
      ≤ (∑ ω : Pairs m → Bool, ∑' x, w ω x) / card := by
        gcongr with ω
        exact hA ω
    _ = ∑' x, (∑ ω, w ω x) / card := by
        rw [← Summable.tsum_finsetSum (fun ω _ => ENNReal.summable), div_eq_mul_inv,
          ← ENNReal.tsum_mul_right]
        rfl
    _ = ∑' x : (Σ p : ℕ, (ZMod p)[X]), (if x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = 2 ∧ Irreducible x.2 then
          ENNReal.ofReal (c x.1) * ENNReal.ofReal
            (prob (fun ω : Pairs m → Bool => x.2 ^ 2 ∣ (modP x.1 (seidelOf ω)).charpoly)) else 0) := by
        congr 1
        funext x
        exact hC x
    _ = ∑' p : ℕ, ∑' β : (ZMod p)[X], (if p ∈ Pfin ∧ β.Monic ∧ β.natDegree = 2 ∧ Irreducible β then
          ENNReal.ofReal (c p) * ENNReal.ofReal
            (prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)) else 0) :=
        ENNReal.tsum_sigma' _
    _ = ∑ p ∈ Pfin, ∑' β : (ZMod p)[X], (if p ∈ Pfin ∧ β.Monic ∧ β.natDegree = 2 ∧ Irreducible β then
          ENNReal.ofReal (c p) * ENNReal.ofReal
            (prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)) else 0) := by
        refine tsum_eq_sum fun p hp => ?_
        simp [hp]
    _ ≤ ∑ p ∈ Pfin, ENNReal.ofReal (c p * B p) := Finset.sum_le_sum hD

def PSdeg2 (ε : ℝ) (n : ℕ) : Set (ℕ × ℕ) :=
  {x | x.1.Prime ∧ x.1 ≠ 2 ∧ (n : ℝ) ^ (1 / 2 - ε) < (x.1 : ℝ) ∧
    (x.1 : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧ x.2 = 2}

theorem mem_PfinDeg1_of_PSdeg2 {ε : ℝ} {N : ℕ} {x : ℕ × ℕ} (hx : x ∈ PSdeg2 ε N) :
    x.1 ∈ PfinDeg1 ε N ∧ x.2 = 2 := by
  obtain ⟨hp, -, h1, h2, h3⟩ := hx
  refine ⟨Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨?_, ?_⟩, hp⟩, h3⟩
  · exact (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg _) _)).2 h1
  · have := Nat.le_floor h2
    omega

open Classical in
theorem sum_prob_sq_dvd_le {m p : ℕ} [Fact p.Prime] (hp23 : 23 ≤ p)
    (hR2 : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], finrank (ZMod p) L = 2 →
      ∀ μ : L, μ ∉ Set.range (algebraMap (ZMod p) L) →
        prob (fun ω : Pairs m → Bool => 1 ≤ geomMult (F := L) 1 (-1) μ ω) ≤
          1 / (p : ℝ) ^ 2 + 1.2 / ((p : ℝ) ^ 2) ^ 2 + Real.exp (-cRK * m)) :
    ∑ β ∈ monicOfDegree p 2, (if Irreducible β then
      prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly) else 0) ≤
      2 + (p : ℝ) ^ 2 * Real.exp (-cRK * m) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp23R : (23 : ℝ) ≤ p := by exact_mod_cast hp23
  set e' := Real.exp (-cRK * m) with he'
  have he'0 : 0 ≤ e' := (Real.exp_pos _).le
  have hterm : ∀ β ∈ monicOfDegree p 2, (if Irreducible β then
      prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly) else 0) ≤
      1 / (p : ℝ) ^ 2 + 1.2 / ((p : ℝ) ^ 2) ^ 2 + e' := by
    intro β hβ
    obtain ⟨hm, hd⟩ := mem_monicOfDegree_iff hβ
    split_ifs with hi
    · have : Fact (Irreducible β) := ⟨hi⟩
      have : Finite (AdjoinRoot β) := finite_adjoinRoot hm.ne_zero
      let : Fintype (AdjoinRoot β) := Fintype.ofFinite _
      refine le_trans (prob_mono fun ω h => one_le_geomMult_of_sq_dvd hm ω h) ?_
      exact hR2 (AdjoinRoot β) (finrank_adjoinRoot_two hm hd) _ (root_not_mem_range hm hd)
    · positivity
  have hcard : ((monicOfDegree p 2).card : ℝ) ≤ (p : ℝ) ^ 2 := by
    exact_mod_cast card_monicOfDegree_le (p := p) 2
  calc ∑ β ∈ monicOfDegree p 2, (if Irreducible β then
        prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly) else 0)
      ≤ ∑ _β ∈ monicOfDegree p 2, (1 / (p : ℝ) ^ 2 + 1.2 / ((p : ℝ) ^ 2) ^ 2 + e') := sum_le_sum hterm
    _ = (monicOfDegree p 2).card * (1 / (p : ℝ) ^ 2 + 1.2 / ((p : ℝ) ^ 2) ^ 2 + e') := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (p : ℝ) ^ 2 * (1 / (p : ℝ) ^ 2 + 1.2 / ((p : ℝ) ^ 2) ^ 2 + e') :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1 + 1.2 / (p : ℝ) ^ 2 + (p : ℝ) ^ 2 * e' := by
        field_simp
    _ ≤ 2 + (p : ℝ) ^ 2 * e' := by
        have : 1.2 / (p : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith
        linarith

theorem expectNPi_deg2_bound {ε : ℝ} {N m : ℕ} (hm1 : 1 ≤ m)
    (hR2 : ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 9)) →
      ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], finrank (ZMod p) L = 2 →
      ∀ μ : L, μ ∉ Set.range (algebraMap (ZMod p) L) →
        prob (fun ω : Pairs m → Bool => 1 ≤ geomMult (F := L) 1 (-1) μ ω) ≤
          1 / (p : ℝ) ^ 2 + 1.2 / ((p : ℝ) ^ 2) ^ 2 + Real.exp (-cRK * m))
    (h22 : 22 ≤ ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊) (hNm : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 9)) :
    expectNPi (PSdeg2 ε N) m {T | GoodSEd 2 T} ≤
      ENNReal.ofReal (4 / (⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ + 1) +
        8 * Real.exp (3 * (N : ℝ) ^ (1 / 10 : ℝ)) * Real.exp (-cRK * m)) := by
  classical
  set a := ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ with ha
  set b := ⌊Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))⌋₊ + 1 with hb
  set X := Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) with hX
  have hX1 : 1 ≤ X := Real.one_le_exp (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have h98 : (m : ℝ) ^ ((1 : ℝ) / 9) ≤ (m : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hm1R (by norm_num)
  have hPfin : ∀ p ∈ PfinDeg1 ε N, p.Prime ∧ 23 ≤ p ∧ (p : ℝ) ≤ X ∧
      (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 9)) := by
    intro p hp
    obtain ⟨hIoo, hpr⟩ := Finset.mem_filter.1 hp
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.1 hIoo
    refine ⟨hpr, by omega, ?_, ?_⟩
    · have h3 : p ≤ ⌊Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))⌋₊ := by omega
      exact (Nat.le_floor_iff (Real.exp_pos _).le).1 h3
    · have h3 : p ≤ ⌊Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))⌋₊ := by omega
      have h4 : (p : ℝ) ≤ Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) :=
        (Nat.le_floor_iff (Real.exp_pos _).le).1 h3
      exact h4.trans (Real.exp_le_exp.2 hNm)
  have h := expectNPi_deg2_le (PSdeg2 ε N) (PfinDeg1 ε N) (fun x hx => mem_PfinDeg1_of_PSdeg2 hx)
    (fun p hp => ⟨(hPfin p hp).1, (hPfin p hp).2.1, (hPfin p hp).2.2.2.trans (Real.exp_le_exp.2 h98)⟩)
    (fun p => 2 + (p : ℝ) ^ 2 * Real.exp (-cRK * m))
    (fun p hp _ => sum_prob_sq_dvd_le (hPfin p hp).2.1
      (hR2 p (hPfin p hp).2.1 (hPfin p hp).2.2.2))
  refine h.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  set e := Real.exp (-2 * cSEd * m) with he
  set e' := Real.exp (-cRK * m) with he'
  have hee' : e ≤ e' := by
    apply Real.exp_le_exp.2
    have h1 : cRK ≤ 2 * cSEd := by
      unfold cRK cPT cSEd
      have : Real.exp (-1500) ≤ Real.exp (-300) := Real.exp_le_exp.2 (by norm_num)
      have := Real.exp_pos (-300)
      linarith
    have := cRK_pos
    nlinarith
  have he1 : e ≤ 1 := by
    rw [he, Real.exp_le_one_iff]
    have := cSEd_pos
    nlinarith
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he'0 : 0 ≤ e' := (Real.exp_pos _).le
  have hterm : ∀ p ∈ PfinDeg1 ε N, (1 / (p : ℝ) ^ 2 + e) * (2 + (p : ℝ) ^ 2 * e') ≤
      2 * ((p : ℝ) ^ 2)⁻¹ + (3 + X ^ 2) * e' := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hPfin p hp).1.one_lt.le
    have hp0 : (0 : ℝ) < p := by linarith
    have hpX : (p : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hp0.le (hPfin p hp).2.2.1 2
    have e1 : (1 / (p : ℝ) ^ 2 + e) * (2 + (p : ℝ) ^ 2 * e') =
        2 * ((p : ℝ) ^ 2)⁻¹ + e' + 2 * e + (p : ℝ) ^ 2 * e * e' := by
      field_simp
      ring
    rw [e1]
    have h2 : (p : ℝ) ^ 2 * e * e' ≤ X ^ 2 * e' := by
      have : (p : ℝ) ^ 2 * e ≤ X ^ 2 * 1 := mul_le_mul hpX he1 he0 (by positivity)
      nlinarith
    nlinarith
  have hsq : ∑ p ∈ PfinDeg1 ε N, ((p : ℝ) ^ 2)⁻¹ ≤ 2 / (a + 1) := by
    calc ∑ p ∈ PfinDeg1 ε N, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ p ∈ Finset.Ioo a b, ((p : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
      _ ≤ 2 / (a + 1) := sum_Ioo_inv_sq_le a b
  have hcard : ((PfinDeg1 ε N).card : ℝ) ≤ X + 1 := by
    have h1 : (PfinDeg1 ε N).card ≤ b := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Nat.card_Ioo]
      omega
    have h2 : (b : ℝ) ≤ X + 1 := by
      rw [hb]
      push_cast
      have := Nat.floor_le (Real.exp_pos ((N : ℝ) ^ (1 / 10 : ℝ))).le
      linarith
    exact (by exact_mod_cast h1 : ((PfinDeg1 ε N).card : ℝ) ≤ b).trans h2
  have hX3 : (X + 1) * (3 + X ^ 2) ≤ 8 * Real.exp (3 * (N : ℝ) ^ (1 / 10 : ℝ)) := by
    have e3 : Real.exp (3 * (N : ℝ) ^ (1 / 10 : ℝ)) = X ^ 3 := by
      rw [hX, ← Real.exp_nat_mul]
      ring_nf
    rw [e3]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hX1 2, pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hX1 3]
  calc ∑ p ∈ PfinDeg1 ε N, (1 / (p : ℝ) ^ 2 + e) * (2 + (p : ℝ) ^ 2 * e')
      ≤ ∑ p ∈ PfinDeg1 ε N, (2 * ((p : ℝ) ^ 2)⁻¹ + (3 + X ^ 2) * e') := Finset.sum_le_sum hterm
    _ = 2 * ∑ p ∈ PfinDeg1 ε N, ((p : ℝ) ^ 2)⁻¹ + (PfinDeg1 ε N).card * ((3 + X ^ 2) * e') := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (2 / (a + 1)) + (X + 1) * ((3 + X ^ 2) * e') := by
        gcongr
    _ = 4 / (a + 1) + ((X + 1) * (3 + X ^ 2)) * e' := by ring
    _ ≤ 4 / (a + 1) + 8 * Real.exp (3 * (N : ℝ) ^ (1 / 10 : ℝ)) * e' := by
        gcongr

theorem prop_deg2 {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    Tendsto (fun n : ℕ => probG n (fun G => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ) ∧ (p : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧ E p 2 G))
      atTop (𝓝 0) := by
  classical
  set G : ∀ n, Set (Matrix (Fin n) (Fin n) ℤ) := fun n => {T | GoodSEd 2 T} with hGdef
  have hG : Tendsto (fun n => probSeidel n (fun S => S ∉ G n)) atTop (𝓝 0) := by
    have hu : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) / 9)) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n : ℕ => -(n : ℝ) / 9) atTop atBot := by
        have := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg (r := -(1 / 9 : ℝ))
          (by norm_num)
        refine this.congr fun n => ?_
        ring
      exact Real.tendsto_exp_atBot.comp h3
    refine tendsto_prob_zero_of_le hu ?_
    filter_upwards [prop_SEd (d := 2) le_rfl (by norm_num)] with n hn
    exact le_trans (le_of_eq (prob_congr fun ω => by simp [hGdef])) hn
  set a : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ (1 / 2 - ε)⌋₊ with ha
  have ha_tend : Tendsto a atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 / 2 - ε)).comp
      tendsto_natCast_atTop_atTop)
  set U : ℕ → ℝ := fun n => 4 / ((a n : ℝ) + 1) + 8 * Real.exp (-(cRK / 2) * n) with hU
  have hU0 : Tendsto U atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => 4 / ((a n : ℝ) + 1)) atTop (𝓝 0) := by
      have : Tendsto (fun n => (a n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp ha_tend)
      exact this.const_div_atTop 4
    have h2 : Tendsto (fun n : ℕ => 8 * Real.exp (-(cRK / 2) * n)) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n : ℕ => -(cRK / 2) * (n : ℝ)) atTop atBot :=
        (tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg (by have := cRK_pos; linarith)
      have h4 := (Real.tendsto_exp_atBot.comp h3).const_mul 8
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
      ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ cRK / 6 * n ∧
      ((n : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 9) := by
    filter_upwards [ha_tend.eventually_ge_atTop 22, eventually_ge_atTop 1,
      eventually_rpow_tenth_succ_le_mul (by have := cRK_pos; positivity : 0 < cRK / 6),
      eventually_rpow_tenth_succ_le_ninth] with n h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hexp : ∀ n : ℕ, ∀ x : ℝ, x ≤ cRK / 6 * n →
      8 * Real.exp (3 * x) * Real.exp (-cRK * n) ≤ 8 * Real.exp (-(cRK / 2) * n) := by
    intro n x hx
    have h1 : Real.exp (3 * x) * Real.exp (-cRK * n) ≤ Real.exp (-(cRK / 2) * n) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith
    linarith
  have hN : Tendsto (fun n => expectNPi (PSdeg2 ε n) n (G n)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => ENNReal.ofReal (U n)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hU0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hev, thm_rank2] with n hn hR2
    obtain ⟨h22, hn1, h3, -⟩ := hn
    have hNm : (n : ℝ) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 9) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)
    refine (expectNPi_deg2_bound hn1 hR2 h22 hNm).trans (ENNReal.ofReal_le_ofReal ?_)
    have h4 : (n : ℝ) ^ (1 / 10 : ℝ) ≤ cRK / 6 * n :=
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by norm_num)).trans h3
    have := hexp n _ h4
    simp only [hU, ha]
    linarith
  have hN' : Tendsto (fun n => expectNPi (PSdeg2 ε (n + 1)) n (G n)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => ENNReal.ofReal (U n)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hU0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hev, thm_rank2] with n hn hR2
    obtain ⟨h22, hn1, h3, h4⟩ := hn
    have h22' : 22 ≤ ⌊((n + 1 : ℕ) : ℝ) ^ (1 / 2 - ε)⌋₊ := h22.trans (hmono n)
    have hNm : ((n + 1 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 9) := by
      push_cast
      exact h4
    refine (expectNPi_deg2_bound hn1 hR2 h22' hNm).trans (ENNReal.ofReal_le_ofReal ?_)
    have h5 : ((n + 1 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ cRK / 6 * n := by
      push_cast
      exact h3
    have := hexp n _ h5
    have h6 : 4 / ((⌊((n + 1 : ℕ) : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ≤ 4 / ((a n : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have : a n ≤ ⌊((n + 1 : ℕ) : ℝ) ^ (1 / 2 - ε)⌋₊ := hmono n
      have : (a n : ℝ) ≤ (⌊((n + 1 : ℕ) : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) := by exact_mod_cast this
      linarith
    simp only [hU]
    linarith
  have hmain := prop_reduction (PSdeg2 ε) (fun n x hx => ⟨hx.1, hx.2.1⟩) G G hG hG hN hN'
  refine hmain.congr fun n => prob_congr fun Gr => ?_
  constructor
  · rintro ⟨p, d, ⟨hp, hp2, h1, h2, hd⟩, hE⟩
    simp only at hd
    subst hd
    exact ⟨p, hp, hp2, h1, h2, hE⟩
  · rintro ⟨p, hp, hp2, h1, h2, hE⟩
    exact ⟨p, 2, ⟨hp, hp2, h1, h2, rfl⟩, hE⟩

end DGS
