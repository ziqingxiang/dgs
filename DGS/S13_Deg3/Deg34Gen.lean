module

public import DGS.S13_Deg3.Rank3
public import DGS.S12_Deg2.Deg2

@[expose] public section

open Finset Filter Topology Matrix Polynomial Module
open scoped Real ENNReal

namespace DGS

section Count

variable {p : ℕ} [Fact p.Prime]

open Classical in
theorem card_sq_dvd_le {d : ℕ} {χ : (ZMod p)[X]} (hχ : χ.Monic) :
    ((monicOfDegree p d).filter (fun β => Irreducible β ∧ β ^ 2 ∣ χ)).card * (2 * d) ≤ χ.natDegree := by
  classical
  set S := (monicOfDegree p d).filter (fun β => Irreducible β ∧ β ^ 2 ∣ χ) with hS
  have hmem : ∀ β ∈ S, β.Monic ∧ β.natDegree = d ∧ Irreducible β ∧ β ^ 2 ∣ χ := by
    intro β hβ
    rw [hS, mem_filter] at hβ
    obtain ⟨hm, hd⟩ := mem_monicOfDegree_iff hβ.1
    exact ⟨hm, hd, hβ.2.1, hβ.2.2⟩
  have hpair : (S : Set (ZMod p)[X]).Pairwise (Function.onFun IsCoprime fun β => β ^ 2) := by
    intro β hβ β' hβ' hne
    obtain ⟨hm, -, hirr, -⟩ := hmem β hβ
    obtain ⟨hm', -, hirr', -⟩ := hmem β' hβ'
    have hc : IsCoprime β β' := by
      rw [hirr.coprime_iff_not_dvd]
      intro hdvd
      exact hne (eq_of_monic_of_associated hm hm' (hirr.associated_of_dvd hirr' hdvd))
    exact hc.pow
  have hdvd : (∏ β ∈ S, β ^ 2) ∣ χ := Finset.prod_dvd_of_coprime hpair fun β hβ => (hmem β hβ).2.2.2
  have h1 := natDegree_le_of_dvd hdvd hχ.ne_zero
  rw [natDegree_prod _ _ fun β hβ => pow_ne_zero 2 (hmem β hβ).2.2.1.ne_zero] at h1
  rw [Finset.sum_congr rfl fun β hβ => by rw [natDegree_pow, (hmem β hβ).2.1], sum_const, smul_eq_mul] at h1
  exact h1

open Classical in
theorem sum_prob_sq_dvd_le_count {m d : ℕ} (hd : 1 ≤ d) :
    ∑ β ∈ monicOfDegree p d, (if Irreducible β then
      prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly) else 0) ≤ (m : ℝ) / (2 * d) := by
  have hd0 : (0 : ℝ) < 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  calc ∑ β ∈ monicOfDegree p d, (if Irreducible β then
        prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly) else 0)
      = ∑ β ∈ monicOfDegree p d, expect (fun ω : Pairs m → Bool =>
          if Irreducible β ∧ β ^ 2 ∣ (modP p (seidelOf ω)).charpoly then (1 : ℝ) else 0) := by
        refine sum_congr rfl fun β _ => ?_
        rw [expect_indicator]
        split_ifs with h
        · exact prob_congr fun ω => ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
        · rw [prob_congr (Q := fun _ => False) fun ω => ⟨fun h' => h h'.1, False.elim⟩, prob_false]
    _ = expect (fun ω : Pairs m → Bool => ∑ β ∈ monicOfDegree p d,
          if Irreducible β ∧ β ^ 2 ∣ (modP p (seidelOf ω)).charpoly then (1 : ℝ) else 0) :=
        (expect_sum _ _).symm
    _ ≤ expect (fun _ : Pairs m → Bool => (m : ℝ) / (2 * d)) := by
        refine expect_mono fun ω => ?_
        rw [sum_boole]
        have h := card_sq_dvd_le (d := d) (Matrix.charpoly_monic (modP p (seidelOf ω)))
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h
        rw [le_div_iff₀ hd0]
        exact_mod_cast h
    _ = (m : ℝ) / (2 * d) := expect_const _

end Count

open Classical in
noncomputable def wDegd {m : ℕ} (d : ℕ) (Pfin : Finset ℕ) (T : Matrix (Fin m) (Fin m) ℤ)
    (x : Σ p : ℕ, (ZMod p)[X]) : ℝ≥0∞ :=
  if x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = d ∧ Irreducible x.2 ∧ x.2 ^ 2 ∣ (modP x.1 T).charpoly then
    ENNReal.ofReal (1 / (x.1 : ℝ) ^ d + Real.exp (-2 * cSEd * m)) else 0

def PfinOK (m d : ℕ) (Pfin : Finset ℕ) : Prop :=
  ∀ p ∈ Pfin, p.Prime ∧ 23 ≤ p ∧ (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) ∧
    (3 ≤ d → (m : ℝ) ^ (0.4 : ℝ) ≤ p)

theorem NPi_degd_le {m d : ℕ} (PS : Set (ℕ × ℕ)) (Pfin : Finset ℕ) (hPS : ∀ x ∈ PS, x.1 ∈ Pfin ∧ x.2 = d)
    (hPfin : PfinOK m d Pfin) {T : Matrix (Fin m) (Fin m) ℤ} (hT : GoodSEd d T) :
    NPi PS T ≤ ∑' x, wDegd d Pfin T x := by
  classical
  unfold NPi
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases h1 : (x.1, x.2.natDegree) ∈ PS ∧ IsRepeatedFactor x.1 T x.2
  · rw [ite_eq_left h1]
    obtain ⟨hP, hdeg⟩ := hPS _ h1.1
    obtain ⟨hmon, hirr, hdvd⟩ := h1.2
    obtain ⟨hp, hp23, hpm, hp4⟩ := hPfin _ hP
    have : Fact x.1.Prime := ⟨hp⟩
    have hcond : x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = d ∧ Irreducible x.2 ∧
        x.2 ^ 2 ∣ (modP x.1 T).charpoly := ⟨hP, hmon, hdeg, hirr, hdvd⟩
    unfold wDegd
    rw [ite_eq_left hcond]
    apply ENNReal.ofReal_le_ofReal
    have h := abeta_le_of_goodSEd hT hp23 hpm hp4 hmon hirr hdeg
    rw [one_div]
    exact h
  · rw [ite_eq_right h1]
    exact zero_le

open Classical in
theorem expectNPi_degd_le {m d : ℕ} (PS : Set (ℕ × ℕ)) (Pfin : Finset ℕ)
    (hPS : ∀ x ∈ PS, x.1 ∈ Pfin ∧ x.2 = d) (hPfin : PfinOK m d Pfin)
    (B : ℕ → ℝ) (hB : ∀ p ∈ Pfin, ∀ [Fact p.Prime], ∑ β ∈ monicOfDegree p d,
      (if Irreducible β then prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)
        else 0) ≤ B p) :
    expectNPi PS m {T | GoodSEd d T} ≤
      ∑ p ∈ Pfin, ENNReal.ofReal ((1 / (p : ℝ) ^ d + Real.exp (-2 * cSEd * m)) * B p) := by
  classical
  set card : ℝ≥0∞ := (Fintype.card (Pairs m → Bool) : ℝ≥0∞) with hcard
  set w : (Pairs m → Bool) → (Σ p : ℕ, (ZMod p)[X]) → ℝ≥0∞ := fun ω x => wDegd d Pfin (seidelOf ω) x with hw
  have hA : ∀ ω : Pairs m → Bool, (if seidelOf ω ∈ {T : Matrix (Fin m) (Fin m) ℤ | GoodSEd d T}
      then NPi PS (seidelOf ω) else 0) ≤ ∑' x, w ω x := by
    intro ω
    split_ifs with h
    · exact NPi_degd_le PS Pfin hPS hPfin h
    · exact zero_le
  set c : ℕ → ℝ := fun p => 1 / (p : ℝ) ^ d + Real.exp (-2 * cSEd * m) with hc
  have hc0 : ∀ p, 0 ≤ c p := fun p => by rw [hc]; positivity
  have hC : ∀ x : (Σ p : ℕ, (ZMod p)[X]), (∑ ω, w ω x) / card =
      if x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = d ∧ Irreducible x.2 then
        ENNReal.ofReal (c x.1) * ENNReal.ofReal
          (prob (fun ω : Pairs m → Bool => x.2 ^ 2 ∣ (modP x.1 (seidelOf ω)).charpoly)) else 0 := by
    intro x
    by_cases hx : x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = d ∧ Irreducible x.2
    · rw [ite_eq_left hx, ofReal_prob_eq, ← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [hw]
      simp only [wDegd]
      by_cases hd : x.2 ^ 2 ∣ (modP x.1 (seidelOf ω)).charpoly
      · rw [ite_eq_left ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2, hd⟩, ite_eq_left hd, mul_one]
      · rw [ite_eq_right (fun h => hd h.2.2.2.2), ite_eq_right hd, mul_zero]
    · rw [ite_eq_right hx]
      have h0 : ∀ ω, w ω x = 0 := by
        intro ω
        rw [hw]
        simp only [wDegd]
        rw [ite_eq_right (fun h => hx ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)]
      simp [h0]
  have hD : ∀ p ∈ Pfin, ∑' β : (ZMod p)[X], (if p ∈ Pfin ∧ β.Monic ∧ β.natDegree = d ∧ Irreducible β then
      ENNReal.ofReal (c p) * ENNReal.ofReal
        (prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)) else 0) ≤
      ENNReal.ofReal (c p * B p) := by
    intro p hp
    have : Fact p.Prime := ⟨(hPfin p hp).1⟩
    rw [tsum_eq_sum (s := monicOfDegree p d) fun β hβ => by
      rw [ite_eq_right]
      rintro ⟨-, hm, hd, -⟩
      exact hβ (hd ▸ mem_monicOfDegree hm)]
    have e : ∀ β ∈ monicOfDegree p d, (if p ∈ Pfin ∧ β.Monic ∧ β.natDegree = d ∧ Irreducible β then
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
  calc (∑ ω : Pairs m → Bool, if seidelOf ω ∈ {T : Matrix (Fin m) (Fin m) ℤ | GoodSEd d T}
        then NPi PS (seidelOf ω) else 0) / card
      ≤ (∑ ω : Pairs m → Bool, ∑' x, w ω x) / card := by
        gcongr with ω
        exact hA ω
    _ = ∑' x, (∑ ω, w ω x) / card := by
        rw [← Summable.tsum_finsetSum (fun ω _ => ENNReal.summable), div_eq_mul_inv,
          ← ENNReal.tsum_mul_right]
        rfl
    _ = ∑' x : (Σ p : ℕ, (ZMod p)[X]), (if x.1 ∈ Pfin ∧ x.2.Monic ∧ x.2.natDegree = d ∧ Irreducible x.2 then
          ENNReal.ofReal (c x.1) * ENNReal.ofReal
            (prob (fun ω : Pairs m → Bool => x.2 ^ 2 ∣ (modP x.1 (seidelOf ω)).charpoly)) else 0) := by
        congr 1
        funext x
        exact hC x
    _ = ∑' p : ℕ, ∑' β : (ZMod p)[X], (if p ∈ Pfin ∧ β.Monic ∧ β.natDegree = d ∧ Irreducible β then
          ENNReal.ofReal (c p) * ENNReal.ofReal
            (prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)) else 0) :=
        ENNReal.tsum_sigma' _
    _ = ∑ p ∈ Pfin, ∑' β : (ZMod p)[X], (if p ∈ Pfin ∧ β.Monic ∧ β.natDegree = d ∧ Irreducible β then
          ENNReal.ofReal (c p) * ENNReal.ofReal
            (prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly)) else 0) := by
        refine tsum_eq_sum fun p hp => ?_
        simp [hp]
    _ ≤ ∑ p ∈ Pfin, ENNReal.ofReal (c p * B p) := Finset.sum_le_sum hD

section Deg3

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

theorem root_not_mem_range_of_two_le {β : (ZMod p)[X]} [Fact (Irreducible β)] (hβm : β.Monic)
    (hβd : 2 ≤ β.natDegree) : AdjoinRoot.root β ∉ Set.range (algebraMap (ZMod p) (AdjoinRoot β)) := by
  have : Module.Finite (ZMod p) (AdjoinRoot β) := (AdjoinRoot.powerBasis hβm.ne_zero).finite
  have : Finite (AdjoinRoot β) := finite_adjoinRoot hβm.ne_zero
  intro hr
  have h1 : (minpoly (ZMod p) (AdjoinRoot.root β)).natDegree = 1 := minpoly.natDegree_eq_one_iff.2 hr
  rw [(isGenRoot_adjoinRoot hβm).minpoly_eq] at h1
  omega

theorem finrank_adjoinRoot_eq {β : (ZMod p)[X]} [Fact (Irreducible β)] (hβm : β.Monic) :
    finrank (ZMod p) (AdjoinRoot β) = β.natDegree := by
  rw [(AdjoinRoot.powerBasis hβm.ne_zero).finrank, AdjoinRoot.powerBasis_dim]

open Classical in
theorem sum_prob_sq_dvd_le3
    (hR3 : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], finrank (ZMod p) L = 3 →
      ∀ μ : L, μ ∉ Set.range (algebraMap (ZMod p) L) →
        prob (fun ω : Pairs m → Bool => 1 ≤ geomMult (F := L) 1 (-1) μ ω) ≤
          1 / (p : ℝ) ^ 3 + 1.2 / ((p : ℝ) ^ 3) ^ 2 + Real.exp (-cRK * m)) :
    ∑ β ∈ monicOfDegree p 3, (if Irreducible β then
      prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly) else 0) ≤
      2 + (p : ℝ) ^ 3 * Real.exp (-cRK * m) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  set e' := Real.exp (-cRK * m) with he'
  have he'0 : 0 ≤ e' := (Real.exp_pos _).le
  have hterm : ∀ β ∈ monicOfDegree p 3, (if Irreducible β then
      prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly) else 0) ≤
      1 / (p : ℝ) ^ 3 + 1.2 / ((p : ℝ) ^ 3) ^ 2 + e' := by
    intro β hβ
    obtain ⟨hm, hd⟩ := mem_monicOfDegree_iff hβ
    split_ifs with hi
    · have : Fact (Irreducible β) := ⟨hi⟩
      have : Finite (AdjoinRoot β) := finite_adjoinRoot hm.ne_zero
      let : Fintype (AdjoinRoot β) := Fintype.ofFinite _
      refine le_trans (prob_mono fun ω h => one_le_geomMult_of_sq_dvd hm ω h) ?_
      exact hR3 (AdjoinRoot β) (by rw [finrank_adjoinRoot_eq hm, hd]) _
        (root_not_mem_range_of_two_le hm (by omega))
    · positivity
  have hcard : ((monicOfDegree p 3).card : ℝ) ≤ (p : ℝ) ^ 3 := by
    exact_mod_cast card_monicOfDegree_le (p := p) 3
  have hp3 : (8 : ℝ) ≤ (p : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp2R 3
    norm_num at h
    linarith
  calc ∑ β ∈ monicOfDegree p 3, (if Irreducible β then
        prob (fun ω : Pairs m → Bool => β ^ 2 ∣ (modP p (seidelOf ω)).charpoly) else 0)
      ≤ ∑ _β ∈ monicOfDegree p 3, (1 / (p : ℝ) ^ 3 + 1.2 / ((p : ℝ) ^ 3) ^ 2 + e') := sum_le_sum hterm
    _ = (monicOfDegree p 3).card * (1 / (p : ℝ) ^ 3 + 1.2 / ((p : ℝ) ^ 3) ^ 2 + e') := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (p : ℝ) ^ 3 * (1 / (p : ℝ) ^ 3 + 1.2 / ((p : ℝ) ^ 3) ^ 2 + e') :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1 + 1.2 / (p : ℝ) ^ 3 + (p : ℝ) ^ 3 * e' := by
        field_simp
    _ ≤ 2 + (p : ℝ) ^ 3 * e' := by
        have : 1.2 / (p : ℝ) ^ 3 ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith
        linarith

end Deg3

end DGS
