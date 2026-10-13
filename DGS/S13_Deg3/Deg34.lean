module

public import DGS.S13_Deg3.Deg34Gen
public import DGS.S13_Deg3.PrimeSum
public import DGS.S13_Deg3.Deg5Main

@[expose] public section

open Finset Filter Topology Matrix Polynomial Module
open scoped Real ENNReal

namespace DGS

def PSdeg4 (ε : ℝ) (n : ℕ) : Set (ℕ × ℕ) :=
  {x | x.1.Prime ∧ x.1 ≠ 2 ∧ (n : ℝ) ^ (1 / 2 - ε) < (x.1 : ℝ) ∧
    (x.1 : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧ x.2 = 4}

def PSdeg3b (ε : ℝ) (n : ℕ) : Set (ℕ × ℕ) :=
  {x | x.1.Prime ∧ x.1 ≠ 2 ∧ (n : ℝ) ^ (1 / 2 - ε) < (x.1 : ℝ) ∧
    (x.1 : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧ n < x.1 * x.1 ∧ x.2 = 3}

def PSdeg3s (ε : ℝ) (n : ℕ) : Set (ℕ × ℕ) :=
  {x | x.1.Prime ∧ x.1 ≠ 2 ∧ (n : ℝ) ^ (1 / 2 - ε) < (x.1 : ℝ) ∧
    (x.1 : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧ x.1 * x.1 ≤ n ∧ x.2 = 3}

theorem mem_PfinDeg1_of {ε : ℝ} {N p : ℕ} (hp : p.Prime) (h1 : (N : ℝ) ^ (1 / 2 - ε) < (p : ℝ))
    (h2 : (p : ℝ) ≤ Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))) : p ∈ PfinDeg1 ε N := by
  refine Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨?_, ?_⟩, hp⟩
  · exact (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg _) _)).2 h1
  · have := Nat.le_floor h2
    omega

theorem pfinOK_of_sub {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) {N m d : ℕ} (hmN : m ≤ N)
    (h22 : 22 ≤ ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊) (hNm : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 8))
    {P : Finset ℕ} (hP : P ⊆ PfinDeg1 ε N) : PfinOK m d P := by
  intro p hpP
  obtain ⟨hIoo, hpr⟩ := Finset.mem_filter.1 (hP hpP)
  obtain ⟨h1, h2⟩ := Finset.mem_Ioo.1 hIoo
  have hN1 : 1 ≤ N := by
    by_contra h
    push Not at h
    have hN0 : N = 0 := by omega
    rw [hN0, Nat.cast_zero, Real.zero_rpow (by linarith)] at h22
    simp at h22
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  refine ⟨hpr, by omega, ?_, fun _ => ?_⟩
  · have h3 : p ≤ ⌊Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))⌋₊ := by omega
    have h4 : (p : ℝ) ≤ Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) := (Nat.le_floor_iff (Real.exp_pos _).le).1 h3
    exact h4.trans (Real.exp_le_exp.2 hNm)
  · have h5 : (N : ℝ) ^ (1 / 2 - ε) < p := (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg _) _)).1 h1
    have h6 : (m : ℝ) ^ (0.4 : ℝ) ≤ (N : ℝ) ^ (0.4 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hmN) (by norm_num)
    have h7 : (N : ℝ) ^ (0.4 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε) :=
      Real.rpow_le_rpow_of_exponent_le hNR (by norm_num; linarith)
    linarith

theorem card_PfinDeg1_le (ε : ℝ) (N : ℕ) :
    ((PfinDeg1 ε N).card : ℝ) ≤ Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1 := by
  have h1 : (PfinDeg1 ε N).card ≤ ⌊Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))⌋₊ + 1 := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Nat.card_Ioo]
    omega
  have h2 : ((⌊Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))⌋₊ : ℕ) : ℝ) ≤ Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) :=
    Nat.floor_le (Real.exp_pos _).le
  have h3 : ((PfinDeg1 ε N).card : ℝ) ≤ ((⌊Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h3
  linarith

theorem sum_inv_pow_le {ε : ℝ} {N : ℕ} {P : Finset ℕ} (hP : P ⊆ PfinDeg1 ε N) (k : ℕ) :
    ∑ p ∈ P, 1 / (p : ℝ) ^ (k + 2) ≤ 2 / ((⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ (k + 1) := by
  set a := ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ with ha
  set b := ⌊Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))⌋₊ + 1 with hb
  have ha0 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hsub : P ⊆ Finset.Ioo a b := hP.trans (Finset.filter_subset _ _)
  have hterm : ∀ p ∈ Finset.Ioo a b, 1 / (p : ℝ) ^ (k + 2) ≤ (((a : ℝ) + 1) ^ k)⁻¹ * ((p : ℝ) ^ 2)⁻¹ := by
    intro p hp
    have hp1 : (a : ℝ) + 1 ≤ p := by
      have := (Finset.mem_Ioo.1 hp).1
      exact_mod_cast this
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le ha0 hp1
    rw [one_div, pow_add, mul_inv, mul_comm ((p : ℝ) ^ k)⁻¹]
    rw [mul_comm (((a : ℝ) + 1) ^ k)⁻¹]
    gcongr
  calc ∑ p ∈ P, 1 / (p : ℝ) ^ (k + 2) ≤ ∑ p ∈ Finset.Ioo a b, 1 / (p : ℝ) ^ (k + 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ p ∈ Finset.Ioo a b, (((a : ℝ) + 1) ^ k)⁻¹ * ((p : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum hterm
    _ = (((a : ℝ) + 1) ^ k)⁻¹ * ∑ p ∈ Finset.Ioo a b, ((p : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (((a : ℝ) + 1) ^ k)⁻¹ * (2 / ((a : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le a b) (by positivity)
    _ = 2 / ((a : ℝ) + 1) ^ (k + 1) := by
        rw [pow_succ]
        field_simp

theorem expectNPi_deg4_bound {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) {N m : ℕ} (hmN : m ≤ N)
    (h22 : 22 ≤ ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊) (hNm : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 8)) :
    expectNPi (PSdeg4 ε N) m {T | GoodSEd 4 T} ≤
      ENNReal.ofReal ((m : ℝ) / 4 / ((⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 3 +
        (m : ℝ) / 8 * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) * Real.exp (-2 * cSEd * m)) := by
  classical
  have hPS : ∀ x ∈ PSdeg4 ε N, x.1 ∈ PfinDeg1 ε N ∧ x.2 = 4 := fun x hx =>
    ⟨mem_PfinDeg1_of hx.1 hx.2.2.1 hx.2.2.2.1, hx.2.2.2.2⟩
  have h := expectNPi_degd_le (PSdeg4 ε N) (PfinDeg1 ε N) hPS
    (pfinOK_of_sub hε0 hε hmN h22 hNm subset_rfl) (fun _ => (m : ℝ) / (2 * (4 : ℕ)))
    (fun p _ _ => sum_prob_sq_dvd_le_count (by norm_num))
  refine h.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  set e := Real.exp (-2 * cSEd * m) with he
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs : ∑ p ∈ PfinDeg1 ε N, 1 / (p : ℝ) ^ 4 ≤ 2 / ((⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 3 :=
    sum_inv_pow_le (ε := ε) (N := N) (P := PfinDeg1 ε N) subset_rfl 2
  have hc := card_PfinDeg1_le ε N
  push_cast
  calc ∑ p ∈ PfinDeg1 ε N, (1 / (p : ℝ) ^ 4 + e) * ((m : ℝ) / (2 * 4))
      = (m : ℝ) / 8 * ∑ p ∈ PfinDeg1 ε N, 1 / (p : ℝ) ^ 4 + (m : ℝ) / 8 * e * (PfinDeg1 ε N).card := by
        rw [show ((m : ℝ) / (2 * 4)) = (m : ℝ) / 8 by norm_num]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (m : ℝ) / 8 * (2 / ((⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 3) +
          (m : ℝ) / 8 * e * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) := by
        gcongr
    _ = (m : ℝ) / 4 / ((⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 3 +
          (m : ℝ) / 8 * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) * e := by ring

theorem expectNPi_deg3b_bound {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) {N m : ℕ} (hmN : m ≤ N)
    (h22 : 22 ≤ ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊) (hNm : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 8))
    (hs2 : 2 ≤ Nat.sqrt N) :
    expectNPi (PSdeg3b ε N) m {T | GoodSEd 3 T} ≤
      ENNReal.ofReal ((m : ℝ) / 6 * (8 / ((Nat.sqrt N : ℝ) ^ 2 * Real.log (Nat.sqrt N)) +
          3 * √(Nat.sqrt N : ℝ) / (Nat.sqrt N : ℝ) ^ 3) +
        (m : ℝ) / 6 * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) * Real.exp (-2 * cSEd * m)) := by
  classical
  set P := (PfinDeg1 ε N).filter (fun p => N < p * p) with hPdef
  have hPsub : P ⊆ PfinDeg1 ε N := Finset.filter_subset _ _
  have hPS : ∀ x ∈ PSdeg3b ε N, x.1 ∈ P ∧ x.2 = 3 := fun x hx =>
    ⟨Finset.mem_filter.2 ⟨mem_PfinDeg1_of hx.1 hx.2.2.1 hx.2.2.2.1, hx.2.2.2.2.1⟩, hx.2.2.2.2.2⟩
  have h := expectNPi_degd_le (PSdeg3b ε N) P hPS
    (pfinOK_of_sub hε0 hε hmN h22 hNm hPsub) (fun _ => (m : ℝ) / (2 * (3 : ℕ)))
    (fun p _ _ => sum_prob_sq_dvd_le_count (by norm_num))
  refine h.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  set e := Real.exp (-2 * cSEd * m) with he
  set s := Nat.sqrt N with hsdef
  set B := ⌊Real.exp ((N : ℝ) ^ (1 / 10 : ℝ))⌋₊ with hB
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hsum : ∑ p ∈ P, 1 / (p : ℝ) ^ 3 ≤ 8 / ((s : ℝ) ^ 2 * Real.log s) + 3 * √(s : ℝ) / (s : ℝ) ^ 3 := by
    refine le_trans ?_ (sum_prime_inv_cube_le hs2 B)
    have hPI : P ⊆ Finset.Ioc s B := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      obtain ⟨hIoo, -⟩ := Finset.mem_filter.1 hp1
      obtain ⟨-, h2⟩ := Finset.mem_Ioo.1 hIoo
      refine Finset.mem_Ioc.2 ⟨Nat.sqrt_lt.2 hp2, by omega⟩
    calc ∑ p ∈ P, 1 / (p : ℝ) ^ 3 = ∑ p ∈ P, (if p.Prime then ((p : ℝ) ^ 3)⁻¹ else 0) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpr : p.Prime := (Finset.mem_filter.1 (hPsub hp)).2
          rw [ite_eq_left hpr, one_div]
      _ ≤ ∑ p ∈ Finset.Ioc s B, (if p.Prime then ((p : ℝ) ^ 3)⁻¹ else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg hPI fun p _ _ => by
            split_ifs
            · positivity
            · exact le_rfl
  have hc : (P.card : ℝ) ≤ Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1 :=
    le_trans (by exact_mod_cast Finset.card_le_card hPsub) (card_PfinDeg1_le ε N)
  push_cast
  calc ∑ p ∈ P, (1 / (p : ℝ) ^ 3 + e) * ((m : ℝ) / (2 * 3))
      = (m : ℝ) / 6 * ∑ p ∈ P, 1 / (p : ℝ) ^ 3 + (m : ℝ) / 6 * e * P.card := by
        rw [show ((m : ℝ) / (2 * 3)) = (m : ℝ) / 6 by norm_num]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (m : ℝ) / 6 * (8 / ((s : ℝ) ^ 2 * Real.log s) + 3 * √(s : ℝ) / (s : ℝ) ^ 3) +
          (m : ℝ) / 6 * e * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) := by
        gcongr
    _ = (m : ℝ) / 6 * (8 / ((s : ℝ) ^ 2 * Real.log s) + 3 * √(s : ℝ) / (s : ℝ) ^ 3) +
          (m : ℝ) / 6 * (Real.exp ((N : ℝ) ^ (1 / 10 : ℝ)) + 1) * e := by ring

theorem expectNPi_deg3s_bound {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 10) {N m : ℕ} (hmN : m ≤ N)
    (h22 : 22 ≤ ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊) (hNm : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 8))
    (hR3 : ∀ p ∈ (PfinDeg1 ε N).filter (fun p => p * p ≤ N), ∀ [Fact p.Prime],
      ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], finrank (ZMod p) L = 3 →
      ∀ μ : L, μ ∉ Set.range (algebraMap (ZMod p) L) →
        prob (fun ω : Pairs m → Bool => 1 ≤ geomMult (F := L) 1 (-1) μ ω) ≤
          1 / (p : ℝ) ^ 3 + 1.2 / ((p : ℝ) ^ 3) ^ 2 + Real.exp (-cRK * m)) :
    expectNPi (PSdeg3s ε N) m {T | GoodSEd 3 T} ≤
      ENNReal.ofReal (4 / ((⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 2 +
        (Nat.sqrt N : ℝ) * (3 + (Nat.sqrt N : ℝ) ^ 3) * Real.exp (-cRK * m)) := by
  classical
  set P := (PfinDeg1 ε N).filter (fun p => p * p ≤ N) with hPdef
  have hPsub : P ⊆ PfinDeg1 ε N := Finset.filter_subset _ _
  have hPS : ∀ x ∈ PSdeg3s ε N, x.1 ∈ P ∧ x.2 = 3 := fun x hx =>
    ⟨Finset.mem_filter.2 ⟨mem_PfinDeg1_of hx.1 hx.2.2.1 hx.2.2.2.1, hx.2.2.2.2.1⟩, hx.2.2.2.2.2⟩
  have h := expectNPi_degd_le (PSdeg3s ε N) P hPS
    (pfinOK_of_sub hε0 hε hmN h22 hNm hPsub) (fun p => 2 + (p : ℝ) ^ 3 * Real.exp (-cRK * m))
    (fun p hp _ => sum_prob_sq_dvd_le3 (hR3 p hp))
  refine h.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  set e := Real.exp (-2 * cSEd * m) with he
  set e' := Real.exp (-cRK * m) with he'
  set s := Nat.sqrt N with hsdef
  have hee' : e ≤ e' := by
    apply Real.exp_le_exp.2
    have h1 : cRK ≤ 2 * cSEd := by
      unfold cRK cPT cSEd
      have : Real.exp (-1500) ≤ Real.exp (-300) := Real.exp_le_exp.2 (by norm_num)
      have := Real.exp_pos (-300)
      linarith
    have := cRK_pos
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have he1 : e ≤ 1 := by
    rw [he, Real.exp_le_one_iff]
    have := cSEd_pos
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he'0 : 0 ≤ e' := (Real.exp_pos _).le
  have hps : ∀ p ∈ P, (p : ℝ) ≤ s := by
    intro p hp
    have := (Finset.mem_filter.1 hp).2
    exact_mod_cast Nat.le_sqrt.2 this
  have hterm : ∀ p ∈ P, (1 / (p : ℝ) ^ 3 + e) * (2 + (p : ℝ) ^ 3 * e') ≤
      2 * (1 / (p : ℝ) ^ 3) + (3 + (s : ℝ) ^ 3) * e' := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by
      have := (Finset.mem_filter.1 (hPsub hp)).2.one_lt.le
      exact_mod_cast this
    have hp0 : (0 : ℝ) < p := by linarith
    have hp3 : (p : ℝ) ^ 3 ≤ (s : ℝ) ^ 3 := pow_le_pow_left₀ hp0.le (hps p hp) 3
    have e1 : (1 / (p : ℝ) ^ 3 + e) * (2 + (p : ℝ) ^ 3 * e') =
        2 * (1 / (p : ℝ) ^ 3) + e' + 2 * e + (p : ℝ) ^ 3 * e * e' := by
      field_simp
      ring
    rw [e1]
    have h2 : (p : ℝ) ^ 3 * e * e' ≤ (s : ℝ) ^ 3 * e' := by
      have : (p : ℝ) ^ 3 * e ≤ (s : ℝ) ^ 3 * 1 := mul_le_mul hp3 he1 he0 (by positivity)
      nlinarith
    nlinarith
  have hcard : (P.card : ℝ) ≤ s := by
    have h1 : P ⊆ Finset.Ioc 0 s := by
      intro p hp
      refine Finset.mem_Ioc.2 ⟨(Finset.mem_filter.1 (hPsub hp)).2.pos, ?_⟩
      exact Nat.le_sqrt.2 (Finset.mem_filter.1 hp).2
    have h2 := Finset.card_le_card h1
    rw [Nat.card_Ioc, Nat.sub_zero] at h2
    exact_mod_cast h2
  have hs : ∑ p ∈ P, 1 / (p : ℝ) ^ 3 ≤ 2 / ((⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 2 :=
    sum_inv_pow_le (ε := ε) (N := N) hPsub 1
  calc ∑ p ∈ P, (1 / (p : ℝ) ^ 3 + e) * (2 + (p : ℝ) ^ 3 * e')
      ≤ ∑ p ∈ P, (2 * (1 / (p : ℝ) ^ 3) + (3 + (s : ℝ) ^ 3) * e') := Finset.sum_le_sum hterm
    _ = 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 3 + P.card * ((3 + (s : ℝ) ^ 3) * e') := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (2 / ((⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 2) + s * ((3 + (s : ℝ) ^ 3) * e') := by
        gcongr
    _ = 4 / ((⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ : ℝ) + 1) ^ 2 + (s : ℝ) * (3 + (s : ℝ) ^ 3) * e' := by ring

end DGS
