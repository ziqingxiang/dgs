module

public import DGS.S11_Deg1.PencilSupp

@[expose] public section

open Finset Matrix Module Filter Topology

namespace DGS

variable {m : ℕ}

theorem pencil_card_facts {U R : Finset (Fin m)} (hRU : Disjoint R U) :
    R.card + (Uᶜ \ R).card + U.card = m ∧ Rᶜ.card + R.card = m := by
  have hsub : R ⊆ Uᶜ := Finset.subset_compl_iff_disjoint_right.2 hRU
  have h1 := Finset.card_sdiff_add_card_eq_card hsub
  have h2 := Finset.card_add_card_compl U
  have h3 := Finset.card_add_card_compl R
  simp only [Fintype.card_fin] at h2 h3
  omega

theorem half_pow_le_two_rpow (N : ℕ) : ((1 : ℝ) / 2) ^ N ≤ (2 : ℝ) ^ (-((N : ℝ) / 4)) := by
  have e : ((1 : ℝ) / 2) ^ N = (2 : ℝ) ^ (-(N : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, _root_.one_div_pow, one_div]
  rw [e]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

def AdmUR (U R : Finset (Fin m)) : Prop :=
  2 * m ≤ 5 * U.card ∧ 5 * U.card ≤ 3 * m ∧ Disjoint R U ∧ 100 * (Uᶜ \ R).card ≤ m

section OneChoice

variable {p : ℕ} [Fact p.Prime]

theorem prob_BK_le (hp2 : p ≠ 2) (b0 b1 a0 a1 : ZMod p) (U R : Finset (Fin m)) (hRU : Disjoint R U)
    (ha : a0 ≠ 0 ∨ a1 ≠ 0) (hm : 34 ≤ m) (hU1 : 2 * m ≤ 5 * U.card) (hU : 5 * U.card ≤ 3 * m)
    (hR : 100 * (Uᶜ \ R).card ≤ m) :
    prob (BK b0 b1 a0 a1 U R) ≤
      32 * 2 ^ m * (2 : ℝ) ^ (-((((m / 100 + 1) * (m / 100 + 1) : ℕ) : ℝ) / 4)) := by
  set t := m / 100 with ht
  obtain ⟨hc1, hc2⟩ := pencil_card_facts hRU
  have htk : t + 1 ≤ R.card / 2 := by omega
  have hkn : R.card / 2 ≤ Rᶜ.card := by omega
  have hkm : R.card / 2 ≤ m := by omega
  have hnumN : 100 * Rᶜ.card + 13 * m + 400 * t ≤ 100 * U.card + 100 * (R.card / 2) := by omega
  have hnum : (Rᶜ.card : ℝ) + 0.13 * m ≤ (U.card : ℝ) + ((R.card / 2 : ℕ) : ℝ) - 4 * t := by
    have h : ((100 * Rᶜ.card + 13 * m + 400 * t : ℕ) : ℝ) ≤
        ((100 * U.card + 100 * (R.card / 2) : ℕ) : ℝ) := by exact_mod_cast hnumN
    push_cast at h
    linarith
  have h1 : prob (BK b0 b1 a0 a1 U R) ≤
      prob (fun ω => BK b0 b1 a0 a1 U R ω ∧ (¬ BW (p := p) R t ω ∧ ¬ BP (p := p) a0 a1 U t ω)) +
        prob (BW (p := p) R t) + prob (BP (p := p) a0 a1 U t) := by
    refine (prob_mono (Q := fun ω => ((BK b0 b1 a0 a1 U R ω ∧
      (¬ BW (p := p) R t ω ∧ ¬ BP (p := p) a0 a1 U t ω)) ∨ BW (p := p) R t ω) ∨
        BP (p := p) a0 a1 U t ω) fun ω hω => by tauto).trans ?_
    refine (prob_or_le _ _).trans ?_
    exact add_le_add (prob_or_le _ _) le_rfl
  have h2 := prob_BK_good_le b0 b1 a0 a1 U R hp2 hRU hnum
  have h3 := prob_BW_le R hp2 htk hkn
  have h4 := prob_BP_le a0 a1 U hp2 ha t
  set E : ℝ := (2 : ℝ) ^ (-((((t + 1) * (t + 1) : ℕ) : ℝ) / 4)) with hE
  have hE0 : 0 ≤ E := by positivity
  have h5 : (2 : ℝ) ^ (R.card / 2) * ((1 : ℝ) / 2) ^ ((t + 1) * (t + 1)) ≤ 2 ^ m * E :=
    mul_le_mul (pow_le_pow_right₀ (by norm_num) hkm) (half_pow_le_two_rpow _) (by positivity)
      (by positivity)
  have h6 : (2 : ℝ) ^ (-(((t + 1 : ℕ) : ℝ) ^ 2 / 4)) = E := by
    have e : (((t + 1 : ℕ) : ℝ) ^ 2 / 4) = ((((t + 1) * (t + 1) : ℕ) : ℝ) / 4) := by
      push_cast
      ring
    rw [hE, e]
  have h7 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  rw [h6] at h4
  calc prob (BK b0 b1 a0 a1 U R) ≤ _ := h1
    _ ≤ 2 ^ m * E + 2 ^ m * E + 30 * E := by linarith
    _ ≤ 32 * 2 ^ m * E := by nlinarith

abbrev PSIdx (m p : ℕ) := (Finset (Fin m) × Finset (Fin m)) × ((ZMod p × ZMod p) × (ZMod p × ZMod p))

variable (p) in
def BadPS (ω : Pairs m → Bool) : Prop :=
  ∃ i : PSIdx m p, (AdmUR i.1.1 i.1.2 ∧ (i.2.1.1 ≠ 0 ∨ i.2.1.2 ≠ 0)) ∧
    BK i.2.2.1 i.2.2.2 i.2.1.1 i.2.1.2 i.1.1 i.1.2 ω

theorem prob_BadPS_le (hp2 : p ≠ 2) (hm : 34 ≤ m) :
    prob (BadPS (m := m) p) ≤ 2 ^ m * 2 ^ m * (p : ℝ) ^ 4 *
      (32 * 2 ^ m * (2 : ℝ) ^ (-((((m / 100 + 1) * (m / 100 + 1) : ℕ) : ℝ) / 4))) := by
  classical
  set B : ℝ := 32 * 2 ^ m * (2 : ℝ) ^ (-((((m / 100 + 1) * (m / 100 + 1) : ℕ) : ℝ) / 4)) with hB
  have hB0 : 0 ≤ B := by positivity
  have h1 := prob_exists_le_sum_fintype (Ω := Pairs m → Bool) (fun (i : PSIdx m p) ω =>
    (AdmUR i.1.1 i.1.2 ∧ (i.2.1.1 ≠ 0 ∨ i.2.1.2 ≠ 0)) ∧ BK i.2.2.1 i.2.2.2 i.2.1.1 i.2.1.2 i.1.1 i.1.2 ω)
  have h2 : ∀ i : PSIdx m p, prob (fun ω => (AdmUR i.1.1 i.1.2 ∧ (i.2.1.1 ≠ 0 ∨ i.2.1.2 ≠ 0)) ∧
      BK i.2.2.1 i.2.2.2 i.2.1.1 i.2.1.2 i.1.1 i.1.2 ω) ≤ B := by
    rintro ⟨⟨U, R⟩, ⟨a0, a1⟩, ⟨b0, b1⟩⟩
    by_cases hc : AdmUR U R ∧ (a0 ≠ 0 ∨ a1 ≠ 0)
    · obtain ⟨⟨hU1, hU, hRU, hR⟩, ha⟩ := hc
      exact (prob_mono fun ω hω => hω.2).trans (prob_BK_le hp2 b0 b1 a0 a1 U R hRU ha hm hU1 hU hR)
    · rw [prob_congr (Q := fun _ => False) fun ω => ⟨fun h => hc h.1, False.elim⟩, prob_false]
      exact hB0
  have hcard : (Fintype.card (PSIdx m p) : ℝ) = 2 ^ m * 2 ^ m * (p : ℝ) ^ 4 := by
    simp only [PSIdx, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin, ZMod.card]
    push_cast
    ring
  calc prob (BadPS (m := m) p) ≤ ∑ i : PSIdx m p, prob (fun ω => (AdmUR i.1.1 i.1.2 ∧
        (i.2.1.1 ≠ 0 ∨ i.2.1.2 ≠ 0)) ∧ BK i.2.2.1 i.2.2.2 i.2.1.1 i.2.1.2 i.1.1 i.1.2 ω) := h1
    _ ≤ ∑ _i : PSIdx m p, B := Finset.sum_le_sum fun i _ => h2 i
    _ = (Fintype.card (PSIdx m p) : ℝ) * B := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 2 ^ m * 2 ^ m * (p : ℝ) ^ 4 * B := by rw [hcard]

end OneChoice

def GoodPS (m : ℕ) (ω : Pairs m → Bool) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) →
    ∀ U R : Finset (Fin m), AdmUR U R → ∀ a0 a1 b0 b1 : ZMod p, (a0 ≠ 0 ∨ a1 ≠ 0) →
      (Rᶜ.card : ℝ) + 0.13 * m ≤ (Kof p b0 b1 a0 a1 U R ω).rank

theorem pencil_numeric : ∀ᶠ m : ℕ in atTop,
    (Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) + 1) * (2 ^ m * 2 ^ m * Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) ^ 4 *
      (32 * 2 ^ m * (2 : ℝ) ^ (-((((m / 100 + 1) * (m / 100 + 1) : ℕ) : ℝ) / 4)))) ≤
        Real.exp (-(m : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1000000] with m hm
  set X := Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) with hX
  have hmR : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hrp : (m : ℝ) ^ ((1 : ℝ) / 8) ≤ m := by
    calc (m : ℝ) ^ ((1 : ℝ) / 8) ≤ (m : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = m := Real.rpow_one _
  have hX1 : X ≤ Real.exp m := Real.exp_le_exp.2 hrp
  have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h2m : (2 : ℝ) ^ m ≤ Real.exp m := by
    calc (2 : ℝ) ^ m ≤ Real.exp 1 ^ m := pow_le_pow_left₀ (by norm_num) (by linarith) m
      _ = Real.exp m := by rw [← Real.exp_nat_mul, mul_one]
  have hX4 : X ^ 4 ≤ Real.exp (4 * m) := by
    calc X ^ 4 ≤ Real.exp m ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le hX1 4
      _ = Real.exp (4 * m) := by rw [← Real.exp_nat_mul]; norm_num
  have hX1' : X + 1 ≤ Real.exp (m + 1) := by
    have h1 : 1 ≤ Real.exp m := Real.one_le_exp (by linarith)
    calc X + 1 ≤ 2 * Real.exp m := by linarith
      _ ≤ Real.exp 1 * Real.exp m := by gcongr; linarith
      _ = Real.exp (m + 1) := by rw [← Real.exp_add]; ring_nf
  have h32 : (32 : ℝ) ≤ Real.exp 4 := by
    calc (32 : ℝ) ≤ 2.7 ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he1 4
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
  set N : ℕ := (m / 100 + 1) * (m / 100 + 1) with hN
  have hN1 : (m : ℝ) / 100 ≤ ((m / 100 + 1 : ℕ) : ℝ) := by
    have h1 : m < 100 * (m / 100 + 1) := by omega
    have h' : (m : ℝ) < ((100 * (m / 100 + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h' ⊢
    linarith
  have hNm : 100 * (m : ℝ) ≤ N := by
    have e : ((N : ℕ) : ℝ) = ((m / 100 + 1 : ℕ) : ℝ) * ((m / 100 + 1 : ℕ) : ℝ) := by
      rw [hN]
      push_cast
      ring
    rw [e]
    have h0 : (0 : ℝ) ≤ (m : ℝ) / 100 := by positivity
    calc 100 * (m : ℝ) ≤ ((m : ℝ) / 100) * ((m : ℝ) / 100) := by nlinarith
      _ ≤ _ := mul_le_mul hN1 hN1 h0 (h0.trans hN1)
  have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hE : (2 : ℝ) ^ (-((N : ℝ) / 4)) ≤ Real.exp (-(0.69 * N / 4)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.2
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  calc (X + 1) * (2 ^ m * 2 ^ m * X ^ 4 * (32 * 2 ^ m * (2 : ℝ) ^ (-((N : ℝ) / 4))))
      ≤ Real.exp (m + 1) * (Real.exp m * Real.exp m * Real.exp (4 * m) *
          (Real.exp 4 * Real.exp m * Real.exp (-(0.69 * N / 4)))) := by gcongr
    _ = Real.exp (8 * m + 5 - 0.69 * N / 4) := by
        simp only [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-(m : ℝ)) := Real.exp_le_exp.2 (by linarith)

theorem lem_pencilsupp : ∀ᶠ m : ℕ in atTop,
    prob (fun ω : Pairs m → Bool => ¬ GoodPS m ω) ≤ Real.exp (-(m : ℝ)) := by
  filter_upwards [pencil_numeric, eventually_ge_atTop 34] with m hnum hm
  classical
  set X : ℝ := Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) with hX
  set PS := (range (⌊X⌋₊ + 1)).filter (fun p => p.Prime ∧ 23 ≤ p) with hPS
  set B : ℝ := 2 ^ m * 2 ^ m * X ^ 4 *
    (32 * 2 ^ m * (2 : ℝ) ^ (-((((m / 100 + 1) * (m / 100 + 1) : ℕ) : ℝ) / 4))) with hB
  have hB0 : 0 ≤ B := by positivity
  let Bad : ℕ → (Pairs m → Bool) → Prop := fun p ω => ∃ h : Fact p.Prime, @BadPS m p h ω
  have hsub : ∀ ω : Pairs m → Bool, ¬ GoodPS m ω → ∃ p ∈ PS, Bad p ω := by
    intro ω hω
    unfold GoodPS at hω
    push Not at hω
    obtain ⟨p, hpF, hp23, hpX, U, R, hUR, a0, a1, b0, b1, ha, hlt⟩ := hω
    refine ⟨p, ?_, hpF, ((U, R), ((a0, a1), (b0, b1))), ⟨hUR, ha⟩, hlt⟩
    rw [hPS, mem_filter, mem_range]
    refine ⟨?_, hpF.out, hp23⟩
    have : p ≤ ⌊X⌋₊ := Nat.le_floor hpX
    omega
  have hbad : ∀ p ∈ PS, prob (Bad p) ≤ B := by
    intro p hp
    rw [hPS, mem_filter, mem_range] at hp
    have : Fact p.Prime := ⟨hp.2.1⟩
    have hp2 : p ≠ 2 := by have := hp.2.2; omega
    have hpX : (p : ℝ) ≤ X := by
      have h1 : p ≤ ⌊X⌋₊ := by omega
      exact (Nat.le_floor_iff (Real.exp_pos _).le).1 h1
    have h1 : prob (Bad p) ≤ prob (BadPS (m := m) p) := prob_mono fun ω ⟨_, h⟩ => h
    refine h1.trans ((prob_BadPS_le hp2 hm).trans ?_)
    rw [hB]
    gcongr
  have hcard : (PS.card : ℝ) ≤ X + 1 := by
    have h1 : PS.card ≤ ⌊X⌋₊ + 1 := (card_filter_le _ _).trans (card_range _).le
    have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le (Real.exp_pos _).le
    have h3 : (PS.card : ℝ) ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  calc prob (fun ω : Pairs m → Bool => ¬ GoodPS m ω) ≤ prob (fun ω => ∃ p ∈ PS, Bad p ω) :=
        prob_mono hsub
    _ ≤ ∑ p ∈ PS, prob (Bad p) := prob_exists_le_sum _ _
    _ ≤ ∑ _p ∈ PS, B := sum_le_sum hbad
    _ = PS.card * B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (X + 1) * B := by gcongr
    _ ≤ Real.exp (-(m : ℝ)) := hnum

theorem commute_QAm_PAm {F : Type*} [Field F] (b0 b1 a0 a1 : F) (A : Matrix (Fin m) (Fin m) F) :
    Commute (QAm b0 b1 A) (PAm a0 a1 A) := by
  have hA : Commute A (PAm a0 a1 A) :=
    ((Commute.refl A).smul_right a1).add_right ((Commute.one_right A).smul_right a0)
  exact ((hA.mul_left hA).add_left (hA.smul_left b1)).add_left ((Commute.one_left _).smul_left b0)

theorem rank_CRU_of_goodPS {ω : Pairs m → Bool} (hω : GoodPS m ω) {p : ℕ} [Fact p.Prime] (hp23 : 23 ≤ p)
    (hpX : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) {U R : Finset (Fin m)} (hUR : AdmUR U R)
    {a0 a1 b0 b1 : ZMod p} (ha : a0 ≠ 0 ∨ a1 ≠ 0)
    (hQ : IsUnit (QAm b0 b1 (modP p (seidelOf ω))).det) :
    0.13 * (m : ℝ) ≤ (diagSet R * (PAm a0 a1 (modP p (seidelOf ω)) *
      (QAm b0 b1 (modP p (seidelOf ω)))⁻¹) * diagSet U).rank := by
  set A := modP p (seidelOf ω) with hA
  have hQC : QAm b0 b1 A * (PAm a0 a1 A * (QAm b0 b1 A)⁻¹) = PAm a0 a1 A := by
    rw [← mul_assoc, (commute_QAm_PAm b0 b1 a0 a1 A).eq, mul_assoc, mul_nonsing_inv _ hQ, mul_one]
  have h1 := rank_Kmat_le (QAm b0 b1 A) (PAm a0 a1 A) _ hQC R U (eRcOf R) (eRcOf_injective R)
    (not_mem_iff_eRcOf R) (eUOf U) (eUOf_injective U) (mem_iff_eUOf U)
  have h2 : (Rᶜ.card : ℝ) + 0.13 * m ≤
      ((Kmat (QAm b0 b1 A) (PAm a0 a1 A) (eRcOf R) (eUOf U)).rank : ℝ) :=
    hω p hp23 hpX U R hUR a0 a1 b0 b1 ha
  have h3 : ((Kmat (QAm b0 b1 A) (PAm a0 a1 A) (eRcOf R) (eUOf U)).rank : ℝ) ≤
      ((diagSet R * (PAm a0 a1 A * (QAm b0 b1 A)⁻¹) * diagSet U).rank : ℝ) + Rᶜ.card := by
    exact_mod_cast h1
  linarith

end DGS
