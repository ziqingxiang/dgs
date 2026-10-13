module

public import DGS.S12_Deg2.SEdNum
public import DGS.S03_Prelim.SuppD

@[expose] public section

open Finset Matrix Polynomial Filter Topology
open scoped Real

namespace DGS

section OnePrime

variable {p : ℕ} [Fact p.Prime]

omit [Fact (Nat.Prime p)] in
theorem sed_levels_facts {n : ℕ} (hp : 2 ≤ p) :
    1 < (2 : ℝ) ^ ((n + 1) * (Nat.log 2 p + 1)) * ((1 + 1 / 100) / (p : ℝ) ^ (n + 1)) := by
  have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : p < 2 ^ (Nat.log 2 p + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
  have h1R : (p : ℝ) < 2 ^ (Nat.log 2 p + 1) := by exact_mod_cast h1
  have e : (2 : ℝ) ^ ((n + 1) * (Nat.log 2 p + 1)) = (2 ^ (Nat.log 2 p + 1)) ^ (n + 1) := by
    rw [← pow_mul, mul_comm]
  rw [e, mul_div_assoc', lt_div_iff₀ (by positivity)]
  have : (p : ℝ) ^ (n + 1) < (2 ^ (Nat.log 2 p + 1)) ^ (n + 1) := pow_lt_pow_left₀ h1R hp0.le (by omega)
  have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ (Nat.log 2 p + 1)) ^ (n + 1) := by positivity
  nlinarith

omit [Fact (Nat.Prime p)] in
theorem sed_Abound {t : ℝ} {m n : ℕ} (hn3 : n ≤ 3) (ht : 20000 ≤ t) (hm : t ^ 16 ≤ m)
    (hp : 2 ≤ p) (hlogp : Real.log p ≤ 2 * t ^ 2) :
    (((n + 1) * (Nat.log 2 p + 1) : ℕ) : ℝ) ≤ Real.exp (0.01 * m) := by
  have hlog2p := (levels_facts (p := p) hp).2
  have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h0 : (0 : ℝ) ≤ ((Nat.log 2 p : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((Nat.log 2 p : ℕ) : ℝ) * 0.69 ≤ ((Nat.log 2 p : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2 h0
  have ht0 : 0 < t := by linarith
  have h2 : t ^ 2 ≤ t ^ 14 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h3 : (10 ^ 8 : ℝ) ≤ t ^ 2 := by nlinarith
  have h4 : 10 ^ 8 * t ^ 2 ≤ t ^ 2 * t ^ 14 := by nlinarith
  have e : t ^ 2 * t ^ 14 = t ^ 16 := by ring
  have h5 := Real.add_one_le_exp (0.01 * (m : ℝ))
  have hn3R : (n : ℝ) ≤ 3 := by exact_mod_cast hn3
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  nlinarith

theorem sed_kL1 {t : ℝ} {m : ℕ} (ht : 20000 ≤ t) (hm : t ^ 16 ≤ m) :
    4 * (2 * t ^ 2) * (t ^ 13 + 1) ≤ 0.01 * m := by
  have ht0 : 0 < t := by linarith
  have h1 : t ^ 2 ≤ t ^ 15 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h3 : 20000 * t ^ 15 ≤ t * t ^ 15 := mul_le_mul_of_nonneg_right ht (by positivity)
  have e : t * t ^ 15 = t ^ 16 := by ring
  have e2 : 4 * (2 * t ^ 2) * (t ^ 13 + 1) = 8 * t ^ 15 + 8 * t ^ 2 := by ring
  rw [e2]
  linarith

theorem sed_kL2 {t : ℝ} {m V : ℕ} (htV : t = V) (ht : 20000 ≤ t) (hm : t ^ 16 ≤ m) :
    4 * (2 * t ^ 2) * (((3 * V ^ 13 + V ^ 10 * (m / V ^ 13) : ℕ) : ℝ) + 1) ≤ 0.01 * m := by
  have ht0 : 0 < t := by linarith
  set q : ℝ := ((m / V ^ 13 : ℕ) : ℝ) with hq
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hqm : q * t ^ 13 ≤ m := by
    have h1 : (m / V ^ 13) * V ^ 13 ≤ m := Nat.div_mul_le_self m _
    have h2 : (((m / V ^ 13) * V ^ 13 : ℕ) : ℝ) ≤ m := by exact_mod_cast h1
    push_cast at h2
    rw [hq, htV]
    exact h2
  have e : 4 * (2 * t ^ 2) * (((3 * V ^ 13 + V ^ 10 * (m / V ^ 13) : ℕ) : ℝ) + 1) =
      24 * t ^ 15 + 8 * (t ^ 12 * q) + 8 * t ^ 2 := by
    push_cast
    rw [← hq, ← htV]
    ring
  rw [e]
  have h2 : t ^ 2 ≤ t ^ 15 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h3 : 20000 * t ^ 15 ≤ t * t ^ 15 := mul_le_mul_of_nonneg_right ht (by positivity)
  have h4 : 20000 * (t ^ 12 * q) ≤ t * (t ^ 12 * q) := mul_le_mul_of_nonneg_right ht (by positivity)
  have e3 : t * t ^ 15 = t ^ 16 := by ring
  have e4 : t * (t ^ 12 * q) = q * t ^ 13 := by ring
  linarith

set_option maxHeartbeats 1000000 in
theorem sed_prime_le {m n : ℕ} (hn : 1 ≤ n) (hn3 : n ≤ 3) (hV : Real.exp 200 ≤ (ptV m : ℝ))
    (hm : 100000 ≤ m) (hp23 : 23 ≤ p) (hpX : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (hp4 : 2 ≤ n → (ptV m : ℝ) ^ 4 ≤ p) :
    ∑ b : Fin (n + 1) → ZMod p, prob (fun ω : Pairs m → Bool => ∃ w : Fin m → Fin (n + 1) → ZMod p,
        krySys ω b w ∧ m ≤ 20 * (univ.filter fun j => w j 0 ≠ 0).card ∧
        (normSqLift (fun j => w j 0) : ℝ) ≤ cSEd * m * (p : ℝ) ^ 2) ≤ Real.exp (-(m : ℝ) / 2) := by
  classical
  set V := ptV m with hVdef
  set t : ℝ := (V : ℝ) with ht
  have he : (201 : ℝ) ≤ Real.exp 200 := by have := Real.add_one_le_exp (200 : ℝ); linarith
  have ht201 : 201 ≤ t := he.trans hV
  have hV201 : 201 ≤ V := by
    have h' : (201 : ℝ) ≤ (V : ℝ) := ht201
    exact_mod_cast h'
  have hV16 : V ^ 16 ≤ m := ptV_pow_le m
  have hV16R : t ^ 16 ≤ m := by
    have : ((V ^ 16 : ℕ) : ℝ) ≤ m := by exact_mod_cast hV16
    push_cast at this
    exact this
  have hp23R : (23 : ℝ) ≤ p := by exact_mod_cast hp23
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : Real.log p ≤ 2 * t ^ 2 := log_le_ptV (by omega) (by omega) hpX
  have H := sed_BDHyp hn hn3 hV hp23 hlogp hp4
  have hsk : V ^ 10 ≤ V ^ 13 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hk : 0 < V ^ 13 := by positivity
  have hkm : V ^ 13 ≤ m := le_trans (Nat.pow_le_pow_right (by omega) (by norm_num)) hV16
  have hMB := sed_hMB (V := V) (by omega) hV16
  set σ : ℝ := 1 / (2 * cSEd * (p : ℝ) ^ 2) with hσ
  have hσ0 : 0 < σ := by have := cSEd_pos; positivity
  have hA := sed_levels_facts (p := p) (n := n) (by omega)
  have hμ0 : muP p σ ≤ Real.exp (-149) * p := by
    have h1 := (lem_gauss (p := p) cSEd_pos cSEd_le).2.1
    have h2 := muP_le_gaussMu0 (p := p) hσ0
    calc muP p σ ≤ gaussMu0 p σ := h2
      _ ≤ √(2 * π * cSEd) * p := h1
      _ ≤ Real.exp (-149) * p := by gcongr; exact sqrt_two_pi_cSEd_le
  have hμpos := muP_pos (p := p) σ
  have hgam := pt_gam0_le hV
  have hβ' : gam0 (V ^ 2 + 50) (V ^ 10) + 1.21 * muP p σ / p ≤ Real.exp (-148) := by
    have h1 : 1.21 * muP p σ / p ≤ 1.21 * Real.exp (-149) := by
      rw [div_le_iff₀ hp0]
      nlinarith
    have h2 : Real.exp (-760) ≤ Real.exp (-149) := Real.exp_le_exp.2 (by norm_num)
    have h3 : 2.21 * Real.exp (-149) ≤ Real.exp (-148) := by
      have e : Real.exp (-148) = Real.exp 1 * Real.exp (-149) := by rw [← Real.exp_add]; norm_num
      rw [e]
      have := Real.exp_one_gt_d9
      nlinarith [Real.exp_pos (-149)]
    linarith
  have hβ1 : gam0 (V ^ 2 + 50) (V ^ 10) + 1.21 * muP p σ / p ≤ 1 :=
    hβ'.trans (by rw [Real.exp_le_one_iff]; norm_num)
  have hγ : gam0 (V ^ 2 + 50) (V ^ 10) ≤ 0.02 := by
    have h1 : Real.exp (-760) ≤ 0.02 := by
      rw [Real.exp_neg]
      have := Real.add_one_le_exp (760 : ℝ)
      rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      norm_num
      linarith
    linarith
  have hone := fun b => prob_krySys_short_le (m := m) hn H hsk hk (by omega) hσ0 (cSEd * m * (p : ℝ) ^ 2) b
    hMB hA hγ hβ1
  have hσR : σ * (cSEd * m * (p : ℝ) ^ 2) = (m : ℝ) / 2 := by
    rw [hσ]
    have := cSEd_pos
    field_simp
  have ht2 : (20000 : ℝ) ≤ t := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 200)
    norm_num at this
    linarith
  have hkL1 : 4 * (2 * t ^ 2) * (((V ^ 13 : ℕ) : ℝ) + 1) ≤ 0.01 * m := by
    have := sed_kL1 ht2 hV16R
    push_cast
    exact this
  have hkL2 := sed_kL2 (m := m) (V := V) rfl ht2 hV16R
  have hA' := sed_Abound (n := n) hn3 ht2 hV16R (by omega) hlogp
  have hsmall : Real.exp (-149) ≤ 0.0006 := by
    rw [Real.exp_neg]
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 149)
    norm_num at this
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    linarith
  have hμ6 : muP p σ ≤ 0.0006 * p := hμ0.trans (mul_le_mul_of_nonneg_right hsmall hp0.le)
  have hT1 := sed_T1 (m := m) (k := V ^ 13) (n := n) (L := 2 * t ^ 2) hn3 hp23 hlogp hμpos.le
    hμ6 hkm hkL1 (by omega)
  have hT2 := sed_T2 (m := m) (k := V ^ 13) (s := V ^ 10) (A := (n + 1) * (Nat.log 2 p + 1)) (n := n)
    (L := 2 * t ^ 2) (β := gam0 (V ^ 2 + 50) (V ^ 10) + 1.21 * muP p σ / p) hn3 hp23 hlogp
    (by have : 0 ≤ gam0 (V ^ 2 + 50) (V ^ 10) := by unfold gam0; positivity
        positivity) hβ' hA' hkL2 hm
  set Bnd : ℝ := Real.exp (σ * (cSEd * m * (p : ℝ) ^ 2)) * (((p : ℝ) ^ n * (1 + muP p σ)) ^ m *
      ((1 + 1 / 100) / (p : ℝ) ^ (n + 1)) ^ (m - V ^ 13) +
    3 ^ m * ((((n + 1) * (Nat.log 2 p + 1) : ℕ) : ℝ) * (2 ^ m * ((p : ℝ) ^ (n + 1)) ^
      (3 * V ^ 13 + V ^ 10 * (m / V ^ 13)) * 1.23 ^ m *
      (gam0 (V ^ 2 + 50) (V ^ 10) + 1.21 * muP p σ / p) ^ (m / 40)))) with hBnd
  calc ∑ b : Fin (n + 1) → ZMod p, prob (fun ω : Pairs m → Bool => ∃ w : Fin m → Fin (n + 1) → ZMod p,
        krySys ω b w ∧ m ≤ 20 * (univ.filter fun j => w j 0 ≠ 0).card ∧
        (normSqLift (fun j => w j 0) : ℝ) ≤ cSEd * m * (p : ℝ) ^ 2)
      ≤ ∑ _b : Fin (n + 1) → ZMod p, Bnd := sum_le_sum fun b _ => hone b
    _ = (p : ℝ) ^ (n + 1) * Bnd := by
        rw [sum_const, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ = (p : ℝ) ^ (n + 1) * (Real.exp ((m : ℝ) / 2) * (((p : ℝ) ^ n * (1 + muP p σ)) ^ m *
          ((1 + 1 / 100) / (p : ℝ) ^ (n + 1)) ^ (m - V ^ 13))) +
        (p : ℝ) ^ (n + 1) * (Real.exp ((m : ℝ) / 2) * (3 ^ m * ((((n + 1) * (Nat.log 2 p + 1) : ℕ) : ℝ) *
          (2 ^ m * ((p : ℝ) ^ (n + 1)) ^ (3 * V ^ 13 + V ^ 10 * (m / V ^ 13)) * 1.23 ^ m *
            (gam0 (V ^ 2 + 50) (V ^ 10) + 1.21 * muP p σ / p) ^ (m / 40))))) := by
        rw [hBnd, hσR]
        ring
    _ ≤ Real.exp (-(m : ℝ) / 2) / 2 + Real.exp (-(m : ℝ) / 2) / 2 := add_le_add hT1 hT2
    _ = Real.exp (-(m : ℝ) / 2) := by ring

end OnePrime

section Krylov

variable {p : ℕ} [Fact p.Prime] {m n : ℕ}

def kryRows (A : Matrix (Fin m) (Fin m) (ZMod p)) (y : Fin m → ZMod p) : Fin m → Fin (n + 1) → ZMod p :=
  fun j r => (A ^ (r : ℕ) *ᵥ y) j

theorem kryRows_zero (A : Matrix (Fin m) (Fin m) (ZMod p)) (y : Fin m → ZMod p) (j : Fin m) :
    kryRows (n := n) A y j 0 = y j := by
  simp [kryRows]

theorem aeval_monic_eq {A : Matrix (Fin m) (Fin m) (ZMod p)} {β : (ZMod p)[X]} (hβm : β.Monic)
    (hβd : β.natDegree = n + 1) :
    aeval A β = A ^ (n + 1) + ∑ i : Fin (n + 1), β.coeff i • A ^ (i : ℕ) := by
  conv_lhs => rw [hβm.as_sum, hβd]
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => β.coeff i • A ^ i)]

theorem krySys_kryRows (ω : Pairs m → Bool) {β : (ZMod p)[X]} (hβm : β.Monic) (hβd : β.natDegree = n + 1)
    {y : Fin m → ZMod p} (hy : aeval (modP p (seidelOf ω)) β *ᵥ y = 0) :
    krySys ω (fun i => β.coeff i) (kryRows (n := n) (modP p (seidelOf ω)) y) := by
  set A := modP p (seidelOf ω) with hA
  have hlast : A ^ (n + 1) *ᵥ y = -∑ i : Fin (n + 1), β.coeff i • (A ^ (i : ℕ) *ᵥ y) := by
    rw [aeval_monic_eq hβm hβd, add_mulVec, Matrix.sum_mulVec] at hy
    simp only [smul_mulVec] at hy
    exact eq_neg_of_add_eq_zero_left hy
  intro i
  funext r
  have hL : (∑ j, seidelOf ω i j • kryRows (n := n) A y j) r = (A ^ ((r : ℕ) + 1) *ᵥ y) i := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, kryRows, zsmul_eq_mul]
    rw [pow_succ', ← mulVec_mulVec]
    simp only [mulVec, dotProduct, hA, modP, Matrix.map_apply, Int.coe_castRingHom]
  rw [hL]
  induction r using Fin.lastCases with
  | last =>
    simp only [companion, Fin.snoc_last, Fin.val_last]
    rw [hlast]
    simp [kryRows, Finset.sum_apply]
  | cast r' =>
    simp only [companion, Fin.snoc_castSucc, Fin.tail, kryRows, Fin.val_castSucc, Fin.val_succ]

end Krylov

def GoodSEd (d : ℕ) {m : ℕ} (T : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) →
    (3 ≤ d → (m : ℝ) ^ (0.4 : ℝ) ≤ p) →
    ∀ β : (ZMod p)[X], β.Monic → β.natDegree = d →
      ∀ y : Fin m → ZMod p, y ≠ 0 → aeval (modP p T) β *ᵥ y = 0 → cSEd * m * (p : ℝ) ^ 2 < (muMin y : ℝ)

def SuppGoodPM {m : ℕ} (ω : Pairs m → Bool) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) → ¬ (p : ℤ) ∣ 1 - -1 →
    ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) →
    ∀ g : (ZMod p)[X], g.Monic → g.natDegree = d →
    ∀ y : Fin m → ZMod p, y ≠ 0 → aeval (modP p (symOf 1 (-1) ω)) g *ᵥ y = 0 →
      (m : ℝ) / (4 * (d + 1)) < ((Finset.univ.filter fun i => y i ≠ 0).card : ℝ)

theorem prob_not_suppGoodPM :
    ∀ᶠ m : ℕ in atTop, prob (fun ω : Pairs m → Bool => ¬ SuppGoodPM ω) ≤ Real.exp (-(m : ℝ) / 8) :=
  lem_suppd 1 (-1)

theorem sed_tail {m : ℕ} (hm : 100 ≤ m) :
    (Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) + 1) * Real.exp (-(m : ℝ) / 2) + Real.exp (-(m : ℝ) / 8) ≤
      Real.exp (-(m : ℝ) / 9) := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have h8 : (m : ℝ) ^ ((1 : ℝ) / 8) ≤ (m : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have h2 : (m : ℝ) ^ ((1 : ℝ) / 2) ≤ m / 4 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by positivity)]
    nlinarith
  have hX : Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) + 1 ≤ 2 * Real.exp ((m : ℝ) / 4) := by
    have h3 : Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) ≤ Real.exp ((m : ℝ) / 4) := Real.exp_le_exp.2 (h8.trans h2)
    have h4 : (1 : ℝ) ≤ Real.exp ((m : ℝ) / 4) := Real.one_le_exp (by positivity)
    linarith
  have hA : 2 * Real.exp ((m : ℝ) / 4) * Real.exp (-(m : ℝ) / 2) ≤ Real.exp (-(m : ℝ) / 9) / 2 := by
    have e : 2 * Real.exp ((m : ℝ) / 4) * Real.exp (-(m : ℝ) / 2) =
        Real.exp (-(m : ℝ) / 9) * (2 * Real.exp (-(5 * (m : ℝ) / 36))) := by
      have e1 : Real.exp ((m : ℝ) / 4) * Real.exp (-(m : ℝ) / 2) =
          Real.exp (-(m : ℝ) / 9) * Real.exp (-(5 * (m : ℝ) / 36)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc 2 * Real.exp ((m : ℝ) / 4) * Real.exp (-(m : ℝ) / 2) =
            2 * (Real.exp ((m : ℝ) / 4) * Real.exp (-(m : ℝ) / 2)) := by ring
        _ = Real.exp (-(m : ℝ) / 9) * (2 * Real.exp (-(5 * (m : ℝ) / 36))) := by rw [e1]; ring
    rw [e]
    have h5 : 2 * Real.exp (-(5 * (m : ℝ) / 36)) ≤ 1 / 2 := by
      have h6 : Real.exp (-(5 * (m : ℝ) / 36)) ≤ Real.exp (-4) := Real.exp_le_exp.2 (by linarith)
      have h7 : Real.exp (-4) ≤ 1 / 4 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        have := Real.add_one_le_exp (4 : ℝ)
        linarith
      linarith
    have := Real.exp_pos (-(m : ℝ) / 9)
    nlinarith
  have hB : Real.exp (-(m : ℝ) / 8) ≤ Real.exp (-(m : ℝ) / 9) / 2 := by
    have e : Real.exp (-(m : ℝ) / 8) = Real.exp (-(m : ℝ) / 9) * Real.exp (-((m : ℝ) / 72)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [e]
    have h6 : Real.exp (-((m : ℝ) / 72)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    have h7 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have := Real.exp_pos (-(m : ℝ) / 9)
    nlinarith
  calc (Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) + 1) * Real.exp (-(m : ℝ) / 2) + Real.exp (-(m : ℝ) / 8)
      ≤ 2 * Real.exp ((m : ℝ) / 4) * Real.exp (-(m : ℝ) / 2) + Real.exp (-(m : ℝ) / 8) := by
        gcongr
    _ ≤ Real.exp (-(m : ℝ) / 9) / 2 + Real.exp (-(m : ℝ) / 9) / 2 := add_le_add hA hB
    _ = Real.exp (-(m : ℝ) / 9) := by ring

theorem sed_rpow_facts {m : ℕ} (hm : 256 ≤ m) :
    (ptV m : ℝ) ^ 4 ≤ (m : ℝ) ^ (0.4 : ℝ) ∧ (4 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := by
  have hmR : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  constructor
  · have h1 := ptV_le_rpow m
    have h2 : (ptV m : ℝ) ^ 4 ≤ ((m : ℝ) ^ ((1 : ℝ) / 16)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 4
    have h3 : ((m : ℝ) ^ ((1 : ℝ) / 16)) ^ 4 = (m : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]
      norm_num
    rw [h3] at h2
    exact h2.trans (Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num))
  · have h := Real.rpow_le_rpow (by norm_num) hmR (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have e : (256 : ℝ) ^ ((1 : ℝ) / 4) = 4 := by
      rw [show (256 : ℝ) = 4 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [e] at h

theorem prop_SEd {d : ℕ} (hd2 : 2 ≤ d) (hd4 : d ≤ 4) :
    ∀ᶠ m : ℕ in atTop, probSeidel m (fun T => ¬ GoodSEd d T) ≤ Real.exp (-(m : ℝ) / 9) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hn3 : n ≤ 3 := by omega
  have hVev : ∀ᶠ m : ℕ in atTop, Real.exp 200 ≤ (ptV m : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp tendsto_ptV).eventually_ge_atTop _
  filter_upwards [prob_not_suppGoodPM, hVev, eventually_ge_atTop 100000] with m hsupp hV hm
  classical
  obtain ⟨hV4, h4⟩ := sed_rpow_facts (m := m) (by omega)
  set X : ℝ := Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) with hX
  set PS := (range (⌊X⌋₊ + 1)).filter (fun p => p.Prime ∧ 23 ≤ p) with hPS
  let Bad : ℕ → (Pairs m → Bool) → Prop := fun p ω => ∃ _ : Fact p.Prime,
    (2 ≤ n → (ptV m : ℝ) ^ 4 ≤ p) ∧ ∃ b : Fin (n + 1) → ZMod p, ∃ w : Fin m → Fin (n + 1) → ZMod p,
      krySys ω b w ∧ m ≤ 20 * (univ.filter fun j => w j 0 ≠ 0).card ∧
      (normSqLift (fun j => w j 0) : ℝ) ≤ cSEd * m * (p : ℝ) ^ 2
  have hsub : ∀ ω : Pairs m → Bool, ¬ GoodSEd (n + 1) (seidelOf ω) →
      ¬ SuppGoodPM ω ∨ ∃ p ∈ PS, Bad p ω := by
    intro ω hω
    by_cases hS : SuppGoodPM ω
    · right
      unfold GoodSEd at hω
      push Not at hω
      obtain ⟨p, hpF, hp23, hpX, hp04, β, hβm, hβd, y, hy0, hβy, hle⟩ := hω
      have hp : p.Prime := hpF.out
      refine ⟨p, ?_, hpF, fun h2 => hV4.trans (hp04 (by omega)), ?_⟩
      · rw [hPS, mem_filter, mem_range]
        refine ⟨?_, hp, hp23⟩
        have : p ≤ ⌊X⌋₊ := Nat.le_floor hpX
        omega
      · obtain ⟨c, hc, hmu⟩ := exists_muMin_eq y
        set y' : Fin m → ZMod p := fun j => c * y j with hy'
        have hy'0 : y' ≠ 0 := by
          intro h0
          apply hy0
          funext j
          have := congrFun h0 j
          simp only [hy', Pi.zero_apply, mul_eq_zero] at this
          exact this.resolve_left hc
        have hβy' : aeval (modP p (seidelOf ω)) β *ᵥ y' = 0 := by
          have : y' = c • y := rfl
          rw [this, mulVec_smul, hβy, smul_zero]
        have hsupp' := hS p hp hpX (by
            intro hdvd
            have h2 : (p : ℤ) ∣ 2 := by simpa using hdvd
            have h3 : p ∣ 2 := by exact_mod_cast h2
            have := Nat.le_of_dvd (by norm_num) h3
            omega) (n + 1) (by omega) (by
            have : ((n + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (by omega : n + 1 ≤ 4)
            linarith) β hβm hβd y' hy'0 hβy'
        refine ⟨fun i => β.coeff i, kryRows (n := n) (modP p (seidelOf ω)) y',
          krySys_kryRows ω hβm hβd hβy', ?_, ?_⟩
        · have hset : (univ.filter fun j => kryRows (n := n) (modP p (seidelOf ω)) y' j 0 ≠ 0) =
              univ.filter fun j => y' j ≠ 0 := by
            simp only [kryRows_zero]
          rw [hset]
          have h20 : (m : ℝ) / 20 ≤ (m : ℝ) / (4 * (((n + 1 : ℕ) : ℝ) + 1)) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            have : ((n + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (by omega : n + 1 ≤ 4)
            linarith
          have h21 : (m : ℝ) < 20 * ((univ.filter fun j => y' j ≠ 0).card : ℝ) := by
            have := h20.trans_lt hsupp'
            linarith
          have : m < 20 * (univ.filter fun j => y' j ≠ 0).card := by exact_mod_cast h21
          omega
        · have e : normSqLift (fun j => kryRows (n := n) (modP p (seidelOf ω)) y' j 0) = muMin y := by
            simp only [kryRows_zero]
            rw [hmu]
          rw [e]
          exact hle
    · exact Or.inl hS
  have hbad : ∀ p ∈ PS, prob (Bad p) ≤ Real.exp (-(m : ℝ) / 2) := by
    intro p hp
    rw [hPS, mem_filter, mem_range] at hp
    have : Fact p.Prime := ⟨hp.2.1⟩
    have hpX : (p : ℝ) ≤ X := by
      have h1 : p ≤ ⌊X⌋₊ := by omega
      exact (Nat.le_floor_iff (Real.exp_pos _).le).1 h1
    by_cases hp4 : 2 ≤ n → (ptV m : ℝ) ^ 4 ≤ p
    · have h1 : prob (Bad p) ≤ ∑ b : Fin (n + 1) → ZMod p, prob (fun ω : Pairs m → Bool =>
          ∃ w : Fin m → Fin (n + 1) → ZMod p, krySys ω b w ∧
            m ≤ 20 * (univ.filter fun j => w j 0 ≠ 0).card ∧
            (normSqLift (fun j => w j 0) : ℝ) ≤ cSEd * m * (p : ℝ) ^ 2) := by
        refine (prob_mono fun ω hω => ?_).trans (prob_exists_le_sum_fintype _)
        obtain ⟨hF, -, b, w, h1, h2, h3⟩ := hω
        exact ⟨b, w, h1, h2, h3⟩
      exact h1.trans (sed_prime_le hn hn3 hV hm hp.2.2 hpX hp4)
    · rw [prob_congr (Q := fun _ => False) fun ω => ⟨fun h => hp4 h.2.1, False.elim⟩, prob_false]
      exact (Real.exp_pos _).le
  have hcard : (PS.card : ℝ) ≤ X + 1 := by
    have h1 : PS.card ≤ ⌊X⌋₊ + 1 := (card_filter_le _ _).trans (card_range _).le
    have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le (Real.exp_pos _).le
    have h3 : (PS.card : ℝ) ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  have htail := sed_tail (m := m) (by omega)
  calc probSeidel m (fun T => ¬ GoodSEd (n + 1) T)
      ≤ prob (fun ω : Pairs m → Bool => ¬ SuppGoodPM ω ∨ ∃ p ∈ PS, Bad p ω) := prob_mono hsub
    _ ≤ prob (fun ω : Pairs m → Bool => ¬ SuppGoodPM ω) + prob (fun ω => ∃ p ∈ PS, Bad p ω) :=
        prob_or_le _ _
    _ ≤ Real.exp (-(m : ℝ) / 8) + ∑ p ∈ PS, prob (Bad p) := add_le_add hsupp (prob_exists_le_sum _ _)
    _ ≤ Real.exp (-(m : ℝ) / 8) + ∑ _p ∈ PS, Real.exp (-(m : ℝ) / 2) := add_le_add le_rfl (sum_le_sum hbad)
    _ = Real.exp (-(m : ℝ) / 8) + PS.card * Real.exp (-(m : ℝ) / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (-(m : ℝ) / 8) + (X + 1) * Real.exp (-(m : ℝ) / 2) := by gcongr
    _ ≤ Real.exp (-(m : ℝ) / 9) := by rw [hX]; linarith

end DGS
