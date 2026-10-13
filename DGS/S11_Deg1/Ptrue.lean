module

public import DGS.S11_Deg1.PtReduce
public import DGS.S11_Deg1.Rankp
public import DGS.S11_Deg1.Isocond
public import DGS.S11_Deg1.Deg1

@[expose] public section

open Finset Matrix Polynomial Filter Topology
open scoped Real

namespace DGS

section Psi

variable {p : ℕ} [Fact p.Prime]

theorem sqrt_two_pi_cPT_le : √(2 * π * cPT) ≤ Real.exp (-749) := by
  rw [Real.sqrt_le_left (Real.exp_pos _).le, ← Real.exp_nat_mul]
  unfold cPT
  have h1 : 2 * π ≤ Real.exp 2 := by
    have h := Real.pi_lt_d2
    have h2 : (7.3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 : (2.718 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      rw [e]
      nlinarith
    linarith
  calc 2 * π * Real.exp (-1500) ≤ Real.exp 2 * Real.exp (-1500) := by gcongr
    _ = Real.exp (((2 : ℕ) : ℝ) * (-749)) := by rw [← Real.exp_add]; norm_num

omit [Fact (Nat.Prime p)] in
theorem levels_facts (hp : 2 ≤ p) :
    1 < (2 : ℝ) ^ (2 * Nat.log 2 p + 2) * ((1 + 1 / 100) / (p : ℝ) ^ 2) ∧
      ((Nat.log 2 p : ℕ) : ℝ) * Real.log 2 ≤ Real.log p := by
  have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : p < 2 ^ (Nat.log 2 p + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
  have h1R : (p : ℝ) < 2 ^ (Nat.log 2 p + 1) := by exact_mod_cast h1
  have h2 : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 (by omega)
  have h2R : (2 : ℝ) ^ Nat.log 2 p ≤ p := by exact_mod_cast h2
  constructor
  · have e : (2 : ℝ) ^ (2 * Nat.log 2 p + 2) = (2 ^ (Nat.log 2 p + 1)) ^ 2 := by ring
    rw [e, mul_div_assoc', lt_div_iff₀ (by positivity)]
    have : (p : ℝ) ^ 2 < (2 ^ (Nat.log 2 p + 1)) ^ 2 := pow_lt_pow_left₀ h1R hp0.le (by norm_num)
    nlinarith
  · rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2R

theorem pt_kL1 {t : ℝ} {m : ℕ} (ht : 20000 ≤ t) (hm : t ^ 16 ≤ m) :
    2 * (2 * t ^ 2) * (t ^ 13 + 1) ≤ 0.01 * m := by
  have ht0 : 0 < t := by linarith
  have h1 : t ^ 2 ≤ t ^ 15 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h3 : 20000 * t ^ 15 ≤ t * t ^ 15 := mul_le_mul_of_nonneg_right ht (by positivity)
  have e : t * t ^ 15 = t ^ 16 := by ring
  have e2 : 2 * (2 * t ^ 2) * (t ^ 13 + 1) = 4 * t ^ 15 + 4 * t ^ 2 := by ring
  rw [e2]
  linarith

theorem pt_kL2 {t : ℝ} {m V : ℕ} (htV : t = V) (ht : 20000 ≤ t) (hm : t ^ 16 ≤ m) :
    2 * (2 * t ^ 2) * (((4 * V ^ 13 + V ^ 10 * (m / V ^ 13) : ℕ) : ℝ) + 1) ≤ 0.01 * m := by
  have ht0 : 0 < t := by linarith
  set q : ℝ := ((m / V ^ 13 : ℕ) : ℝ) with hq
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hqm : q * t ^ 13 ≤ m := by
    have h1 : (m / V ^ 13) * V ^ 13 ≤ m := Nat.div_mul_le_self m _
    have h2 : (((m / V ^ 13) * V ^ 13 : ℕ) : ℝ) ≤ m := by exact_mod_cast h1
    push_cast at h2
    rw [hq, htV]
    exact h2
  have e : 2 * (2 * t ^ 2) * (((4 * V ^ 13 + V ^ 10 * (m / V ^ 13) : ℕ) : ℝ) + 1) =
      16 * t ^ 15 + 4 * (t ^ 12 * q) + 4 * t ^ 2 := by
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

theorem pt_Abound {t : ℝ} {m p : ℕ} (ht : 20000 ≤ t) (hm : t ^ 16 ≤ m)
    (hlog2p : ((Nat.log 2 p : ℕ) : ℝ) * Real.log 2 ≤ Real.log p) (hlogp : Real.log p ≤ 2 * t ^ 2) :
    ((2 * Nat.log 2 p + 2 : ℕ) : ℝ) ≤ Real.exp (0.01 * m) := by
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
  push_cast
  nlinarith

set_option maxHeartbeats 1000000 in
theorem psi_le {m : ℕ} (hV : Real.exp 200 ≤ (ptV m : ℝ)) (hm : 100000 ≤ m) (hp23 : 23 ≤ p)
    (hpX : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) (b0 b1 : ZMod p) (U : Finset (Fin m))
    (hU : 5 * U.card ≤ 3 * m) (u : Fin m → ZMod p) :
    prob (fun ω : Pairs m → Bool => PsiEv b0 b1 U u (cPT * m * (p : ℝ) ^ 2) ω) ≤ Real.exp (-(m : ℝ) / 2) := by
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
  have H := pt_BDHyp hV hp23 hlogp
  have hsk : V ^ 10 ≤ V ^ 13 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hk : 0 < V ^ 13 := by positivity
  have hkm : V ^ 13 ≤ m := le_trans (Nat.pow_le_pow_right (by omega) (by norm_num)) hV16
  have hMB := pt_hMB (V := V) (by omega) hV16
  set σ : ℝ := 1 / (2 * cPT * (p : ℝ) ^ 2) with hσ
  have hσ0 : 0 < σ := by have := cPT_pos; positivity
  obtain ⟨hA, hlog2p⟩ := levels_facts (p := p) (by omega)
  have hμ0 : muP p σ ≤ Real.exp (-749) * p := by
    have h1 := (lem_gauss (p := p) cPT_pos cPT_le).2.1
    have h2 := muP_le_gaussMu0 (p := p) hσ0
    calc muP p σ ≤ gaussMu0 p σ := h2
      _ ≤ √(2 * π * cPT) * p := h1
      _ ≤ Real.exp (-749) * p := by gcongr; exact sqrt_two_pi_cPT_le
  have hμpos := muP_pos (p := p) σ
  have hgam := pt_gam0_le hV
  have hβ' : gam0 (V ^ 2 + 50) (V ^ 10) + 1.21 * muP p σ / p ≤ Real.exp (-748) := by
    have h1 : 1.21 * muP p σ / p ≤ 1.21 * Real.exp (-749) := by
      rw [div_le_iff₀ hp0]
      nlinarith
    have h2 : Real.exp (-760) ≤ Real.exp (-749) := Real.exp_le_exp.2 (by norm_num)
    have h3 : 2.21 * Real.exp (-749) ≤ Real.exp (-748) := by
      have e : Real.exp (-748) = Real.exp 1 * Real.exp (-749) := by rw [← Real.exp_add]; norm_num
      rw [e]
      have := Real.exp_one_gt_d9
      nlinarith [Real.exp_pos (-749)]
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
  have hPsi := prob_Psi_le (m := m) H hsk hk hkm (by omega) hσ0 (cPT * m * (p : ℝ) ^ 2) U b0 b1 u hMB hA hγ hβ1
  refine le_trans (le_of_eq (prob_congr fun ω => Iff.rfl)) (hPsi.trans ?_)
  have hσR : σ * (cPT * m * (p : ℝ) ^ 2) = (m : ℝ) / 2 := by
    rw [hσ]
    have := cPT_pos
    field_simp
  have hW : ∏ j : Fin m, (if j ∈ U then (p : ℝ) ^ 2 else p * (1 + muP p σ)) =
      ((p : ℝ) ^ 2) ^ U.card * ((p : ℝ) * (1 + muP p σ)) ^ (m - U.card) := by
    rw [prod_ite, prod_const, prod_const]
    have h1 : (univ.filter fun j => j ∈ U).card = U.card := by rw [filter_mem_eq_inter, univ_inter]
    have h2 : (univ.filter fun j => j ∉ U).card = m - U.card := by
      have h3 := card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (fun j => j ∈ U)
      rw [card_univ, Fintype.card_fin, h1] at h3
      omega
    rw [h1, h2]
  rw [hσR, hW]
  have ht2 : (20000 : ℝ) ≤ t := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 200)
    norm_num at this
    linarith
  have hkL1 : 2 * (2 * t ^ 2) * (((V ^ 13 : ℕ) : ℝ) + 1) ≤ 0.01 * m := by
    have := pt_kL1 ht2 hV16R
    push_cast
    exact this
  have hkL2 := pt_kL2 (m := m) (V := V) rfl ht2 hV16R
  have hA' := pt_Abound ht2 hV16R hlog2p hlogp
  have hsmall : Real.exp (-749) ≤ 0.0006 := by
    rw [Real.exp_neg]
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 749)
    norm_num at this
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    linarith
  have hμ6 : muP p σ ≤ 0.0006 * p := hμ0.trans (mul_le_mul_of_nonneg_right hsmall hp0.le)
  have hT1 := pt_T1 (m := m) (k := V ^ 13) (nU := U.card) (L := 2 * t ^ 2) hp23 hlogp hμpos.le
    hμ6 hkm hU hkL1 (by omega)
  have hT2 := pt_T2 (m := m) (k := V ^ 13) (s := V ^ 10) (A := 2 * Nat.log 2 p + 2) (L := 2 * t ^ 2)
    (β := gam0 (V ^ 2 + 50) (V ^ 10) + 1.21 * muP p σ / p) hp23 hlogp
    (by have : 0 ≤ gam0 (V ^ 2 + 50) (V ^ 10) := by unfold gam0; positivity
        positivity) hβ' hA' hkL2 hm
  calc (p : ℝ) ^ 2 * (Real.exp ((m : ℝ) / 2) * (((p : ℝ) ^ 2) ^ U.card * ((p : ℝ) * (1 + muP p σ)) ^ (m - U.card) *
        ((1 + 1 / 100) / (p : ℝ) ^ 2) ^ (m - V ^ 13) +
      3 ^ m * (((2 * Nat.log 2 p + 2 : ℕ) : ℝ) * (2 ^ m * ((p : ℝ) ^ 2) ^ (4 * V ^ 13 + V ^ 10 * (m / V ^ 13)) *
        1.23 ^ m * (gam0 (V ^ 2 + 50) (V ^ 10) + 1.21 * muP p σ / p) ^ (m / 200)))))
      = (p : ℝ) ^ 2 * (Real.exp ((m : ℝ) / 2) * (((p : ℝ) ^ 2) ^ U.card * ((p : ℝ) * (1 + muP p σ)) ^ (m - U.card) *
          ((1 + 1 / 100) / (p : ℝ) ^ 2) ^ (m - V ^ 13))) +
        (p : ℝ) ^ 2 * (Real.exp ((m : ℝ) / 2) * (3 ^ m * (((2 * Nat.log 2 p + 2 : ℕ) : ℝ) *
          (2 ^ m * ((p : ℝ) ^ 2) ^ (4 * V ^ 13 + V ^ 10 * (m / V ^ 13)) * 1.23 ^ m *
            (gam0 (V ^ 2 + 50) (V ^ 10) + 1.21 * muP p σ / p) ^ (m / 200))))) := by ring
    _ ≤ Real.exp (-(m : ℝ) / 2) / 2 + Real.exp (-(m : ℝ) / 2) / 2 := add_le_add hT1 hT2
    _ = Real.exp (-(m : ℝ) / 2) := by ring

end Psi

end DGS
