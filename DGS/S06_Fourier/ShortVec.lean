module

public import DGS.S06_Fourier.FourierAsymp
public import DGS.S03_Prelim.SuppD

@[expose] public section

open Matrix Polynomial Filter Topology

namespace DGS

section Card

variable {p : ℕ} [hp : Fact p.Prime]

theorem card_two_torsion_odd (hp2 : p ≠ 2) (E : ℕ) :
    Fintype.card {x : ZMod (p ^ E) // x + x = 0} = 1 := by
  have hcop : Nat.Coprime 2 (p ^ E) :=
    ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2)).pow_right E
  have hu : IsUnit (2 : ZMod (p ^ E)) := by
    have := (ZMod.isUnit_iff_coprime 2 (p ^ E)).2 hcop
    exact_mod_cast this
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, add_zero 0⟩, fun x => Subtype.ext ?_⟩
  have h := x.2
  rw [← two_mul] at h
  exact (hu.mul_right_eq_zero).1 h

theorem card_two_torsion_two {E : ℕ} (hE : 1 ≤ E) :
    Fintype.card {x : ZMod (2 ^ E) // x + x = 0} = 2 := by
  classical
  have hQ : (2 : ℕ) ^ E = 2 * 2 ^ (E - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hval : ((2 : ZMod (2 ^ E)) ^ (E - 1)).val = 2 ^ (E - 1) := by
    rw [show (2 : ZMod (2 ^ E)) ^ (E - 1) = ((2 ^ (E - 1) : ℕ) : ZMod (2 ^ E)) by push_cast; rfl,
      ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [hQ]; have := Nat.one_le_two_pow (n := E - 1); omega)]
  have hne : (2 : ZMod (2 ^ E)) ^ (E - 1) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [hval, ZMod.val_zero] at this
    exact absurd this (by positivity)
  have hset : (Finset.univ.filter fun x : ZMod (2 ^ E) => x + x = 0) =
      {0, (2 : ZMod (2 ^ E)) ^ (E - 1)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      have h1 : ((x.val + x.val : ℕ) : ZMod (2 ^ E)) = 0 := by
        push_cast; rw [ZMod.natCast_zmod_val]; exact hx
      rw [ZMod.natCast_eq_zero_iff] at h1
      have h1' : 2 * 2 ^ (E - 1) ∣ 2 * x.val := by rw [← hQ, two_mul]; exact h1
      have h2 : 2 ^ (E - 1) ∣ x.val := (Nat.mul_dvd_mul_iff_left (by norm_num)).1 h1'
      obtain ⟨j, hj⟩ := h2
      have hlt : x.val < 2 * 2 ^ (E - 1) := by rw [← hQ]; exact ZMod.val_lt x
      have hj2 : j < 2 := by
        rw [hj, mul_comm 2] at hlt
        exact Nat.lt_of_mul_lt_mul_left hlt
      interval_cases j
      · left
        rw [← ZMod.natCast_zmod_val x, hj, mul_zero, Nat.cast_zero]
      · right
        rw [← ZMod.natCast_zmod_val x, hj, mul_one]
        push_cast; rfl
    · rintro (rfl | rfl)
      · exact add_zero 0
      · rw [← two_mul, ← pow_succ', show E - 1 + 1 = E by omega]
        exact_mod_cast ZMod.natCast_self (2 ^ E)
  rw [Fintype.card_subtype, hset, Finset.card_pair (Ne.symm hne)]

theorem card_antisymm_odd (hp2 : p ≠ 2) (m E : ℕ) :
    (antisymm m (p ^ E)).card = p ^ (E * (m * (m - 1) / 2)) := by
  rw [card_antisymm, card_two_torsion_odd hp2, one_pow, mul_one, ← pow_mul]

theorem card_antisymm_two (m : ℕ) {E : ℕ} (hE : 1 ≤ E) :
    (antisymm m (2 ^ E)).card = 2 ^ (E * (m * (m - 1) / 2) + m) := by
  rw [card_antisymm, card_two_torsion_two hE, ← pow_mul, ← pow_add]

end Card

theorem eventually_sqrt_le_exp :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ((1 : ℝ) / 2) ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 8)) := by
  have h := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).bound
    (by norm_num : (0 : ℝ) < 1)).filter_mono (le_refl _)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', eventually_ge_atTop 1] with n hn hn1
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hNpos : (0 : ℝ) < n := by linarith
  rw [Real.rpow_def_of_pos hNpos]
  apply Real.exp_le_exp.2
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hN
  have hr : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 8) := by positivity
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hr, one_mul] at hn
  linarith

theorem prop_shortany {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∀ᶠ n : ℕ in atTop, prob (fun ω : Pairs n → Bool => ¬ ∀ p : ℕ, p.Prime →
      ∀ g : (ZMod p)[X], g.Monic → (p, g.natDegree) ∈ Rn δ n →
      ∀ z : Fin n → ZMod p, 0 < wt z → wt z < sDelta δ n →
        aeval (modP p (symOf 1 0 ω)) g *ᵥ z ≠ 0) ≤ Real.exp (-(n : ℝ) / 8) := by
  have hLev : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  filter_upwards [lem_suppd 1 0, hLev, eventually_sqrt_le_exp, eventually_ge_atTop 1]
    with n hsupp hLn hexpn hn1
  refine le_trans (prob_mono ?_) hsupp
  intro ω hω hgood
  apply hω
  intro p hp g hg hR z hz0 hzs hgz
  obtain ⟨-, hd1, hdR, hpdR⟩ := hR
  set d := g.natDegree with hd
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hNpos : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log n := by linarith
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hpB : (p : ℝ) ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 8)) := by
    have h1 : (p : ℝ) ≤ ((p * d : ℕ) : ℝ) := by
      push_cast; exact le_mul_of_one_le_right (Nat.cast_nonneg p) hd1'
    calc (p : ℝ) ≤ ((p * d : ℕ) : ℝ) := h1
      _ ≤ (n : ℝ) ^ (1 / 2 - δ) / Real.log n := hpdR
      _ ≤ (n : ℝ) ^ (1 / 2 - δ) := div_le_self (by positivity) hL1
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ ≤ _ := hexpn
  have hpab : ¬ (p : ℤ) ∣ 1 - 0 := by
    rw [sub_zero]
    intro h
    have : p ∣ 1 := by exact_mod_cast h
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hdm : (d : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
    calc (d : ℝ) ≤ (n : ℝ) ^ δ / Real.log n ^ 2 := hdR
      _ ≤ (n : ℝ) ^ δ := div_le_self (by positivity) (by nlinarith)
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hN1 hδ1
  have hz : z ≠ 0 := by
    rintro rfl
    simp [wt] at hz0
  have hsupp' := hgood p hp hpB hpab d hd1 hdm g hg rfl z hz hgz
  have h1 : 4 * ((d : ℝ) + 1) ≤ (n : ℝ) ^ δ / 2 := by
    have h1a : (d : ℝ) * Real.log n ^ 2 ≤ (n : ℝ) ^ δ := by
      rwa [le_div_iff₀ (by positivity)] at hdR
    have h1b := mul_nonneg (show (0 : ℝ) ≤ Real.log n ^ 2 - 16 by nlinarith)
      (show (0 : ℝ) ≤ d by linarith)
    nlinarith
  have h2 : 2 * (n : ℝ) ^ (1 - δ) ≤ (n : ℝ) / (4 * (d + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    calc 2 * (n : ℝ) ^ (1 - δ) * (4 * (d + 1)) ≤ 2 * (n : ℝ) ^ (1 - δ) * ((n : ℝ) ^ δ / 2) := by
          gcongr
      _ = (n : ℝ) ^ (1 - δ) * (n : ℝ) ^ δ := by ring
      _ = n := by rw [← Real.rpow_add hNpos]; simp
  have h3 : (wt z : ℝ) < (n : ℝ) ^ (1 - δ) + 1 := by
    have : (wt z : ℝ) < sDelta δ n := by exact_mod_cast hzs
    exact this.trans_le (Nat.ceil_lt_add_one (by positivity)).le
  have h4 : (1 : ℝ) ≤ (n : ℝ) ^ (1 - δ) := Real.one_le_rpow hN1 (by linarith)
  have h5 : (n : ℝ) / (4 * (d + 1)) < wt z := hsupp'
  linarith

end DGS
