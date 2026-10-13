module

public import DGS.S14_NoFactor.Cheb
public import DGS.S14_NoFactor.Valuations
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Sum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

open Finset Polynomial

namespace DGS

section ComplexRoots

variable {g : ℤ[X]}

theorem card_roots_complex (hg : g.Monic) :
    Multiset.card (g.map (Int.castRingHom ℂ)).roots = g.natDegree := by
  have hspl : (g.map (Int.castRingHom ℂ)).Splits := IsAlgClosed.splits _
  rw [← hspl.natDegree_eq_card_roots, hg.natDegree_map]

theorem abs_eval_eq_prod (hg : g.Monic) (a : ℤ) :
    |((g.eval a : ℤ) : ℝ)| = ((g.map (Int.castRingHom ℂ)).roots.map fun α => ‖(a : ℂ) - α‖).prod := by
  set G := g.map (Int.castRingHom ℂ) with hG
  have hGm : G.Monic := hg.map _
  have hspl : G.Splits := IsAlgClosed.splits G
  have h1 : G.eval (a : ℂ) = ((g.eval a : ℤ) : ℂ) := by
    rw [hG, eval_intCast_map]
    simp
  have h2 : G.eval (a : ℂ) = (G.roots.map fun α => (a : ℂ) - α).prod := by
    conv_lhs => rw [hspl.eq_prod_roots_of_monic hGm]
    rw [eval_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun α _ => ?_
    simp
  rw [← Complex.norm_intCast, ← h1, h2, Multiset.norm_prod_map]

theorem abs_eval_le (hg : g.Monic) {R : ℝ} (hR : ∀ α ∈ (g.map (Int.castRingHom ℂ)).roots, ‖α‖ ≤ R) (a : ℤ) :
    |((g.eval a : ℤ) : ℝ)| ≤ (|(a : ℝ)| + R) ^ g.natDegree := by
  rw [abs_eval_eq_prod hg, ← card_roots_complex hg]
  calc ((g.map (Int.castRingHom ℂ)).roots.map fun α => ‖(a : ℂ) - α‖).prod
      ≤ ((g.map (Int.castRingHom ℂ)).roots.map fun _ => |(a : ℝ)| + R).prod :=
        Multiset.prod_map_le_prod_map₀ _ _ (fun α _ => norm_nonneg _) fun α hα => by
          calc ‖(a : ℂ) - α‖ ≤ ‖(a : ℂ)‖ + ‖α‖ := norm_sub_le _ _
            _ ≤ |(a : ℝ)| + R := by
                rw [Complex.norm_intCast]
                linarith [hR α hα]
    _ = (|(a : ℝ)| + R) ^ Multiset.card (g.map (Int.castRingHom ℂ)).roots := by
        rw [Multiset.map_const', Multiset.prod_replicate]

theorem abs_eval_ge (hg : g.Monic) {R : ℝ} (hR : ∀ α ∈ (g.map (Int.castRingHom ℂ)).roots, ‖α‖ ≤ R)
    {a : ℤ} {b : ℝ} (hb0 : 0 ≤ b) (hab : b ≤ (a : ℝ) - R) :
    b ^ g.natDegree ≤ |((g.eval a : ℤ) : ℝ)| := by
  rw [abs_eval_eq_prod hg, ← card_roots_complex hg]
  calc b ^ Multiset.card (g.map (Int.castRingHom ℂ)).roots
      = ((g.map (Int.castRingHom ℂ)).roots.map fun _ => b).prod := by
        rw [Multiset.map_const', Multiset.prod_replicate]
    _ ≤ ((g.map (Int.castRingHom ℂ)).roots.map fun α => ‖(a : ℂ) - α‖).prod :=
        Multiset.prod_map_le_prod_map₀ _ _ (fun α _ => hb0) fun α hα => by
          have h1 : ‖(a : ℂ)‖ - ‖α‖ ≤ ‖(a : ℂ) - α‖ := norm_sub_norm_le _ _
          rw [Complex.norm_intCast] at h1
          have h2 : (a : ℝ) ≤ |(a : ℝ)| := le_abs_self _
          linarith [hR α hα]

end ComplexRoots

theorem log_le_sum_of_primeFactors {n : ℕ} (hn : n ≠ 0) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hdiv : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ P) :
    Real.log n ≤ ∑ p ∈ P, (padicValNat p n : ℝ) * Real.log p := by
  have h := Nat.prod_pow_prime_padicValNat n hn (n + 1) (Nat.lt_succ_self _)
  have hlog : Real.log n = ∑ p ∈ (range (n + 1)).filter Nat.Prime, (padicValNat p n : ℝ) * Real.log p := by
    conv_lhs => rw [← h]
    push_cast
    rw [Real.log_prod]
    · refine sum_congr rfl fun p _ => ?_
      rw [Real.log_pow]
    · intro p hp
      have : p.Prime := (mem_filter.1 hp).2
      have : (0 : ℝ) < p := by exact_mod_cast this.pos
      positivity
  rw [hlog]
  have hnn : ∀ p ∈ P, 0 ≤ (padicValNat p n : ℝ) * Real.log p := fun p hp => by
    have : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (hP p hp).one_lt.le)
    positivity
  calc ∑ p ∈ (range (n + 1)).filter Nat.Prime, (padicValNat p n : ℝ) * Real.log p
      = ∑ p ∈ ((range (n + 1)).filter Nat.Prime).filter (· ∈ P), (padicValNat p n : ℝ) * Real.log p := by
        refine (sum_filter_of_ne fun p hp hne => ?_).symm
        have hpr : p.Prime := (mem_filter.1 hp).2
        have : Fact p.Prime := ⟨hpr⟩
        have h0 : padicValNat p n ≠ 0 := by
          intro h0
          rw [h0, Nat.cast_zero, zero_mul] at hne
          exact hne rfl
        exact hdiv p hpr (dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.2 h0))
    _ ≤ ∑ p ∈ P, (padicValNat p n : ℝ) * Real.log p :=
        sum_le_sum_of_subset_of_nonneg (fun p hp => (mem_filter.1 hp).2) fun p hp _ => hnn p hp

theorem log_four_le : Real.log 4 ≤ 1.3863 := by
  have h := Real.log_two_lt_d9
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  linarith

theorem six_le_log {A : ℝ} (hA : 1000 ≤ A) : 6 ≤ Real.log A := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have he : Real.exp 1 ≤ 2.7183 := by have := Real.exp_one_lt_d9; linarith
  calc Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 2.7183 ^ 6 := pow_le_pow_left₀ (Real.exp_pos 1).le he 6
    _ ≤ 1000 := by norm_num
    _ ≤ A := hA

theorem schur_numeric {A : ℝ} (hA : 1000 ≤ A) :
    2 * (A ^ 3 + 1) * (Real.log A + Real.log 4) + 4 * A * (A + 1) * Real.log A + A * Real.log 4 <
      (A ^ 3 - A) * (Real.log (A ^ 3 - A) - 1) := by
  have hL := six_le_log hA
  have hl4 := log_four_le
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl2 : Real.log 2 ≤ 0.6932 := by have := Real.log_two_lt_d9; linarith
  set L := Real.log A with hLdef
  have hA0 : 0 < A := by linarith
  have hA3 : A ^ 3 / 2 ≤ A ^ 3 - A := by
    have h2 : 2 ≤ A ^ 2 := by nlinarith
    nlinarith [mul_nonneg hA0.le (sub_nonneg.2 h2)]
  have hpos : 0 < A ^ 3 / 2 := by positivity
  have hlog3 : 3 * L - 0.6932 ≤ Real.log (A ^ 3 - A) := by
    have h1 : Real.log (A ^ 3 / 2) ≤ Real.log (A ^ 3 - A) := Real.log_le_log hpos hA3
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h1
    push_cast at h1
    linarith
  have hAA : 0 ≤ A ^ 3 - A := by nlinarith
  have hrhs : (A ^ 3 - A) * (3 * L - 1.6932) ≤ (A ^ 3 - A) * (Real.log (A ^ 3 - A) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hAA
  have hA2 : 1000 * A ^ 2 ≤ A ^ 3 := by nlinarith
  have hkey : 2 * (A ^ 3 + 1) * (L + 1.3863) + 4 * A * (A + 1) * L + A * 1.3863 <
      (A ^ 3 - A) * (3 * L - 1.6932) := by
    have hL0 : 0 ≤ L := by linarith
    have hA1 : 1 ≤ A := by linarith
    have hA2' : 1 ≤ A ^ 2 := by nlinarith
    have h1 : A ^ 3 * (L / 4) ≤ A ^ 3 * (L - 4.4658) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 1000 * A ^ 2 * (L / 4) ≤ A ^ 3 * (L / 4) := mul_le_mul_of_nonneg_right hA2 (by positivity)
    have h3 : A * L ≤ A ^ 2 * L := mul_le_mul_of_nonneg_right (by nlinarith) hL0
    have h4 : L ≤ A ^ 2 * L := by nlinarith
    have h5 : 2.7726 ≤ A ^ 2 * L := by nlinarith
    have hAL : 0 ≤ A * L := by positivity
    have e : (A ^ 3 - A) * (3 * L - 1.6932) - (2 * (A ^ 3 + 1) * (L + 1.3863) + 4 * A * (A + 1) * L + A * 1.3863) =
        A ^ 3 * (L - 4.4658) - 4 * (A ^ 2 * L) - 7 * (A * L) - 2 * L + 0.3069 * A - 2.7726 := by ring
    nlinarith
  have hlhs : 2 * (A ^ 3 + 1) * (L + Real.log 4) + 4 * A * (A + 1) * L + A * Real.log 4 ≤
      2 * (A ^ 3 + 1) * (L + 1.3863) + 4 * A * (A + 1) * L + A * 1.3863 := by
    have : 0 ≤ A ^ 3 + 1 := by positivity
    nlinarith
  linarith

theorem exists_pow_ge {p : ℕ} (hp : p.Prime) {X : ℝ} (hX : 1 ≤ X) :
    ∃ K : ℕ, X ≤ (p : ℝ) ^ K ∧ (K : ℝ) * Real.log p ≤ Real.log X + Real.log p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hlb : 0 ≤ Real.logb p X := Real.logb_nonneg hp1 hX
  refine ⟨⌈Real.logb p X⌉₊, ?_, ?_⟩
  · calc X = (p : ℝ) ^ (Real.logb p X) := (Real.rpow_logb hp0 hp1.ne' (by linarith)).symm
      _ ≤ (p : ℝ) ^ ((⌈Real.logb p X⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1.le (Nat.le_ceil _)
      _ = (p : ℝ) ^ ⌈Real.logb p X⌉₊ := Real.rpow_natCast _ _
  · have h1 : (⌈Real.logb p X⌉₊ : ℝ) < Real.logb p X + 1 := Nat.ceil_lt_add_one hlb
    calc (⌈Real.logb p X⌉₊ : ℝ) * Real.log p ≤ (Real.logb p X + 1) * Real.log p :=
          mul_le_mul_of_nonneg_right h1.le hlp.le
      _ = Real.log X + Real.log p := by
          rw [add_mul, Real.logb, div_mul_cancel₀ _ hlp.ne', one_mul]

theorem lem_schur {g : ℤ[X]} (hg : g.Monic) (hj : 2 ≤ g.natDegree) (hroot : ∀ a : ℤ, g.eval a ≠ 0)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ α ∈ (g.map (Int.castRingHom ℂ)).roots, ‖α‖ ≤ R)
    {A : ℝ} (hA : 1000 ≤ A) (hAR : R + 1 ≤ A) (hAj : (g.natDegree : ℝ) ≤ A) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ ⌈A ^ 3⌉₊ ∧ ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ g.eval (a : ℤ) ∧ A ≤ p ∧
      (p : ℝ) ≤ A ^ (4 * g.natDegree) := by
  classical
  set j := g.natDegree with hjdef
  set N := ⌈A ^ 3⌉₊ with hN
  set X := A ^ (4 * j) with hX
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hj0 : (0 : ℝ) < j := by
    have : (2 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hNA : A ^ 3 ≤ N := Nat.le_ceil _
  have hNA' : (N : ℝ) < A ^ 3 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hX1 : 1 ≤ X := one_le_pow₀ hA1
  have hA2 : 1000 ≤ A ^ 2 := by nlinarith
  have hAA3 : 1000 * A ≤ A ^ 3 := by
    have : 1000 * A ≤ A ^ 2 * A := mul_le_mul_of_nonneg_right hA2 hA0.le
    nlinarith
  have hA4 : A ^ 3 + 1 + A ≤ A ^ 4 := by
    have h1 : 1000 * A ^ 3 ≤ A * A ^ 3 := mul_le_mul_of_nonneg_right hA (by positivity)
    have h2 : A ^ 4 = A * A ^ 3 := by ring
    nlinarith
  have hgX : ∀ a ∈ Icc 1 N, |((g.eval (a : ℤ) : ℤ) : ℝ)| ≤ X := by
    intro a ha
    have h1 := abs_eval_le hg hR (a : ℤ)
    have ha' : (a : ℝ) ≤ N := by exact_mod_cast (mem_Icc.1 ha).2
    have h2 : |((a : ℤ) : ℝ)| + R ≤ A ^ 4 := by
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg a)]
      linarith
    calc _ ≤ (|((a : ℤ) : ℝ)| + R) ^ j := h1
      _ ≤ (A ^ 4) ^ j := pow_le_pow_left₀ (by positivity) h2 j
      _ = X := by rw [hX, ← pow_mul]
  by_contra hno
  push Not at hno
  have hsmall : ∀ a ∈ Icc 1 N, ∀ p : ℕ, p.Prime → (p : ℤ) ∣ g.eval (a : ℤ) → (p : ℝ) < A := by
    intro a ha p hp hdvd
    by_contra hpA
    push Not at hpA
    have h1 := hno a (mem_Icc.1 ha).1 (mem_Icc.1 ha).2 p hp hdvd hpA
    have h2 : (p : ℤ) ≤ |g.eval (a : ℤ)| := Int.le_of_dvd (abs_pos.2 (hroot _)) ((dvd_abs _ _).2 hdvd)
    have h3 : (p : ℝ) ≤ |((g.eval (a : ℤ) : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast h2
    linarith [hgX a ha]
  set PA := (range ⌈A⌉₊).filter Nat.Prime with hPA
  have hPAprime : ∀ p ∈ PA, p.Prime := fun p hp => (mem_filter.1 hp).2
  have hmemPA : ∀ p : ℕ, p.Prime → (p : ℝ) < A → p ∈ PA := fun p hp hpA =>
    mem_filter.2 ⟨mem_range.2 (Nat.lt_ceil.2 hpA), hp⟩
  have hPAle : ∀ p ∈ PA, (p : ℝ) ≤ A := by
    intro p hp
    have h1 : p < ⌈A⌉₊ := mem_range.1 (mem_filter.1 hp).1
    exact (Nat.lt_ceil.1 h1).le
  have hlogle : ∀ a ∈ Icc 1 N, Real.log |((g.eval (a : ℤ) : ℤ) : ℝ)| ≤
      ∑ p ∈ PA, (padicValInt p (g.eval (a : ℤ)) : ℝ) * Real.log p := by
    intro a ha
    have hn : (g.eval (a : ℤ)).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (hroot _)
    have h := log_le_sum_of_primeFactors hn hPAprime (fun p hp hdvd =>
      hmemPA p hp (hsmall a ha p hp (Int.natCast_dvd.2 hdvd)))
    have e : |((g.eval (a : ℤ) : ℤ) : ℝ)| = ((g.eval (a : ℤ)).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [e]
    exact h
  choose! Kf hKf1 hKf2 using fun p (hp : p ∈ PA) => exists_pow_ge (hPAprime p hp) hX1
  have hval : ∀ p ∈ PA, ∑ a ∈ Icc 1 N, (padicValInt p (g.eval (a : ℤ)) : ℝ) ≤
      j * ((N : ℝ) / (p - 1) + Kf p) := by
    intro p hp
    have : Fact p.Prime := ⟨hPAprime p hp⟩
    refine lem_valuations hg (fun a _ => hroot _) fun a ha => ?_
    have h1 : |((g.eval (a : ℤ) : ℤ) : ℝ)| ≤ (p : ℝ) ^ Kf p := (hgX a ha).trans (hKf1 p hp)
    rw [← Int.cast_abs] at h1
    exact_mod_cast h1
  have hupper : ∑ a ∈ Icc 1 N, Real.log |((g.eval (a : ℤ) : ℤ) : ℝ)| ≤
      j * (2 * (A ^ 3 + 1) * (Real.log A + Real.log 4) + 4 * A * (A + 1) * Real.log A + A * Real.log 4) := by
    have hlogX : Real.log X ≤ 4 * A * Real.log A := by
      rw [hX, Real.log_pow]
      push_cast
      have hL : 0 ≤ Real.log A := Real.log_nonneg hA1
      nlinarith
    have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA1
    have hsub : PA ⊆ Nat.primesLE ⌊A⌋₊ := by
      intro p hp
      exact Nat.mem_primesLE.2 ⟨Nat.le_floor (hPAle p hp), hPAprime p hp⟩
    have hfl1 : 1 ≤ ⌊A⌋₊ := Nat.le_floor (by norm_num; linarith)
    have hfl : (⌊A⌋₊ : ℝ) ≤ A := Nat.floor_le hA0.le
    have hS1 : ∑ p ∈ PA, Real.log p / p ≤ Real.log A + Real.log 4 := by
      calc ∑ p ∈ PA, Real.log p / p ≤ ∑ p ∈ Nat.primesLE ⌊A⌋₊, Real.log p / p :=
            sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
        _ ≤ Real.log ⌊A⌋₊ + Real.log 4 := sum_log_div_le hfl1
        _ ≤ Real.log A + Real.log 4 := by
            have : Real.log ⌊A⌋₊ ≤ Real.log A :=
              Real.log_le_log (by exact_mod_cast hfl1) hfl
            linarith
    have hS2 : ∑ p ∈ PA, Real.log p ≤ A * Real.log 4 := by
      calc ∑ p ∈ PA, Real.log p ≤ ∑ p ∈ Nat.primesLE ⌊A⌋₊, Real.log p :=
            sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
              Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.1 hp).2.one_lt.le)
        _ ≤ Real.log 4 * ⌊A⌋₊ := chebyshev_theta_le _
        _ ≤ A * Real.log 4 := by
            have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
            nlinarith
    have hS3 : (PA.card : ℝ) ≤ A + 1 := by
      have h1 : PA.card ≤ ⌈A⌉₊ := (card_filter_le _ _).trans (card_range _).le
      have h2 : (⌈A⌉₊ : ℝ) < A + 1 := Nat.ceil_lt_add_one hA0.le
      have h3 : (PA.card : ℝ) ≤ ⌈A⌉₊ := by exact_mod_cast h1
      linarith
    have hterm : ∀ p ∈ PA, Real.log p * (j * ((N : ℝ) / (p - 1) + Kf p)) ≤
        j * (2 * N * (Real.log p / p) + Real.log X + Real.log p) := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hPAprime p hp).two_le
      have hlp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
      have h1 : (N : ℝ) / (p - 1) ≤ 2 * N / p := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        nlinarith
      have h2 := hKf2 p hp
      have h3 : Real.log p * ((N : ℝ) / (p - 1)) ≤ 2 * N * (Real.log p / p) := by
        calc Real.log p * ((N : ℝ) / (p - 1)) ≤ Real.log p * (2 * N / p) := mul_le_mul_of_nonneg_left h1 hlp
          _ = 2 * N * (Real.log p / p) := by ring
      have h4 : Real.log p * (j * ((N : ℝ) / (p - 1) + Kf p)) =
          j * (Real.log p * ((N : ℝ) / (p - 1)) + (Kf p : ℝ) * Real.log p) := by ring
      rw [h4]
      apply mul_le_mul_of_nonneg_left _ hj0.le
      linarith
    calc ∑ a ∈ Icc 1 N, Real.log |((g.eval (a : ℤ) : ℤ) : ℝ)|
        ≤ ∑ a ∈ Icc 1 N, ∑ p ∈ PA, (padicValInt p (g.eval (a : ℤ)) : ℝ) * Real.log p := sum_le_sum hlogle
      _ = ∑ p ∈ PA, Real.log p * ∑ a ∈ Icc 1 N, (padicValInt p (g.eval (a : ℤ)) : ℝ) := by
          rw [sum_comm]
          refine sum_congr rfl fun p _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun a _ => by ring
      _ ≤ ∑ p ∈ PA, Real.log p * (j * ((N : ℝ) / (p - 1) + Kf p)) := by
          refine sum_le_sum fun p hp => ?_
          have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (hPAprime p hp).one_lt.le)
          exact mul_le_mul_of_nonneg_left (hval p hp) hlp
      _ ≤ ∑ p ∈ PA, j * (2 * N * (Real.log p / p) + Real.log X + Real.log p) := sum_le_sum hterm
      _ = j * (2 * N * ∑ p ∈ PA, Real.log p / p + PA.card * Real.log X + ∑ p ∈ PA, Real.log p) := by
          rw [← mul_sum, sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ j * (2 * (A ^ 3 + 1) * (Real.log A + Real.log 4) + (A + 1) * (4 * A * Real.log A) +
            A * Real.log 4) := by
          apply mul_le_mul_of_nonneg_left _ hj0.le
          have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
          have hl4 : 0 ≤ Real.log A + Real.log 4 := by
            have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
            linarith
          have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
          have e1 : 2 * N * ∑ p ∈ PA, Real.log p / p ≤ 2 * (A ^ 3 + 1) * (Real.log A + Real.log 4) := by
            have : 2 * (N : ℝ) * ∑ p ∈ PA, Real.log p / p ≤ 2 * N * (Real.log A + Real.log 4) :=
              mul_le_mul_of_nonneg_left hS1 (by positivity)
            nlinarith
          have e2 : (PA.card : ℝ) * Real.log X ≤ (A + 1) * (4 * A * Real.log A) :=
            mul_le_mul hS3 hlogX hlX (by positivity)
          linarith
      _ = j * (2 * (A ^ 3 + 1) * (Real.log A + Real.log 4) + 4 * A * (A + 1) * Real.log A +
            A * Real.log 4) := by ring
  set R' := ⌈R⌉₊ with hR'
  have hR'A : (R' : ℝ) ≤ A := by
    have := Nat.ceil_lt_add_one hR0
    linarith
  have hR'N : R' ≤ N := by
    have h1 : (R' : ℝ) ≤ N := by linarith
    exact_mod_cast h1
  set M := N - R' with hM
  have hMR : (M : ℝ) = N - R' := by rw [hM, Nat.cast_sub hR'N]
  have hlower : (j : ℝ) * ((M : ℝ) * Real.log M - M) ≤ ∑ a ∈ Icc 1 N, Real.log |((g.eval (a : ℤ) : ℤ) : ℝ)| := by
    have hnn : ∀ a ∈ Icc 1 N, 0 ≤ Real.log |((g.eval (a : ℤ) : ℤ) : ℝ)| := by
      intro a _
      apply Real.log_nonneg
      have : 1 ≤ |g.eval (a : ℤ)| := Int.one_le_abs (hroot _)
      rw [← Int.cast_abs]
      exact_mod_cast this
    have hsub : Icc (R' + 1) N ⊆ Icc 1 N := Icc_subset_Icc (by omega) le_rfl
    have hge : ∀ a ∈ Icc (R' + 1) N, (j : ℝ) * Real.log ((a : ℝ) - R') ≤ Real.log |((g.eval (a : ℤ) : ℤ) : ℝ)| := by
      intro a ha
      have ha1 : R' + 1 ≤ a := (mem_Icc.1 ha).1
      have hb1 : (1 : ℝ) ≤ (a : ℝ) - R' := by
        have : ((R' + 1 : ℕ) : ℝ) ≤ a := by exact_mod_cast ha1
        push_cast at this
        linarith
      have hRR : R ≤ (R' : ℝ) := Nat.le_ceil R
      have h1 := abs_eval_ge hg hR (a := (a : ℤ)) (b := (a : ℝ) - R') (by linarith) (by
        rw [Int.cast_natCast]
        linarith)
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) h1
    have hreindex : ∑ a ∈ Icc (R' + 1) N, Real.log ((a : ℝ) - R') = ∑ k ∈ Ioc 0 M, Real.log k := by
      have e : Icc (R' + 1) N = (Icc 1 M).map (addRightEmbedding R') := by
        rw [map_add_right_Icc, hM, Nat.sub_add_cancel hR'N, add_comm]
      rw [e, sum_map, ← Finset.Icc_add_one_left_eq_Ioc]
      refine sum_congr rfl fun k _ => ?_
      simp
    calc (j : ℝ) * ((M : ℝ) * Real.log M - M) ≤ j * ∑ k ∈ Ioc 0 M, Real.log k :=
          mul_le_mul_of_nonneg_left (Real.le_sum_log_nat M) hj0.le
      _ = ∑ a ∈ Icc (R' + 1) N, (j : ℝ) * Real.log ((a : ℝ) - R') := by rw [← hreindex, mul_sum]
      _ ≤ ∑ a ∈ Icc (R' + 1) N, Real.log |((g.eval (a : ℤ) : ℤ) : ℝ)| := sum_le_sum hge
      _ ≤ ∑ a ∈ Icc 1 N, Real.log |((g.eval (a : ℤ) : ℤ) : ℝ)| :=
          sum_le_sum_of_subset_of_nonneg hsub fun a ha _ => hnn a ha
  have hMx : A ^ 3 - A ≤ (M : ℝ) := by rw [hMR]; linarith
  have hx1 : Real.exp 1 ≤ A ^ 3 - A := by
    have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hxpos : 0 < A ^ 3 - A := lt_of_lt_of_le (Real.exp_pos 1) hx1
  have hlogx : 1 ≤ Real.log (A ^ 3 - A) := by
    rw [Real.le_log_iff_exp_le hxpos]
    exact hx1
  have hMlog : (A ^ 3 - A) * (Real.log (A ^ 3 - A) - 1) ≤ (M : ℝ) * Real.log M - M := by
    have hM0 : 0 < (M : ℝ) := lt_of_lt_of_le hxpos hMx
    have hlogM : Real.log (A ^ 3 - A) ≤ Real.log M := Real.log_le_log hxpos hMx
    calc (A ^ 3 - A) * (Real.log (A ^ 3 - A) - 1) ≤ (A ^ 3 - A) * (Real.log M - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hxpos.le
      _ ≤ (M : ℝ) * (Real.log M - 1) := mul_le_mul_of_nonneg_right hMx (by linarith)
      _ = (M : ℝ) * Real.log M - M := by ring
  have hcomb : (M : ℝ) * Real.log M - M ≤
      2 * (A ^ 3 + 1) * (Real.log A + Real.log 4) + 4 * A * (A + 1) * Real.log A + A * Real.log 4 := by
    have := hlower.trans hupper
    exact le_of_mul_le_mul_left this hj0
  have := schur_numeric hA
  linarith

end DGS
