module

public import DGS.S13_Deg3.Simple3Sys
public import DGS.S12_Deg2.TraceRes
public import DGS.S11_Deg1.PtrueMain
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open Finset Matrix Polynomial Module Filter Topology
open scoped Real

namespace DGS

section Symm

variable {p : ℕ} [Fact p.Prime] {m n d : ℕ}

theorem polyA_transpose {A : Matrix (Fin m) (Fin m) (ZMod p)} (hA : A.IsSymm) (a : Fin d → ZMod p) :
    (polyA A a)ᵀ = polyA A a := by
  unfold polyA
  rw [transpose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [transpose_smul, transpose_pow, hA.eq]

theorem QAd_transpose {A : Matrix (Fin m) (Fin m) (ZMod p)} (hA : A.IsSymm) (b : Fin (n + 1) → ZMod p) :
    (QAd b A)ᵀ = QAd b A := by
  unfold QAd
  rw [transpose_add, transpose_sum, transpose_pow, hA.eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [transpose_smul, transpose_pow, hA.eq]

theorem commute_polyA_QAd (A : Matrix (Fin m) (Fin m) (ZMod p)) (a : Fin d → ZMod p)
    (b : Fin (n + 1) → ZMod p) : Commute (polyA A a) (QAd b A) := by
  unfold polyA QAd
  refine Commute.sum_left _ _ _ fun i _ => ?_
  refine Commute.smul_left ?_ _
  refine Commute.add_right (Commute.pow_pow_self A _ _) ?_
  exact Commute.sum_right _ _ _ fun j _ => (Commute.pow_pow_self A _ _).smul_right _

theorem inv_mul_eq_mul_inv_of_commute {X Q : Matrix (Fin m) (Fin m) (ZMod p)} (hQ : IsUnit Q.det)
    (hc : Commute X Q) : Q⁻¹ * X = X * Q⁻¹ := by
  have hc' := hc.eq
  calc Q⁻¹ * X = Q⁻¹ * X * (Q * Q⁻¹) := by rw [mul_nonsing_inv _ hQ, mul_one]
    _ = Q⁻¹ * (Q * X) * Q⁻¹ := by rw [← hc']; simp only [Matrix.mul_assoc]
    _ = X * Q⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hQ, Matrix.one_mul]

theorem isSymm_polyA_QAd_inv {A : Matrix (Fin m) (Fin m) (ZMod p)} (hA : A.IsSymm) (a : Fin d → ZMod p)
    (b : Fin (n + 1) → ZMod p) (hQ : IsUnit (QAd b A).det) : (polyA A a * (QAd b A)⁻¹).IsSymm := by
  rw [Matrix.IsSymm, transpose_mul, transpose_nonsing_inv, QAd_transpose hA, polyA_transpose hA,
    inv_mul_eq_mul_inv_of_commute hQ (commute_polyA_QAd A a b)]

end Symm

def GoodS3 {m : ℕ} (T : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p → (m : ℝ) ^ (0.4 : ℝ) ≤ p → (p : ℝ) ≤ 4 * √(m : ℝ) →
    ∀ β P : (ZMod p)[X], β.Monic → β.natDegree = 3 → IsUnit (aeval (modP p T) β).det →
      P ≠ 0 → P.natDegree ≤ 2 →
        ‖quadSum (aeval (modP p T) P * (aeval (modP p T) β)⁻¹) 1‖ ≤ Real.exp (-(cSEd * m) / 2)

section Numbers

theorem simple3_real {m N N' : ℕ} {P μ' X E : ℝ} (hNN : N + N' = m) (hN : 2 * m ≤ 5 * N)
    (hP : 0 < P) (hPe : P ≤ Real.exp (0.28 * m)) (hμ0 : 0 ≤ μ') (hy : (1 + μ') / P ≤ Real.exp (-70))
    (hX0 : 0 ≤ X) (hX : X ≤ 25) (hE : E ≤ 10.6 * m) :
    P ^ 3 * (Real.exp (m / 2) * ((P ^ 2 * (1 + μ')) ^ N * (P ^ 3) ^ N')) *
      ((P ^ (3 * m))⁻¹ * (1 + X) ^ (3 * m) * Real.exp E * P ^ 18) ≤ Real.exp (-(m : ℝ)) := by
  have e1 : P ^ 3 * (Real.exp (m / 2) * ((P ^ 2 * (1 + μ')) ^ N * (P ^ 3) ^ N')) *
      ((P ^ (3 * m))⁻¹ * (1 + X) ^ (3 * m) * Real.exp E * P ^ 18) =
      P ^ 21 * ((1 + μ') / P) ^ N * (1 + X) ^ (3 * m) * (Real.exp (m / 2) * Real.exp E) := by
    rw [mul_pow, div_pow, ← pow_mul]
    generalize (1 + μ') ^ N = a
    generalize (1 + X) ^ (3 * m) = Y
    subst hNN
    field_simp
    ring
  rw [e1]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : P ^ 21 ≤ Real.exp (5.88 * m) := by
    calc P ^ 21 ≤ Real.exp (0.28 * m) ^ 21 := pow_le_pow_left₀ hP.le hPe 21
      _ = Real.exp (5.88 * m) := by rw [← Real.exp_nat_mul]; ring_nf
  have hA0 : 0 ≤ (1 + μ') / P := div_nonneg (by linarith) hP.le
  have h2 : ((1 + μ') / P) ^ N ≤ Real.exp (-28 * m) := by
    calc ((1 + μ') / P) ^ N ≤ Real.exp (-70) ^ N := pow_le_pow_left₀ hA0 hy N
      _ = Real.exp (-70 * N) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-28 * m) := by
          apply Real.exp_le_exp.2
          have : ((2 * m : ℕ) : ℝ) ≤ ((5 * N : ℕ) : ℝ) := by exact_mod_cast hN
          push_cast at this
          linarith
  have h3 : (1 + X) ^ (3 * m) ≤ Real.exp (10 * m) := by
    rw [pow_mul]
    have h26 : (1 + X) ^ 3 ≤ Real.exp 10 := by
      have h0 : (1 + X) ^ 3 ≤ 26 ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
      have he : (2.718 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have h10 : (26 : ℝ) ^ 3 ≤ Real.exp 10 := by
        calc (26 : ℝ) ^ 3 ≤ 2.718 ^ 10 := by norm_num
          _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) he 10
          _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
      linarith
    calc ((1 + X) ^ 3) ^ m ≤ Real.exp 10 ^ m := pow_le_pow_left₀ (by positivity) h26 m
      _ = Real.exp (10 * m) := by rw [← Real.exp_nat_mul]; ring_nf
  have h4 : Real.exp (m / 2) * Real.exp E ≤ Real.exp (11.1 * m) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  have hX3 : 0 ≤ (1 + X) ^ (3 * m) := pow_nonneg (by linarith) _
  calc P ^ 21 * ((1 + μ') / P) ^ N * (1 + X) ^ (3 * m) * (Real.exp (m / 2) * Real.exp E)
      ≤ Real.exp (5.88 * m) * Real.exp (-28 * m) * Real.exp (10 * m) * Real.exp (11.1 * m) := by
        apply mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (pow_nonneg hA0 N) (Real.exp_pos _).le) h3 hX3
          (by positivity)) h4 (by positivity) (by positivity)
    _ = Real.exp (-(1.02 * m)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(m : ℝ)) := by
        apply Real.exp_le_exp.2
        linarith

variable {p : ℕ} [Fact p.Prime]

theorem simple3_Pu_le {m k N N' : ℕ} {σ R2 : ℝ} (hNN : N + N' = m) (hN : 2 * m ≤ 5 * N)
    (hσR : σ * R2 = m / 2) (hpe : (p : ℝ) ≤ Real.exp (0.28 * m)) (hμ : (1 + muP p σ) / p ≤ Real.exp (-70))
    (hX : (p : ℝ) / √(π * ((((k + (2 + 1) - 1) / (2 + 1)) / 2 : ℕ) : ℝ)) ≤ 25)
    (hE : 1.6 * ((2 + 1 : ℕ) : ℝ) ^ 2 * p * √((((k + (2 + 1) - 1) / (2 + 1) : ℕ) : ℝ)) ≤ 10.6 * m) :
    (p : ℝ) ^ (2 + 1) * (Real.exp (σ * R2) * (((p : ℝ) ^ 2 * (1 + muP p σ)) ^ N *
      ((p : ℝ) ^ (2 + 1)) ^ N')) * seqB p m 2 k ≤ Real.exp (-(m : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold seqB
  rw [hσR]
  have hμ0 := (muP_pos (p := p) σ).le
  have hX0 : 0 ≤ (p : ℝ) / √(π * ((((k + (2 + 1) - 1) / (2 + 1)) / 2 : ℕ) : ℝ)) := by positivity
  exact simple3_real hNN hN hp0 hpe hμ0 hμ hX0 hX hE

theorem simple3_t_facts {m : ℕ} (hm : 7260 ≤ m) :
    2 ≤ ((m + 19) / 20 + (2 + 1) - 1) / (2 + 1) ∧
    m ≤ 121 * ((((m + 19) / 20 + (2 + 1) - 1) / (2 + 1)) / 2) ∧
    30 * (((m + 19) / 20 + (2 + 1) - 1) / (2 + 1)) ≤ m :=
  ⟨by omega, by omega, by omega⟩

theorem simple3_X_le {m s : ℕ} {P : ℝ} (hPm : P ≤ 4 * √(m : ℝ)) (hs : m ≤ 121 * s) (hm : 1 ≤ m) :
    P / √(π * (s : ℝ)) ≤ 25 := by
  have hs1 : (1 : ℝ) ≤ s := by
    have : 1 ≤ s := by omega
    exact_mod_cast this
  have hpos : 0 < √(π * (s : ℝ)) := Real.sqrt_pos.2 (by positivity)
  rw [div_le_iff₀ hpos]
  have h2 : √(16 * (m : ℝ)) ≤ √(625 * (π * s)) := Real.sqrt_le_sqrt (by
    have : (m : ℝ) ≤ 121 * s := by exact_mod_cast hs
    have := Real.pi_gt_d2
    nlinarith)
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num)] at h2
  have e16 : √(16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e625 : √(625 : ℝ) = 25 := by
    rw [show (625 : ℝ) = 25 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e16, e625] at h2
  linarith

theorem simple3_E_le {m t : ℕ} {P : ℝ} (hP0 : 0 ≤ P) (hPm : P ≤ 4 * √(m : ℝ)) (ht : 30 * t ≤ m) :
    1.6 * ((2 + 1 : ℕ) : ℝ) ^ 2 * P * √(t : ℝ) ≤ 10.6 * m := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hP2 : P ^ 2 ≤ 16 * m := by
    have h := pow_le_pow_left₀ hP0 hPm 2
    rw [mul_pow, Real.sq_sqrt hm0] at h
    linarith
  have ht' : (t : ℝ) * 30 ≤ m := by
    have : ((30 * t : ℕ) : ℝ) ≤ m := by exact_mod_cast ht
    push_cast at this
    linarith
  have hsq : (√(t : ℝ)) ^ 2 = t := Real.sq_sqrt (Nat.cast_nonneg _)
  have hst : 0 ≤ √(t : ℝ) := Real.sqrt_nonneg _
  have e3 : ((2 + 1 : ℕ) : ℝ) = 3 := by norm_num
  rw [e3]
  have key : (1.6 * 3 ^ 2 * P * √(t : ℝ)) ^ 2 ≤ (10.6 * m) ^ 2 := by
    have e : (1.6 * 3 ^ 2 * P * √(t : ℝ)) ^ 2 = 207.36 * (P ^ 2 * (√(t : ℝ)) ^ 2) := by ring
    rw [e, hsq]
    have h1 : P ^ 2 * t ≤ 16 * m * (m / 30) :=
      mul_le_mul hP2 (by linarith) (Nat.cast_nonneg _) (by positivity)
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 key

end Numbers

section OnePair

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

def EvS3 (b : Fin 3 → ZMod p) (ω : Pairs m → Bool) (x : SignPair m) : Prop :=
  IsUnit (QAd (n := 2) b (modP p (seidelOf ω))).det ∧ ∃ a : Fin 3 → ZMod p, a ≠ 0 ∧
    (muMin (fun j : {j // uPair p x j = 0} =>
      ((polyA (modP p (seidelOf ω)) a * (QAd (n := 2) b (modP p (seidelOf ω)))⁻¹) *ᵥ uPair p x) j) : ℝ) ≤
        cSEd * m * (p : ℝ) ^ 2

theorem simple3_mu_le (hp71 : Real.exp 71 ≤ p) :
    (1 + muP p (1 / (2 * cSEd * (p : ℝ) ^ 2))) / p ≤ Real.exp (-70) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hσ : 0 < 1 / (2 * cSEd * (p : ℝ) ^ 2) := by have := cSEd_pos; positivity
  have h1 := muP_le_gaussMu0 (p := p) hσ
  have h2 := (lem_gauss (p := p) cSEd_pos cSEd_le).2.1
  have h3 := sqrt_two_pi_cSEd_le
  have h4 : muP p (1 / (2 * cSEd * (p : ℝ) ^ 2)) / p ≤ Real.exp (-149) := by
    rw [div_le_iff₀ hp0]
    calc muP p (1 / (2 * cSEd * (p : ℝ) ^ 2)) ≤ √(2 * π * cSEd) * p := h1.trans h2
      _ ≤ Real.exp (-149) * p := mul_le_mul_of_nonneg_right h3 hp0.le
  have h5 : 1 / (p : ℝ) ≤ Real.exp (-71) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos _) hp71
  have h6 : Real.exp (-149) ≤ Real.exp (-71) := Real.exp_le_exp.2 (by norm_num)
  have h7 : 2 * Real.exp (-71) ≤ Real.exp (-70) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    calc 2 * Real.exp (-71) ≤ Real.exp 1 * Real.exp (-71) :=
          mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = Real.exp (-70) := by rw [← Real.exp_add]; norm_num
  rw [add_div]
  linarith

theorem prob_EvS3_le (hm : 7260 ≤ m) (hp23 : 23 ≤ p) (hp71 : Real.exp 71 ≤ p)
    (hpm : (p : ℝ) ≤ 4 * √(m : ℝ)) (hpe : (p : ℝ) ≤ Real.exp (0.28 * m)) (b : Fin 3 → ZMod p) :
    prob (fun y : (Pairs m → Bool) × SignPair m => EvS3 b y.1 y.2) ≤
      2 * Real.exp (-(m : ℝ) / 50) + 60 * (p : ℝ) ^ 2 * (2 : ℝ) ^ (-(((m / 1000 + 1 : ℕ) : ℝ) ^ 2 / 4)) +
        (p : ℝ) ^ 3 * Real.exp (-(m : ℝ) / 30) + Real.exp (-(m : ℝ)) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hm0 : 0 < m := by omega
  set r := m / 1000 + 1 with hr
  set k := (m + 19) / 20 with hk
  set R2 : ℝ := cSEd * m * (p : ℝ) ^ 2 with hR2
  set σ : ℝ := 1 / (2 * cSEd * (p : ℝ) ^ 2) with hσ
  set A : (Pairs m → Bool) → Matrix (Fin m) (Fin m) (ZMod p) := fun ω => modP p (seidelOf ω) with hA
  set adm : SignPair m → Prop :=
    fun x => 2 * m ≤ 5 * (suppU x).card ∧ 5 * (suppU x).card ≤ 3 * m with hadm
  set Small : (Pairs m → Bool) → SignPair m → Prop := fun ω x => 2 * m ≤ 5 * (suppU x).card ∧
    ∃ a : Fin 3 → ZMod p, a ≠ 0 ∧ 20 * (univ.filter fun j =>
      ((polyA (A ω) a * (QAd (n := 2) b (A ω))⁻¹) *ᵥ uPair p x) j ≠ 0).card < m with hSmall
  set SysE : (Pairs m → Bool) → SignPair m → Prop := fun ω x => ∃ w : Fin m → Fin (2 + 1) → ZMod p,
      (∀ a : Fin (2 + 1) → ZMod p, a ≠ 0 → k ≤ (univ.filter fun j => a ⬝ᵥ w j ≠ 0).card) ∧
      krySysU ω b (uPair p x) w ∧ ∃ ℓ : Fin (2 + 1) → ZMod p, ℓ ≠ 0 ∧
        ∑ j ∈ univ.filter (fun j => uPair p x j = 0), (((ℓ ⬝ᵥ w j).valMinAbs : ℤ) : ℝ) ^ 2 ≤ R2
    with hSysE
  have hsub : ∀ y : (Pairs m → Bool) × SignPair m, EvS3 b y.1 y.2 →
      ¬ adm y.2 ∨ (¬ KerGood p 3 r (A y.1) ∨ ((KerGood p 3 r (A y.1) ∧
        IsUnit (QAd (n := 2) b (A y.1)).det ∧ Small y.1 y.2) ∨ (adm y.2 ∧ SysE y.1 y.2))) := by
    rintro ⟨ω, x⟩ ⟨hQ, a, ha, hmu⟩
    by_cases hx : adm x
    · right
      by_cases hK : KerGood p 3 r (A ω)
      · right
        by_cases hS : Small ω x
        · left
          exact ⟨hK, hQ, hS⟩
        · right
          refine ⟨hx, ?_⟩
          have hsupp : ∀ a' : Fin (2 + 1) → ZMod p, a' ≠ 0 → m ≤ 20 * (univ.filter fun j =>
              ((polyA (A ω) a' * (QAd (n := 2) b (A ω))⁻¹) *ᵥ uPair p x) j ≠ 0).card := by
            intro a' ha'
            by_contra hlt
            push Not at hlt
            exact hS ⟨hx.1, a', ha', hlt⟩
          exact sysU_of_short ω b (uPair p x) (fun j => uPair p x j = 0) hQ hsupp ha hmu
      · left
        exact hK
    · left
      exact hx
  have h1 : prob (fun y : (Pairs m → Bool) × SignPair m => ¬ adm y.2) ≤ 2 * Real.exp (-(m : ℝ) / 50) := by
    rw [prob_snd (Ω := Pairs m → Bool) (fun x => ¬ adm x)]
    exact prob_suppU_bad_le hm0
  have h2 : prob (fun y : (Pairs m → Bool) × SignPair m => ¬ KerGood p 3 r (A y.1)) ≤
      60 * (p : ℝ) ^ 2 * (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4)) := by
    rw [prob_fst (Ω' := SignPair m) (fun ω => ¬ KerGood p 3 r (A ω))]
    exact prob_not_kerGood_le hp2 3 r (by omega)
  have h3 : prob (fun y : (Pairs m → Bool) × SignPair m => KerGood p 3 r (A y.1) ∧
      IsUnit (QAd (n := 2) b (A y.1)).det ∧ Small y.1 y.2) ≤ (p : ℝ) ^ 3 * Real.exp (-(m : ℝ) / 30) := by
    refine prob_le_of_forall_fst (fun ω => ?_) (by positivity)
    by_cases hω : KerGood p 3 r (A ω) ∧ IsUnit (QAd (n := 2) b (A ω)).det
    · exact (prob_mono fun x hx => hx.2.2).trans (lem_fullsupp hp2 hω.1 (by omega) hω.2)
    · rw [prob_congr (Q := fun _ => False) fun x => ⟨fun h => hω ⟨h.1, h.2.1⟩, False.elim⟩, prob_false]
      positivity
  have h4 : prob (fun y : (Pairs m → Bool) × SignPair m => adm y.2 ∧ SysE y.1 y.2) ≤
      Real.exp (-(m : ℝ)) := by
    refine prob_le_of_forall_snd (fun x => ?_) (by positivity)
    by_cases hx : adm x
    · refine (prob_mono fun ω hω => hω.2).trans ?_
      obtain ⟨ht2, ht121, ht30⟩ := simple3_t_facts hm
      have hbound := prob_sysU_short_le (n := 2) (k := k) hp2 b (uPair p x)
        (univ.filter fun j => uPair p x j = 0) (σ := σ) (by have := cSEd_pos; positivity) R2 ht2
      refine hbound.trans ?_
      have hUc : (univ.filter fun j => uPair p x j = 0) = (suppU x)ᶜ := by
        ext j
        simp [uPair_eq_zero_iff_not_mem]
      have hcard := Finset.card_add_card_compl (univ.filter fun j => uPair p x j = 0)
      simp only [Fintype.card_fin] at hcard
      have hN : 2 * m ≤ 5 * (univ.filter fun j => uPair p x j = 0).card := by
        rw [hUc, card_compl, Fintype.card_fin]
        have := hx.2
        have : (suppU x).card ≤ m := by
          have := card_le_univ (suppU x)
          simpa using this
        omega
      have hσR : σ * R2 = m / 2 := by
        rw [hσ, hR2]
        have := cSEd_pos
        field_simp
      refine simple3_Pu_le hcard hN hσR hpe (simple3_mu_le hp71) ?_ ?_
      · exact simple3_X_le hpm ht121 (by omega)
      · exact simple3_E_le hp0.le hpm ht30
    · rw [prob_congr (Q := fun _ => False) fun ω => ⟨fun h => hx h.1, False.elim⟩, prob_false]
      positivity
  calc prob (fun y : (Pairs m → Bool) × SignPair m => EvS3 b y.1 y.2)
      ≤ prob (fun y : (Pairs m → Bool) × SignPair m => ¬ adm y.2 ∨ (¬ KerGood p 3 r (A y.1) ∨
          ((KerGood p 3 r (A y.1) ∧ IsUnit (QAd (n := 2) b (A y.1)).det ∧ Small y.1 y.2) ∨
            (adm y.2 ∧ SysE y.1 y.2)))) := prob_mono hsub
    _ ≤ _ := (prob_or_le _ _).trans (add_le_add le_rfl ((prob_or_le _ _).trans
          (add_le_add le_rfl (prob_or_le _ _))))
    _ ≤ 2 * Real.exp (-(m : ℝ) / 50) + (60 * (p : ℝ) ^ 2 * (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4)) +
          ((p : ℝ) ^ 3 * Real.exp (-(m : ℝ) / 30) + Real.exp (-(m : ℝ)))) :=
        add_le_add h1 (add_le_add h2 (add_le_add h3 h4))
    _ = _ := by ring

theorem prob_bad_p3_le (hm : 7260 ≤ m) (hp23 : 23 ≤ p) (hp71 : Real.exp 71 ≤ p)
    (hpm : (p : ℝ) ≤ 4 * √(m : ℝ)) (hpe : (p : ℝ) ≤ Real.exp (0.28 * m)) :
    prob (fun ω : Pairs m → Bool => ∃ b : Fin 3 → ZMod p,
      Real.exp (-(m : ℝ) / 100) < prob (fun x : SignPair m => EvS3 b ω x)) ≤
      (p : ℝ) ^ 3 * ((2 * Real.exp (-(m : ℝ) / 50) +
        60 * (p : ℝ) ^ 2 * (2 : ℝ) ^ (-(((m / 1000 + 1 : ℕ) : ℝ) ^ 2 / 4)) +
        (p : ℝ) ^ 3 * Real.exp (-(m : ℝ) / 30) + Real.exp (-(m : ℝ))) / Real.exp (-(m : ℝ) / 100)) := by
  classical
  set B : ℝ := (2 * Real.exp (-(m : ℝ) / 50) +
    60 * (p : ℝ) ^ 2 * (2 : ℝ) ^ (-(((m / 1000 + 1 : ℕ) : ℝ) ^ 2 / 4)) +
    (p : ℝ) ^ 3 * Real.exp (-(m : ℝ) / 30) + Real.exp (-(m : ℝ))) / Real.exp (-(m : ℝ) / 100) with hB
  have hb : ∀ b : Fin 3 → ZMod p, prob (fun ω : Pairs m → Bool =>
      Real.exp (-(m : ℝ) / 100) < prob (fun x : SignPair m => EvS3 b ω x)) ≤ B := by
    intro b
    refine (prob_mono fun ω h => le_of_lt h).trans ?_
    refine (prob_ge_le_expect_div _ (fun ω => prob_nonneg _) (Real.exp_pos _)).trans ?_
    rw [expect_prob_eq (fun y : (Pairs m → Bool) × SignPair m => EvS3 b y.1 y.2)]
    exact div_le_div_of_nonneg_right (prob_EvS3_le hm hp23 hp71 hpm hpe b) (Real.exp_pos _).le
  calc prob (fun ω : Pairs m → Bool => ∃ b : Fin 3 → ZMod p,
        Real.exp (-(m : ℝ) / 100) < prob (fun x : SignPair m => EvS3 b ω x))
      ≤ ∑ b : Fin 3 → ZMod p, prob (fun ω : Pairs m → Bool =>
          Real.exp (-(m : ℝ) / 100) < prob (fun x : SignPair m => EvS3 b ω x)) :=
        prob_exists_le_sum_fintype _
    _ ≤ ∑ _b : Fin 3 → ZMod p, B := sum_le_sum fun b _ => hb b
    _ = (p : ℝ) ^ 3 * B := by
        rw [sum_const, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end OnePair

theorem goodS3_of {m : ℕ} (hcm : 1 ≤ cSEd * m) {ω : Pairs m → Bool}
    (h : ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p → (m : ℝ) ^ (0.4 : ℝ) ≤ p → (p : ℝ) ≤ 4 * √(m : ℝ) →
      ∀ b : Fin 3 → ZMod p, prob (fun x : SignPair m => EvS3 b ω x) ≤ Real.exp (-(m : ℝ) / 100)) :
    GoodS3 (seidelOf ω) := by
  intro p _ hp23 hp4 hpm β P hβm hβd hβdet hP0 hPd
  have hp2 : p ≠ 2 := by omega
  set A := modP p (seidelOf ω) with hA
  set b : Fin 3 → ZMod p := fun i => β.coeff i with hb
  set a : Fin 3 → ZMod p := fun i => P.coeff i with ha
  have hQ' : aeval A β = QAd (n := 2) b A := aeval_eq_QAd hβm hβd
  have hP' : aeval A P = polyA A a := by
    conv_lhs => rw [eq_polyOf (d := 3) (show P.natDegree < 3 by omega)]
    rw [aeval_polyOf]
  have ha0 : a ≠ 0 := coeffs_ne_zero (by omega) hP0
  rw [hQ'] at hβdet
  rw [hP', hQ']
  set B := polyA A a * (QAd (n := 2) b A)⁻¹ with hBdef
  have hB : B.IsSymm := isSymm_polyA_QAd_inv (modP_seidel_isSymm ω) a b hβdet
  have hprob : prob (fun x : SignPair m =>
      (muMin (fun j : {j // uPair p x j = 0} => (B *ᵥ uPair p x) j) : ℝ) ≤ cSEd * m * (p : ℝ) ^ 2) ≤
      Real.exp (-(m : ℝ) / 100) :=
    (prob_mono fun x hx => ⟨hβdet, a, ha0, hx⟩).trans (h p hp23 hp4 hpm b)
  have hsq := lem_squaring_bound hp2 B hB one_ne_zero cSEd_pos (cSEd_le.trans (by norm_num)) hprob
  have e : Real.exp (-(cSEd * m) / 2) ^ 2 = Real.exp (-(cSEd * m)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have h2 : 2 * Real.exp (-2 * cSEd * m) ≤ Real.exp (-(cSEd * m)) := by
    have h3 : (2 : ℝ) ≤ Real.exp (cSEd * m) := by
      have := Real.add_one_le_exp (cSEd * m)
      linarith
    calc 2 * Real.exp (-2 * cSEd * m) ≤ Real.exp (cSEd * m) * Real.exp (-2 * cSEd * m) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = Real.exp (-(cSEd * m)) := by rw [← Real.exp_add]; ring_nf
  have h4 : ‖quadSum B 1‖ ^ 2 ≤ Real.exp (-(cSEd * m) / 2) ^ 2 := by rw [e]; exact hsq.trans h2
  have h5 := norm_nonneg (quadSum B 1)
  have h6 := Real.exp_pos (-(cSEd * m) / 2)
  nlinarith

theorem simple3_two_rpow_le {m : ℕ} (hm : 200000 ≤ m) :
    (2 : ℝ) ^ (-(((m / 1000 + 1 : ℕ) : ℝ) ^ 2 / 4)) ≤ Real.exp (-(m : ℝ) / 50) := by
  have hmR : (200000 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : (m : ℝ) / 1000 ≤ ((m / 1000 + 1 : ℕ) : ℝ) := by
    have h1 : m < 1000 * (m / 1000 + 1) := by omega
    have h2 : (m : ℝ) < 1000 * ((m / 1000 + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hl : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.2
  have h0 : (0 : ℝ) ≤ (m : ℝ) / 1000 := by positivity
  have h3 : ((m : ℝ) / 1000) ^ 2 ≤ ((m / 1000 + 1 : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ h0 hr 2
  nlinarith

theorem simple3_sqrt_le {m : ℕ} (hm : 100 ≤ m) : 4 * √(m : ℝ) ≤ m ∧ (m : ℝ) ≤ Real.exp (0.28 * m) := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  constructor
  · have hs : √(m : ℝ) ^ 2 = m := Real.sq_sqrt (by linarith)
    have hs0 : 0 ≤ √(m : ℝ) := Real.sqrt_nonneg _
    nlinarith
  · have h := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 0.28 * m)
    nlinarith

theorem prop_simple3 :
    ∀ᶠ m : ℕ in atTop, probSeidel m (fun T => ¬ GoodS3 T) ≤ Real.exp (-(m : ℝ) / 200) := by
  have hc : ∀ᶠ m : ℕ in atTop, 1 ≤ cSEd * m := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1 / cSEd)] with m hm
    have := cSEd_pos
    rw [div_le_iff₀ this] at hm
    linarith
  have h71 : ∀ᶠ m : ℕ in atTop, Real.exp 71 ≤ (m : ℝ) ^ (0.4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.4)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hpoly : ∀ᶠ m : ℕ in atTop, 2 * (m : ℝ) ≤ Real.exp (1 / 1400 * m) :=
    eventually_mul_le_exp (by norm_num) (by norm_num)
  filter_upwards [hc, h71, hpoly, eventually_ge_atTop 200000] with m hcm hm71 hmpoly hm
  classical
  have hmR : (200000 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hsq, hme⟩ := simple3_sqrt_le (m := m) (by omega)
  set X : ℝ := 4 * √(m : ℝ) with hX
  set PS := (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ 23 ≤ p ∧ (m : ℝ) ^ (0.4 : ℝ) ≤ (p : ℝ))
    with hPSdef
  let Bad : ℕ → (Pairs m → Bool) → Prop := fun p ω => ∃ hF : Fact p.Prime, ∃ b : Fin 3 → ZMod p,
    Real.exp (-(m : ℝ) / 100) < prob (fun x : SignPair m => @EvS3 p hF m b ω x)
  have hsub : ∀ ω : Pairs m → Bool, ¬ GoodS3 (seidelOf ω) → ∃ p ∈ PS, Bad p ω := by
    intro ω hω
    by_contra hno
    push Not at hno
    apply hω
    refine goodS3_of hcm fun p hF hp23 hp4 hpX b => ?_
    have hp : p ∈ PS := by
      rw [hPSdef, mem_filter, mem_range]
      refine ⟨?_, hF.out, hp23, hp4⟩
      have : p ≤ ⌊X⌋₊ := Nat.le_floor hpX
      omega
    have h1 := hno p hp
    simp only [Bad, not_exists, not_lt] at h1
    exact h1 hF b
  set e50 := Real.exp (-(m : ℝ) / 50) with he50
  set Bnd : ℝ := (m : ℝ) ^ 3 * (64 * (m : ℝ) ^ 3 * e50 / Real.exp (-(m : ℝ) / 100)) with hBnd
  have hbad : ∀ p ∈ PS, prob (Bad p) ≤ Bnd := by
    intro p hp
    rw [hPSdef, mem_filter, mem_range] at hp
    have : Fact p.Prime := ⟨hp.2.1⟩
    have hpX : (p : ℝ) ≤ X := by
      have h1 : p ≤ ⌊X⌋₊ := by omega
      exact (Nat.le_floor_iff (by positivity)).1 h1
    have hp71 : Real.exp 71 ≤ p := hm71.trans hp.2.2.2
    have hpm' : (p : ℝ) ≤ m := hpX.trans hsq
    have hpe : (p : ℝ) ≤ Real.exp (0.28 * m) := hpm'.trans hme
    have h1 : prob (Bad p) ≤ prob (fun ω : Pairs m → Bool => ∃ b : Fin 3 → ZMod p,
        Real.exp (-(m : ℝ) / 100) < prob (fun x : SignPair m => EvS3 b ω x)) :=
      prob_mono fun ω ⟨_, h⟩ => h
    refine h1.trans ((prob_bad_p3_le (by omega) hp.2.2.1 hp71 hpX hpe).trans ?_)
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    have hm1 : (1 : ℝ) ≤ m := by linarith
    have h2r := simple3_two_rpow_le hm
    have e1 : Real.exp (-(m : ℝ) / 30) ≤ e50 := Real.exp_le_exp.2 (by linarith)
    have e2 : Real.exp (-(m : ℝ)) ≤ e50 := Real.exp_le_exp.2 (by linarith)
    have he0 : 0 ≤ e50 := (Real.exp_pos _).le
    have hp2 : (p : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ hp0 hpm' 2
    have hp3 : (p : ℝ) ^ 3 ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ hp0 hpm' 3
    have hnum : 2 * e50 + 60 * (p : ℝ) ^ 2 * (2 : ℝ) ^ (-(((m / 1000 + 1 : ℕ) : ℝ) ^ 2 / 4)) +
        (p : ℝ) ^ 3 * Real.exp (-(m : ℝ) / 30) + Real.exp (-(m : ℝ)) ≤ 64 * (m : ℝ) ^ 3 * e50 := by
      have hm2 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by nlinarith
      have hm3 : (1 : ℝ) ≤ (m : ℝ) ^ 3 := one_le_pow₀ hm1
      have t1 : 60 * (p : ℝ) ^ 2 * (2 : ℝ) ^ (-(((m / 1000 + 1 : ℕ) : ℝ) ^ 2 / 4)) ≤ 60 * (m : ℝ) ^ 3 * e50 := by
        have := mul_le_mul hp2 h2r (by positivity) (by positivity)
        nlinarith
      have t2 : (p : ℝ) ^ 3 * Real.exp (-(m : ℝ) / 30) ≤ (m : ℝ) ^ 3 * e50 :=
        mul_le_mul hp3 e1 (Real.exp_pos _).le (by positivity)
      nlinarith
    rw [hBnd]
    gcongr
  have hcard : (PS.card : ℝ) ≤ 2 * m := by
    have h1 : PS.card ≤ ⌊X⌋₊ + 1 := (card_filter_le _ _).trans (card_range _).le
    have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le (by positivity)
    have h3 : (PS.card : ℝ) ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  have hBnd0 : 0 ≤ Bnd := by positivity
  have hfin : 2 * (m : ℝ) * Bnd ≤ Real.exp (-(m : ℝ) / 200) := by
    have hdiv : e50 / Real.exp (-(m : ℝ) / 100) = Real.exp (-(m : ℝ) / 100) := by
      rw [he50, ← Real.exp_sub]
      ring_nf
    have e1 : 2 * (m : ℝ) * Bnd = 128 * (m : ℝ) ^ 7 * Real.exp (-(m : ℝ) / 100) := by
      rw [hBnd, mul_div_assoc, hdiv]
      ring
    have h7 : 128 * (m : ℝ) ^ 7 ≤ Real.exp ((m : ℝ) / 200) := by
      have h2m : 0 ≤ 2 * (m : ℝ) := by positivity
      calc 128 * (m : ℝ) ^ 7 = (2 * (m : ℝ)) ^ 7 := by ring
        _ ≤ Real.exp (1 / 1400 * m) ^ 7 := pow_le_pow_left₀ h2m hmpoly 7
        _ = Real.exp ((m : ℝ) / 200) := by rw [← Real.exp_nat_mul]; ring_nf
    rw [e1]
    calc 128 * (m : ℝ) ^ 7 * Real.exp (-(m : ℝ) / 100)
        ≤ Real.exp ((m : ℝ) / 200) * Real.exp (-(m : ℝ) / 100) :=
          mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le
      _ = Real.exp (-(m : ℝ) / 200) := by rw [← Real.exp_add]; ring_nf
  calc probSeidel m (fun T => ¬ GoodS3 T)
      = prob (fun ω : Pairs m → Bool => ¬ GoodS3 (seidelOf ω)) := rfl
    _ ≤ prob (fun ω : Pairs m → Bool => ∃ p ∈ PS, Bad p ω) := prob_mono hsub
    _ ≤ ∑ p ∈ PS, prob (Bad p) := prob_exists_le_sum _ _
    _ ≤ ∑ _p ∈ PS, Bnd := sum_le_sum hbad
    _ = PS.card * Bnd := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 * (m : ℝ) * Bnd := by gcongr
    _ ≤ Real.exp (-(m : ℝ) / 200) := hfin

section Consequences

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [Algebra (ZMod p) L] {m : ℕ}

theorem natDegree_minpoly_eq_three [Finite L] (hL : finrank (ZMod p) L = 3) {μ : L}
    (hμ : μ ∉ Set.range (algebraMap (ZMod p) L)) : (minpoly (ZMod p) μ).natDegree = 3 := by
  have hint : IsIntegral (ZMod p) μ := IsIntegral.of_finite (ZMod p) μ
  have h1 := minpoly.degree_dvd hint
  rw [hL] at h1
  have h2 : (minpoly (ZMod p) μ).natDegree ≠ 1 := fun h => hμ (minpoly.natDegree_eq_one_iff.1 h)
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
  · exact absurd h h2
  · exact h

theorem isGenRoot_minpoly_three [Finite L] (hL : finrank (ZMod p) L = 3) {μ : L}
    (hμ : μ ∉ Set.range (algebraMap (ZMod p) L)) : IsGenRoot (minpoly (ZMod p) μ) μ := by
  have hint : IsIntegral (ZMod p) μ := IsIntegral.of_finite (ZMod p) μ
  exact ⟨minpoly.monic hint, minpoly.irreducible hint, minpoly.aeval _ _,
    by rw [hL, natDegree_minpoly_eq_three hL hμ]⟩

theorem quadSum_trMat_le3 [Finite L] {T : Matrix (Fin m) (Fin m) ℤ} (hT : GoodS3 T) (hp23 : 23 ≤ p)
    (hp4 : (m : ℝ) ^ (0.4 : ℝ) ≤ p) (hpm : (p : ℝ) ≤ 4 * √(m : ℝ)) {β : (ZMod p)[X]} {μ : L}
    (hgen : IsGenRoot β μ) (hβd : β.natDegree = 3)
    (hdet : IsUnit (T.map (Int.castRingHom L) - μ • 1).det) {t : L} (ht : t ≠ 0) :
    ‖quadSum (trMat (ZMod p) (t • (T.map (Int.castRingHom L) - μ • 1)⁻¹)) 1‖ ≤
      Real.exp (-(cSEd * m) / 2) := by
  have hAL : (modP p T).map (algebraMap (ZMod p) L) = T.map (Int.castRingHom L) := by
    ext i j
    simp [modP]
  rw [← hAL] at hdet ⊢
  rw [trMat_smul_resolvent hgen (modP p T) hdet t]
  refine hT p hp23 hp4 hpm β (trPoly (ZMod p) μ t) hgen.monic hβd (isUnit_aeval_of_isUnit hgen _ hdet)
    (fun h0 => ht (trPoly_eq_zero hgen h0)) ?_
  have := natDegree_trPoly_lt hgen t
  omega

theorem prob_quadL3_le [Finite L] {T : Matrix (Fin m) (Fin m) ℤ} (hT : GoodS3 T) (hp23 : 23 ≤ p)
    (hp4 : (m : ℝ) ^ (0.4 : ℝ) ≤ p) (hpm : (p : ℝ) ≤ 4 * √(m : ℝ)) {β : (ZMod p)[X]} {μ : L}
    (hgen : IsGenRoot β μ) (hβd : β.natDegree = 3)
    (hdet : IsUnit (T.map (Int.castRingHom L) - μ • 1).det) (a : L) :
    prob (fun ξ : Fin m → Bool => twoValued (1 : L) (-1) ξ ⬝ᵥ
      ((T.map (Int.castRingHom L) - μ • 1)⁻¹ *ᵥ twoValued 1 (-1) ξ) = a) ≤
      1 / (p : ℝ) ^ 3 + Real.exp (-(cSEd * m) / 2) := by
  have h := prob_quadL_eq_le_of (L := L) (p := p) (T.map (Int.castRingHom L) - μ • 1)⁻¹ a
    (Real.exp_pos _).le fun t ht => quadSum_trMat_le3 hT hp23 hp4 hpm hgen hβd hdet ht
  rwa [hgen.finrank_eq, hβd, ← one_div ((p : ℝ) ^ 3)] at h

end Consequences

end DGS
