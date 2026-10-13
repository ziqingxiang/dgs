module

public import DGS.S10_Tools.VanishingSums
public import DGS.S10_Tools.Dilates
public import DGS.S10_Tools.Gauss
public import DGS.External
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

open Finset Matrix
open scoped Pointwise Real

namespace DGS

theorem cos_le_exp_neg_sq_div_two {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ π / 2) :
    Real.cos y ≤ Real.exp (-(y ^ 2 / 2)) := by
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h, Real.cos_pi_div_two]
    exact (Real.exp_pos _).le
  set g : ℝ → ℝ := fun y => Real.exp (y ^ 2 / 2) * Real.cos y with hg
  have hd : ∀ y, HasDerivAt g (Real.exp (y ^ 2 / 2) * (y * Real.cos y - Real.sin y)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
      have := (hasDerivAt_pow 2 y).div_const 2
      convert this using 1
      push_cast
      ring
    have h2 := h1.exp.mul (Real.hasDerivAt_cos y)
    convert h2 using 1
    ring
  have hanti : AntitoneOn g (Set.Ico 0 (π / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico 0 (π / 2))
    · exact fun y _ => (hd y).continuousAt.continuousWithinAt
    · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Ico] at hz
      rw [(hd z).deriv]
      have hc : 0 < Real.cos z := Real.cos_pos_of_mem_Ioo ⟨by linarith [hz.1, Real.pi_pos], hz.2⟩
      have ht := Real.le_tan hz.1.le hz.2
      rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc] at ht
      have : z * Real.cos z - Real.sin z ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le this
  have h3 := hanti (Set.left_mem_Ico.2 (by linarith [Real.pi_pos])) ⟨h0, h⟩ h0
  simp only [hg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, Real.exp_zero,
    Real.cos_zero, mul_one] at h3
  have e : Real.cos y = Real.exp (-(y ^ 2 / 2)) * (Real.exp (y ^ 2 / 2) * Real.cos y) := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [e]
  calc _ ≤ Real.exp (-(y ^ 2 / 2)) * 1 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = _ := mul_one _

theorem abs_cos_pi_mul_le_exp {θ : ℝ} (hθ : |θ| ≤ 1 / 2) :
    |Real.cos (π * θ)| ≤ Real.exp (-(π ^ 2 / 2) * θ ^ 2) := by
  have h0 : |π * θ| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hnn : 0 ≤ Real.cos (π * θ) := Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_le.1 h0],
    by linarith [abs_le.1 h0]⟩
  rw [abs_of_nonneg hnn, ← Real.cos_abs]
  have := cos_le_exp_neg_sq_div_two (abs_nonneg (π * θ)) h0
  rw [sq_abs] at this
  convert this using 2
  ring

variable {p : ℕ} [Fact p.Prime]

theorem abs_cosP_le_exp_halasz (x : ZMod p) :
    |cosP x| ≤ Real.exp (-(π ^ 2 / 2) * ((((2 * x).valMinAbs : ℤ) : ℝ) / p) ^ 2) := by
  rw [abs_cosP_eq]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hθ : |(((2 * x).valMinAbs : ℤ) : ℝ) / p| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have := two_abs_valMinAbs_le (2 * x)
    linarith
  have := abs_cos_pi_mul_le_exp hθ
  rwa [mul_div_assoc]

theorem one_sub_le_cosP (x : ZMod p) :
    1 - 2 * π ^ 2 * (((x.valMinAbs : ℤ) : ℝ) / p) ^ 2 ≤ cosP x := by
  rw [cosP_eq_of_cast x x.valMinAbs (ZMod.coe_valMinAbs x)]
  have := Real.one_sub_sq_div_two_le_cos (x := 2 * π * ((x.valMinAbs : ℤ) : ℝ) / p)
  have e : (2 * π * ((x.valMinAbs : ℤ) : ℝ) / p) ^ 2 / 2 =
      2 * π ^ 2 * (((x.valMinAbs : ℤ) : ℝ) / p) ^ 2 := by ring
  linarith

variable {g : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def phiH (w : ι → Fin g → ZMod p) (τ : Fin g → ZMod p) (j : ι) : ℝ :=
  (((2 * (τ ⬝ᵥ w j)).valMinAbs : ℤ) : ℝ) / p

noncomputable def fH (w : ι → Fin g → ZMod p) (τ : Fin g → ZMod p) : ℝ := ∑ j, phiH w τ j ^ 2

noncomputable def levH (w : ι → Fin g → ZMod p) (x : ℝ) : Finset (Fin g → ZMod p) :=
  univ.filter fun τ => fH w τ ≤ x

omit [DecidableEq ι] in
theorem fH_nonneg (w : ι → Fin g → ZMod p) (τ : Fin g → ZMod p) : 0 ≤ fH w τ :=
  sum_nonneg fun _j _ => sq_nonneg _

omit [DecidableEq ι] in
theorem fH_zero (w : ι → Fin g → ZMod p) : fH w 0 = 0 := by
  simp [fH, phiH]

omit [DecidableEq ι] in
theorem mem_levH {w : ι → Fin g → ZMod p} {x : ℝ} {τ : Fin g → ZMod p} :
    τ ∈ levH w x ↔ fH w τ ≤ x := by
  simp [levH]

omit [DecidableEq ι] in
theorem zero_mem_levH (w : ι → Fin g → ZMod p) {x : ℝ} (hx : 0 ≤ x) : (0 : Fin g → ZMod p) ∈ levH w x :=
  mem_levH.2 (by rw [fH_zero]; exact hx)

omit [DecidableEq ι] in
theorem levH_mono (w : ι → Fin g → ZMod p) {x y : ℝ} (hxy : x ≤ y) : levH w x ⊆ levH w y :=
  fun _τ hτ => mem_levH.2 ((mem_levH.1 hτ).trans hxy)

omit [Fintype ι] [DecidableEq ι] in
theorem abs_phiH_add_le (w : ι → Fin g → ZMod p) (τ τ' : Fin g → ZMod p) (j : ι) :
    |phiH w (τ + τ') j| ≤ |phiH w τ j| + |phiH w τ' j| := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold phiH
  rw [abs_div, abs_div, abs_div, abs_of_pos hp, ← add_div]
  refine div_le_div_of_nonneg_right ?_ hp.le
  have h1 := ZMod.natAbs_valMinAbs_add_le (2 * (τ ⬝ᵥ w j)) (2 * (τ' ⬝ᵥ w j))
  rw [← mul_add, ← add_dotProduct] at h1
  have h2 : ((2 * ((τ + τ') ⬝ᵥ w j)).valMinAbs.natAbs : ℝ) ≤
      ((2 * (τ ⬝ᵥ w j)).valMinAbs + (2 * (τ' ⬝ᵥ w j)).valMinAbs).natAbs := by exact_mod_cast h1
  rw [Nat.cast_natAbs, Nat.cast_natAbs] at h2
  push_cast at h2
  exact h2.trans (abs_add_le _ _)

omit [DecidableEq ι] in
theorem fH_add_le (w : ι → Fin g → ZMod p) (τ τ' : Fin g → ZMod p) :
    fH w (τ + τ') ≤ (√(fH w τ) + √(fH w τ')) ^ 2 := by
  set a := fun j => |phiH w τ j|
  set b := fun j => |phiH w τ' j|
  have hA : fH w τ = ∑ j, a j ^ 2 := by simp [fH, a, sq_abs]
  have hB : fH w τ' = ∑ j, b j ^ 2 := by simp [fH, b, sq_abs]
  have h1 : fH w (τ + τ') ≤ ∑ j, (a j + b j) ^ 2 := by
    refine sum_le_sum fun j _ => ?_
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_phiH_add_le w τ τ' j) 2
  have hCS : ∑ j, a j * b j ≤ √(fH w τ) * √(fH w τ') := by
    rw [hA, hB]
    have := Real.sum_mul_le_sqrt_mul_sqrt univ a b
    exact this
  have h2 : ∑ j, (a j + b j) ^ 2 = fH w τ + 2 * ∑ j, a j * b j + fH w τ' := by
    rw [hA, hB, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    ring
  have h3 : (√(fH w τ) + √(fH w τ')) ^ 2 = fH w τ + 2 * (√(fH w τ) * √(fH w τ')) + fH w τ' := by
    rw [add_sq, Real.sq_sqrt (fH_nonneg w τ), Real.sq_sqrt (fH_nonneg w τ')]
    ring
  rw [h3]
  linarith

omit [DecidableEq ι] in
theorem fH_neg (w : ι → Fin g → ZMod p) (τ : Fin g → ZMod p) : fH w (-τ) = fH w τ := by
  unfold fH phiH
  refine sum_congr rfl fun j _ => ?_
  rw [neg_dotProduct, mul_neg, div_pow, div_pow]
  congr 1
  have h1 := ZMod.natAbs_valMinAbs_neg (2 * (τ ⬝ᵥ w j))
  have h2 : (((-(2 * (τ ⬝ᵥ w j))).valMinAbs.natAbs : ℕ) : ℝ) =
      (((2 * (τ ⬝ᵥ w j)).valMinAbs.natAbs : ℕ) : ℝ) := by exact_mod_cast h1
  rw [Nat.cast_natAbs, Nat.cast_natAbs] at h2
  push_cast at h2
  rw [← sq_abs, h2, sq_abs]

def iterSum {G : Type*} [AddCommGroup G] [DecidableEq G] (Λ : Finset G) : ℕ → Finset G
  | 0 => {0}
  | j + 1 => iterSum Λ j + Λ

omit [DecidableEq ι] in
theorem iterSum_subset_levH (w : ι → Fin g → ZMod p) {x : ℝ} (hx : 0 ≤ x) :
    ∀ j : ℕ, iterSum (levH w x) j ⊆ levH w ((j : ℝ) ^ 2 * x)
  | 0 => by
    intro τ hτ
    rw [iterSum, mem_singleton] at hτ
    rw [hτ]
    exact zero_mem_levH w (by positivity)
  | j + 1 => by
    intro τ hτ
    rw [iterSum, mem_add] at hτ
    obtain ⟨a, ha, b, hb, rfl⟩ := hτ
    have ha' := mem_levH.1 (iterSum_subset_levH w hx j ha)
    have hb' := mem_levH.1 hb
    refine mem_levH.2 ((fH_add_le w a b).trans ?_)
    have h1 : √(fH w a) ≤ j * √x := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg j : (0 : ℝ) ≤ j), ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt ha'
    have h2 : √(fH w b) ≤ √x := Real.sqrt_le_sqrt hb'
    have h3 : (√(fH w a) + √(fH w b)) ^ 2 ≤ (j * √x + √x) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h4 : (j * √x + √x) ^ 2 = ((j + 1 : ℕ) : ℝ) ^ 2 * x := by
      push_cast
      rw [show (j : ℝ) * √x + √x = (j + 1) * √x by ring, mul_pow, Real.sq_sqrt hx]
    linarith

noncomputable def cosSumC (c : ZMod p) (w : ι → Fin g → ZMod p) (τ : Fin g → ZMod p) : ℝ :=
  ∑ j, cosP (c * (τ ⬝ᵥ w j))

noncomputable def cosSum (w : ι → Fin g → ZMod p) (τ : Fin g → ZMod p) : ℝ := cosSumC 2 w τ

omit [DecidableEq ι] in
theorem two_mul_cosSumC (c : ZMod p) (w : ι → Fin g → ZMod p) (τ : Fin g → ZMod p) :
    ((2 * cosSumC c w τ : ℝ) : ℂ) = ∑ k : ι × Bool,
      ZMod.stdAddChar ((sgnZ k.2 : ZMod p) * (c * (τ ⬝ᵥ w k.1))) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, sgnZ_true, sgnZ_false, Int.cast_one, Int.cast_neg, one_mul,
    neg_one_mul, stdAddChar_add_neg]
  rw [cosSumC]
  push_cast
  rw [mul_sum]

omit [DecidableEq ι] in
theorem card_filter_pairs_eq_Rl [DecidableEq (Fin g → ZMod p)] (w : ι → Fin g → ZMod p) (l : ℕ) :
    (univ.filter fun x : Fin (2 * l) → ι × Bool =>
      ∑ r, sgnZ (x r).2 • w (x r).1 = 0).card = Rl l w := by
  unfold Rl vanSet
  refine card_equiv (Equiv.arrowProdEquivProdArrow (Fin (2 * l)) (fun _ => ι) (fun _ => Bool))
    fun x => ?_
  simp only [mem_filter, mem_univ, true_and]
  rfl

omit [DecidableEq ι] in
theorem sum_cosSumC_pow {c : ZMod p} (hc : c ≠ 0) (w : ι → Fin g → ZMod p) (l : ℕ) :
    ∑ τ, cosSumC c w τ ^ (2 * l) = (p : ℝ) ^ g * (Fintype.card ι : ℝ) ^ (2 * l) * rl l w := by
  classical
  set ψ := (ZMod.stdAddChar : AddChar (ZMod p) ℂ) with hψ
  let S : (Fin (2 * l) → ι × Bool) → Fin g → ZMod p := fun x => ∑ r, sgnZ (x r).2 • w (x r).1
  have hdot : ∀ (τ : Fin g → ZMod p) (x : Fin (2 * l) → ι × Bool),
      ∏ r, ψ ((sgnZ (x r).2 : ZMod p) * (c * (τ ⬝ᵥ w (x r).1))) =
        ψ (∑ i, τ i * (c • S x) i) := by
    intro τ x
    rw [← addChar_map_sum]
    congr 1
    have : ∑ i, τ i * (c • S x) i = τ ⬝ᵥ (c • S x) := rfl
    rw [this, dotProduct_smul, smul_eq_mul]
    simp only [S, dotProduct_sum, dotProduct_zsmul, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    ring
  have hsum : ∀ x : Fin (2 * l) → ι × Bool,
      ∑ τ : Fin g → ZMod p, ψ (∑ i, τ i * (c • S x) i) =
        if S x = 0 then (p : ℂ) ^ g else 0 := by
    intro x
    have h := sum_stdAddChar_dot (q := p) (c • S x)
    simp only [Fintype.card_fin] at h
    rw [h]
    have h2 : c • S x = 0 ↔ S x = 0 := by
      rw [smul_eq_zero]
      simp [hc]
    by_cases hS : S x = 0
    · rw [ite_eq_left (h2.2 hS), ite_eq_left hS]
    · rw [ite_eq_right (fun h => hS (h2.1 h)), ite_eq_right hS]
  have hC : ((∑ τ, (2 * cosSumC c w τ) ^ (2 * l) : ℝ) : ℂ) = (p : ℂ) ^ g * (Rl l w : ℂ) := by
    push_cast
    have h1 : ∀ τ : Fin g → ZMod p, ((2 * cosSumC c w τ : ℝ) : ℂ) ^ (2 * l) =
        ∑ x : Fin (2 * l) → ι × Bool, ψ (∑ i, τ i * (c • S x) i) := by
      intro τ
      rw [two_mul_cosSumC, ← Fin.prod_const, Fintype.prod_sum]
      exact sum_congr rfl fun x _ => hdot τ x
    simp_rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
    simp_rw [h1]
    rw [sum_comm]
    simp_rw [hsum]
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    rw [← card_filter_pairs_eq_Rl w l]
  have hC' : ∑ τ, (2 * cosSumC c w τ) ^ (2 * l) = (p : ℝ) ^ g * (Rl l w : ℝ) := by
    exact_mod_cast hC
  have h4 : ∑ τ, (2 * cosSumC c w τ) ^ (2 * l) = 4 ^ l * ∑ τ, cosSumC c w τ ^ (2 * l) := by
    rw [mul_sum]
    refine sum_congr rfl fun τ _ => ?_
    rw [mul_pow, pow_mul]
    norm_num
  have hR : (Rl l w : ℝ) = rl l w * (2 * (Fintype.card ι : ℝ)) ^ (2 * l) := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
    ·
      have hl0 : l = 0 ∨ 0 < l := Nat.eq_zero_or_pos l
      rcases hl0 with rfl | hl
      · simp [rl]
      · have : Rl l w = 0 := by
          unfold Rl vanSet
          rw [card_eq_zero, filter_eq_empty_iff]
          intro x _
          have : IsEmpty ι := Fintype.card_eq_zero_iff.1 h0
          exact isEmptyElim (x.1 ⟨0, by omega⟩)
        rw [this, rl, this, h0]
        simp
    · rw [rl]
      have : (2 * (Fintype.card ι : ℝ)) ^ (2 * l) ≠ 0 := by positivity
      field_simp
  have h5 : (2 * (Fintype.card ι : ℝ)) ^ (2 * l) = 4 ^ l * (Fintype.card ι : ℝ) ^ (2 * l) := by
    rw [mul_pow, pow_mul]
    norm_num
  rw [h4, hR, h5] at hC'
  have h4l : (0 : ℝ) < 4 ^ l := by positivity
  have : 4 ^ l * ∑ τ, cosSumC c w τ ^ (2 * l) =
      4 ^ l * ((p : ℝ) ^ g * (Fintype.card ι : ℝ) ^ (2 * l) * rl l w) := by
    rw [hC']
    ring
  exact mul_left_cancel₀ h4l.ne' this

omit [DecidableEq ι] in
theorem sum_cosSum_pow (hp2 : p ≠ 2) (w : ι → Fin g → ZMod p) (l : ℕ) :
    ∑ τ, cosSum w τ ^ (2 * l) = (p : ℝ) ^ g * (Fintype.card ι : ℝ) ^ (2 * l) * rl l w :=
  sum_cosSumC_pow (two_ne_zero_zmod hp2) w l

omit [DecidableEq ι] in
theorem cosSum_ge (w : ι → Fin g → ZMod p) (τ : Fin g → ZMod p) :
    (Fintype.card ι : ℝ) - 2 * π ^ 2 * fH w τ ≤ cosSum w τ := by
  unfold cosSum cosSumC fH
  have h : ∀ j, 1 - 2 * π ^ 2 * phiH w τ j ^ 2 ≤ cosP (2 * (τ ⬝ᵥ w j)) := fun j => by
    have := one_sub_le_cosP (2 * (τ ⬝ᵥ w j))
    simpa [phiH] using this
  have h2 := sum_le_sum fun j (_ : j ∈ univ) => h j
  rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, ← mul_sum] at h2
  exact h2

omit [DecidableEq ι] in
theorem card_levH_x0_le (hp2 : p ≠ 2) (w : ι → Fin g → ZMod p) {l : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ Fintype.card ι) :
    ((levH w ((Fintype.card ι : ℝ) / (8 * π ^ 2 * l))).card : ℝ) ≤ 2 * (p : ℝ) ^ g * rl l w := by
  set m : ℝ := (Fintype.card ι : ℝ) with hmdef
  set x0 := m / (8 * π ^ 2 * l) with hx0
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hmR : (1 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm
  have hπ : 0 < π ^ 2 := by positivity
  set c0 := m * (1 - 1 / (4 * l)) with hc0
  have hc0pos : 0 < c0 := by
    rw [hc0]
    have : 1 / (4 * (l : ℝ)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    nlinarith
  have hge : ∀ τ ∈ levH w x0, c0 ≤ cosSum w τ := by
    intro τ hτ
    have h1 := cosSum_ge w τ
    have h2 := mem_levH.1 hτ
    have h3 : 2 * π ^ 2 * fH w τ ≤ 2 * π ^ 2 * x0 := by gcongr
    have h4 : 2 * π ^ 2 * x0 = m / (4 * l) := by
      rw [hx0]
      field_simp
      ring
    rw [hc0]
    have : m * (1 - 1 / (4 * l)) = m - m / (4 * l) := by ring
    linarith
  have hpow : ∀ τ ∈ levH w x0, c0 ^ (2 * l) ≤ cosSum w τ ^ (2 * l) := fun τ hτ =>
    pow_le_pow_left₀ hc0pos.le (hge τ hτ) _
  have hnn : ∀ τ, 0 ≤ cosSum w τ ^ (2 * l) := fun τ => by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have h1 : ((levH w x0).card : ℝ) * c0 ^ (2 * l) ≤ (p : ℝ) ^ g * m ^ (2 * l) * rl l w := by
    rw [← sum_cosSum_pow hp2 w l]
    calc ((levH w x0).card : ℝ) * c0 ^ (2 * l) = ∑ τ ∈ levH w x0, c0 ^ (2 * l) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ τ ∈ levH w x0, cosSum w τ ^ (2 * l) := sum_le_sum hpow
      _ ≤ ∑ τ, cosSum w τ ^ (2 * l) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun τ _ _ => hnn τ
  have hbern : (1 : ℝ) / 2 ≤ (1 - 1 / (4 * l)) ^ (2 * l) := by
    have h := one_add_mul_le_pow (a := -(1 / (4 * (l : ℝ)))) (by
      have : 1 / (4 * (l : ℝ)) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith) (2 * l)
    have e : 1 + ((2 * l : ℕ) : ℝ) * -(1 / (4 * (l : ℝ))) = 1 / 2 := by
      push_cast
      field_simp
      ring
    rw [e, ← sub_eq_add_neg] at h
    exact h
  have hc0pow : c0 ^ (2 * l) = m ^ (2 * l) * (1 - 1 / (4 * l)) ^ (2 * l) := by
    rw [hc0, mul_pow]
  have hm2l : 0 < m ^ (2 * l) := by positivity
  have hr : 0 ≤ rl l w := rl_nonneg l w
  have hcard0 : (0 : ℝ) ≤ (levH w x0).card := Nat.cast_nonneg _
  rw [hc0pow] at h1
  have h2 : ((levH w x0).card : ℝ) * (m ^ (2 * l) / 2) ≤ (p : ℝ) ^ g * m ^ (2 * l) * rl l w := by
    calc ((levH w x0).card : ℝ) * (m ^ (2 * l) / 2)
        = ((levH w x0).card : ℝ) * (m ^ (2 * l) * (1 / 2)) := by ring
      _ ≤ ((levH w x0).card : ℝ) * (m ^ (2 * l) * (1 - 1 / (4 * l)) ^ (2 * l)) := by
          gcongr
      _ ≤ _ := h1
  have h3 : ((levH w x0).card : ℝ) * m ^ (2 * l) ≤ (2 * (p : ℝ) ^ g * rl l w) * m ^ (2 * l) := by
    nlinarith
  exact le_of_mul_le_mul_right h3 hm2l

def annih (H : AddSubgroup (Fin g → ZMod p)) : AddSubgroup (Fin g → ZMod p) where
  carrier := {v | ∀ τ ∈ H, τ ⬝ᵥ v = 0}
  add_mem' := fun ha hb τ hτ => by rw [dotProduct_add, ha τ hτ, hb τ hτ, add_zero]
  zero_mem' := fun τ _ => dotProduct_zero τ
  neg_mem' := fun ha τ hτ => by rw [dotProduct_neg, ha τ hτ, neg_zero]

theorem annih_ne_top {H : AddSubgroup (Fin g → ZMod p)} (hH : H ≠ ⊥) : annih H ≠ ⊤ := by
  rcases H.bot_or_exists_ne_zero with h | ⟨τ, hτ, hne⟩
  · exact absurd h hH
  obtain ⟨i, hi⟩ : ∃ i, τ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  intro htop
  have h1 : (Pi.single i 1 : Fin g → ZMod p) ∈ annih H := by
    rw [htop]
    exact AddSubgroup.mem_top _
  have h2 := h1 τ hτ
  rw [dotProduct_single, mul_one] at h2
  exact hi h2

theorem sum_subgroup_dot (H : AddSubgroup (Fin g → ZMod p)) [DecidablePred (· ∈ H)]
    (v : Fin g → ZMod p) (G : ZMod p → ℝ) {τ0 : Fin g → ZMod p} (hτ0 : τ0 ∈ H)
    (hb : τ0 ⬝ᵥ v ≠ 0) :
    (p : ℝ) * ∑ τ ∈ univ.filter (· ∈ H), G (τ ⬝ᵥ v) =
      ((univ.filter (· ∈ H)).card : ℝ) * ∑ a, G a := by
  set Hf := univ.filter (· ∈ H) with hHf
  have htrans : ∀ k : ZMod p, ∑ τ ∈ Hf, G (τ ⬝ᵥ v + k) = ∑ τ ∈ Hf, G (τ ⬝ᵥ v) := by
    intro k
    set t := (k * (τ0 ⬝ᵥ v)⁻¹).val • τ0 with ht
    have htH : t ∈ H := AddSubgroup.nsmul_mem H hτ0 _
    have htv : t ⬝ᵥ v = k := by
      rw [ht, smul_dotProduct, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hb,
        mul_one]
    refine Finset.sum_equiv (Equiv.addRight t) (fun τ => ?_) (fun τ _ => ?_)
    · simp only [hHf, mem_filter, mem_univ, true_and, Equiv.coe_addRight]
      exact (H.add_mem_cancel_right htH).symm
    · simp only [Equiv.coe_addRight, add_dotProduct, htv]
  calc (p : ℝ) * ∑ τ ∈ Hf, G (τ ⬝ᵥ v) = ∑ k : ZMod p, ∑ τ ∈ Hf, G (τ ⬝ᵥ v + k) := by
        rw [sum_congr rfl fun k _ => htrans k, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    _ = ∑ τ ∈ Hf, ∑ k : ZMod p, G (τ ⬝ᵥ v + k) := sum_comm
    _ = ∑ τ ∈ Hf, ∑ a, G a := sum_congr rfl fun τ _ =>
        Fintype.sum_equiv (Equiv.addLeft (τ ⬝ᵥ v)) _ _ (fun k => rfl)
    _ = (Hf.card : ℝ) * ∑ a, G a := by rw [sum_const, nsmul_eq_mul]

theorem sum_range_sq_mul_six (n : ℕ) :
    (∑ i ∈ range n, ((i : ℝ)) ^ 2) * 6 = ((n : ℝ) - 1) * n * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih]
    push_cast
    ring

theorem sum_valMinAbs_sq (hp2 : p ≠ 2) :
    ∑ a : ZMod p, (((a.valMinAbs : ℤ) : ℝ)) ^ 2 = ((p : ℝ) ^ 2 - 1) * p / 12 := by
  obtain ⟨h, hh⟩ : ∃ h, p = 2 * h + 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd' with h2 | ho
    · exact absurd h2 hp2
    · exact ho
  have : NeZero p := ⟨by omega⟩
  have e1 : ∑ a : ZMod p, (((a.valMinAbs : ℤ) : ℝ)) ^ 2 =
      ∑ v ∈ range p, ((((v : ZMod p).valMinAbs : ℤ) : ℝ)) ^ 2 := by
    refine Finset.sum_nbij' (fun a => a.val) (fun v => (v : ZMod p)) ?_ ?_ ?_ ?_ ?_
    · intro a _
      simp [ZMod.val_lt]
    · intro v _
      simp
    · intro a _
      simp
    · intro v hv
      have hv' : v < p := by simpa using hv
      simp [ZMod.val_natCast_of_lt hv']
    · intro a _
      simp
  have e2 : ∀ v < p, (((v : ZMod p).valMinAbs : ℤ) : ℝ) =
      if v ≤ h then (v : ℝ) else (v : ℝ) - p := by
    intro v hv
    rw [ZMod.valMinAbs_def_pos, ZMod.val_natCast_of_lt hv]
    have : p / 2 = h := by omega
    rw [this]
    split_ifs <;> push_cast <;> ring
  rw [e1, sum_congr rfl fun v hv => by rw [e2 v (mem_range.1 hv)]]
  have hp' : p = (h + 1) + h := by omega
  rw [show range p = range ((h + 1) + h) by rw [← hp'], sum_range_add]
  have s1 : ∑ v ∈ range (h + 1), (if v ≤ h then (v : ℝ) else (v : ℝ) - p) ^ 2 =
      ∑ v ∈ range (h + 1), ((v : ℝ)) ^ 2 :=
    sum_congr rfl fun v hv => by rw [ite_eq_left (by have := mem_range.1 hv; omega)]
  have s2 : ∑ u ∈ range h, (if h + 1 + u ≤ h then ((h + 1 + u : ℕ) : ℝ) else
      ((h + 1 + u : ℕ) : ℝ) - p) ^ 2 = ∑ u ∈ range h, (((h - 1 - u : ℕ) : ℝ) + 1) ^ 2 := by
    refine sum_congr rfl fun u hu => ?_
    have hu' := mem_range.1 hu
    rw [ite_eq_right (by omega)]
    have : ((h - 1 - u : ℕ) : ℝ) = (h : ℝ) - 1 - u := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [this, hh]
    push_cast
    ring
  have s3 : ∑ u ∈ range h, (((h - 1 - u : ℕ) : ℝ) + 1) ^ 2 = ∑ u ∈ range h, (((u : ℕ) : ℝ) + 1) ^ 2 :=
    sum_range_reflect (fun u => (((u : ℕ) : ℝ) + 1) ^ 2) h
  have s4 : ∑ u ∈ range h, (((u : ℕ) : ℝ) + 1) ^ 2 = ∑ v ∈ range (h + 1), ((v : ℝ)) ^ 2 := by
    rw [sum_range_succ']
    push_cast
    simp
  rw [s1, s2, s3, s4]
  have h6 := sum_range_sq_mul_six (h + 1)
  have hpR : (p : ℝ) = 2 * h + 1 := by rw [hh]; push_cast; ring
  rw [hpR]
  push_cast at h6
  nlinarith

omit [Fintype ι] [DecidableEq ι] in
theorem sum_phiH_sq_ge (hp2 : p ≠ 2) (w : ι → Fin g → ZMod p) (H : AddSubgroup (Fin g → ZMod p))
    [DecidablePred (· ∈ H)] {j : ι} (hj : w j ∉ annih H) :
    ((univ.filter (· ∈ H)).card : ℝ) * (2 / 27) ≤ ∑ τ ∈ univ.filter (· ∈ H), phiH w τ j ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp3 : (3 : ℝ) ≤ p := by
    have h1 := (Fact.out : p.Prime).two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  obtain ⟨τ0, hτ0, hb⟩ : ∃ τ0 ∈ H, τ0 ⬝ᵥ w j ≠ 0 := by
    by_contra h
    push Not at h
    exact hj h
  set G : ZMod p → ℝ := fun a => ((((2 * a).valMinAbs : ℤ) : ℝ) / p) ^ 2 with hG
  have h1 := sum_subgroup_dot H (w j) G hτ0 hb
  have h2 : ∑ a, G a = ∑ a : ZMod p, ((((a.valMinAbs : ℤ) : ℝ)) / p) ^ 2 :=
    Fintype.sum_equiv (Equiv.mulLeft₀ (2 : ZMod p) (two_ne_zero_zmod hp2)) _ _ (fun a => rfl)
  have h3 : ∑ a : ZMod p, ((((a.valMinAbs : ℤ) : ℝ)) / p) ^ 2 = ((p : ℝ) ^ 2 - 1) / (12 * p) := by
    simp_rw [div_pow]
    rw [← sum_div, sum_valMinAbs_sq hp2]
    field_simp
  have hsum : ∑ τ ∈ univ.filter (· ∈ H), phiH w τ j ^ 2 = ∑ τ ∈ univ.filter (· ∈ H), G (τ ⬝ᵥ w j) :=
    rfl
  rw [hsum]
  rw [h2, h3] at h1
  have hc : (0 : ℝ) ≤ (univ.filter (· ∈ H)).card := Nat.cast_nonneg _
  have key : (2 / 27 : ℝ) * p ≤ ((p : ℝ) ^ 2 - 1) / (12 * p) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have : ((univ.filter (· ∈ H)).card : ℝ) * (2 / 27) * p ≤
      (p : ℝ) * ∑ τ ∈ univ.filter (· ∈ H), G (τ ⬝ᵥ w j) := by
    rw [h1]
    nlinarith
  nlinarith

omit [DecidableEq ι] in
theorem exists_gt_x0_of_subgroup (hp2 : p ≠ 2) (w : ι → Fin g → ZMod p) {l : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ Fintype.card ι)
    (hsub : ∀ K : AddSubgroup (Fin g → ZMod p), K ≠ ⊤ →
      (0.18 : ℝ) * Fintype.card ι / l ≤ Nat.card {j // w j ∉ K})
    (H : AddSubgroup (Fin g → ZMod p)) (hH : H ≠ ⊥) :
    ∃ τ ∈ H, (Fintype.card ι : ℝ) / (8 * π ^ 2 * l) < fH w τ := by
  classical
  set Hf := univ.filter (· ∈ H) with hHf
  set m : ℝ := (Fintype.card ι : ℝ) with hmdef
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hmR : (1 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm
  have hHcard : (1 : ℝ) ≤ Hf.card := by
    have : 1 ≤ Hf.card := card_pos.2 ⟨0, by simp [hHf, H.zero_mem]⟩
    exact_mod_cast this
  set J := univ.filter fun j => w j ∉ annih H with hJ
  have hJcard := hsub (annih H) (annih_ne_top hH)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hJcard
  have hsum : (Hf.card : ℝ) * (2 / 27) * J.card ≤ ∑ τ ∈ Hf, fH w τ := by
    unfold fH
    rw [sum_comm]
    calc (Hf.card : ℝ) * (2 / 27) * J.card = ∑ j ∈ J, (Hf.card : ℝ) * (2 / 27) := by
          rw [sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ j ∈ J, ∑ τ ∈ Hf, phiH w τ j ^ 2 := sum_le_sum fun j hj =>
          sum_phiH_sq_ge hp2 w H (mem_filter.1 hj).2
      _ ≤ ∑ j, ∑ τ ∈ Hf, phiH w τ j ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ =>
            sum_nonneg fun τ _ => sq_nonneg _
  by_contra hcon
  push Not at hcon
  have hle : ∑ τ ∈ Hf, fH w τ ≤ Hf.card * (m / (8 * π ^ 2 * l)) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun τ hτ => hcon τ (mem_filter.1 hτ).2
  have hpi := Real.pi_gt_d2
  have hpi2 : (9.8 : ℝ) < π ^ 2 := by nlinarith
  have hkey : m / (8 * π ^ 2 * l) < (2 / 27) * (0.18 * m / l) := by
    rw [div_lt_iff₀ (by positivity)]
    have : (2 / 27 : ℝ) * (0.18 * m / l) * (8 * π ^ 2 * l) = (2 / 27) * 0.18 * 8 * π ^ 2 * m := by
      field_simp
    rw [this]
    have h3 : (1 : ℝ) < 2 / 27 * 0.18 * 8 * π ^ 2 := by linarith
    nlinarith
  have h1 : (Hf.card : ℝ) * (2 / 27) * (0.18 * m / l) ≤ (Hf.card : ℝ) * (2 / 27) * J.card := by
    have : (0 : ℝ) ≤ (Hf.card : ℝ) * (2 / 27) := by positivity
    exact mul_le_mul_of_nonneg_left hJcard this
  have h2 : (Hf.card : ℝ) * (m / (8 * π ^ 2 * l)) < (Hf.card : ℝ) * ((2 / 27) * (0.18 * m / l)) :=
    mul_lt_mul_of_pos_left hkey (by linarith)
  nlinarith

def stabSubgroup (S : Finset (Fin g → ZMod p)) : AddSubgroup (Fin g → ZMod p) where
  carrier := {t | t ∈ addStab S}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, addStab, mem_filter, mem_univ, true_and, zero_add]
    exact image_id'
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, addStab, mem_filter, mem_univ, true_and] at ha hb ⊢
    have : S.image (fun x => a + b + x) = (S.image fun x => b + x).image fun x => a + x := by
      rw [image_image]
      congr 1
      funext x
      simp [Function.comp, add_assoc]
    rw [this, hb, ha]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, addStab, mem_filter, mem_univ, true_and] at ha ⊢
    calc S.image (fun x => -a + x) = (S.image fun x => a + x).image (fun x => -a + x) := by rw [ha]
      _ = S := by
        rw [image_image]
        have : (fun x => -a + x) ∘ (fun x => a + x) = id := by
          funext x
          simp
        rw [this, image_id]

theorem mem_stabSubgroup {S : Finset (Fin g → ZMod p)} {t : Fin g → ZMod p} :
    t ∈ stabSubgroup S ↔ t ∈ addStab S := Iff.rfl

theorem addStab_subset {S : Finset (Fin g → ZMod p)} (h0 : (0 : Fin g → ZMod p) ∈ S) :
    addStab S ⊆ S := by
  intro t ht
  simp only [addStab, mem_filter, mem_univ, true_and] at ht
  rw [← ht]
  exact mem_image.2 ⟨0, h0, add_zero t⟩

theorem zero_mem_iterSum {G : Type*} [AddCommGroup G] [DecidableEq G] {Λ : Finset G}
    (h0 : (0 : G) ∈ Λ) : ∀ j, (0 : G) ∈ iterSum Λ j
  | 0 => mem_singleton_self 0
  | j + 1 => mem_add.2 ⟨0, zero_mem_iterSum h0 j, 0, h0, add_zero 0⟩

theorem iterSum_one {G : Type*} [AddCommGroup G] [DecidableEq G] (Λ : Finset G) :
    iterSum Λ 1 = Λ := by
  rw [iterSum, iterSum, singleton_zero, zero_add]

omit [DecidableEq ι] in
theorem card_levH_le (hp2 : p ≠ 2) (w : ι → Fin g → ZMod p) {l : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ Fintype.card ι)
    (hsub : ∀ K : AddSubgroup (Fin g → ZMod p), K ≠ ⊤ →
      (0.18 : ℝ) * Fintype.card ι / l ≤ Nat.card {j // w j ∉ K})
    {x : ℝ} (hx : 0 < x) (hxx0 : x ≤ (Fintype.card ι : ℝ) / (8 * π ^ 2 * l)) :
    ((levH w x).card : ℝ) ≤
      1 + 4 * (p : ℝ) ^ g * rl l w * √(x / ((Fintype.card ι : ℝ) / (8 * π ^ 2 * l))) := by
  set x0 := (Fintype.card ι : ℝ) / (8 * π ^ 2 * l) with hx0
  set Λ := levH w x with hΛ
  have hΛ0 : (0 : Fin g → ZMod p) ∈ Λ := zero_mem_levH w hx.le
  have hx0pos : 0 < x0 := hx.trans_le hxx0
  set y := √(x0 / x) with hy
  have hy1 : 1 ≤ y := by
    rw [hy, Real.one_le_sqrt, le_div_iff₀ hx, one_mul]
    exact hxx0
  set h := ⌊y⌋₊ with hh
  have hh1 : 1 ≤ h := (Nat.one_le_floor_iff y).2 hy1
  have hhy : (h : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyh : y < h + 1 := Nat.lt_floor_add_one y
  have hh2x : (h : ℝ) ^ 2 * x ≤ x0 := by
    have h1 : (h : ℝ) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hhy 2
    rw [hy, Real.sq_sqrt (by positivity)] at h1
    calc (h : ℝ) ^ 2 * x ≤ x0 / x * x := mul_le_mul_of_nonneg_right h1 hx.le
      _ = x0 := by field_simp
  have hsubx0 : ∀ j ≤ h, iterSum Λ j ⊆ levH w x0 := by
    intro j hj
    refine (iterSum_subset_levH w hx.le j).trans (levH_mono w ?_)
    have : (j : ℝ) ^ 2 ≤ (h : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hj) 2
    nlinarith
  have hstab : ∀ j, j + 1 ≤ h → addStab (iterSum Λ j + Λ) = {0} := by
    intro j hj
    set S := iterSum Λ j + Λ with hS
    have hS0 : (0 : Fin g → ZMod p) ∈ S := mem_add.2 ⟨0, zero_mem_iterSum hΛ0 j, 0, hΛ0, add_zero 0⟩
    have hSx0 : S ⊆ levH w x0 := hsubx0 (j + 1) hj
    have hbot : stabSubgroup S = ⊥ := by
      by_contra hne
      obtain ⟨τ, hτ, hfτ⟩ := exists_gt_x0_of_subgroup hp2 w hl hm hsub (stabSubgroup S) hne
      have := mem_levH.1 (hSx0 (addStab_subset hS0 (mem_stabSubgroup.1 hτ)))
      linarith
    ext t
    rw [mem_singleton, ← mem_stabSubgroup, hbot, AddSubgroup.mem_bot]
  have hgrow : ∀ j, 1 ≤ j → j ≤ h → j * Λ.card ≤ (iterSum Λ j).card + (j - 1) := by
    intro j hj1 hjh
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · rw [iterSum_one]
        omega
      have ih' := ih hjpos (by omega)
      have hk := ext_kneser (X := iterSum Λ j) (Y := Λ) ⟨0, zero_mem_iterSum hΛ0 j⟩ ⟨0, hΛ0⟩
      rw [hstab j hjh, card_singleton, singleton_zero, add_zero, add_zero] at hk
      have : iterSum Λ (j + 1) = iterSum Λ j + Λ := rfl
      rw [this]
      rw [Nat.succ_mul]
      omega
  have hgh := hgrow h hh1 le_rfl
  have hLx0 : (iterSum Λ h).card ≤ (levH w x0).card := card_le_card (hsubx0 h le_rfl)
  have hx0card := card_levH_x0_le hp2 w hl hm
  rw [← hx0] at hx0card
  have hR : (h : ℝ) * Λ.card ≤ 2 * (p : ℝ) ^ g * rl l w + (h - 1) := by
    have h1 : ((h * Λ.card : ℕ) : ℝ) ≤ (((iterSum Λ h).card + (h - 1) : ℕ) : ℝ) := by
      exact_mod_cast hgh
    push_cast [Nat.cast_sub hh1] at h1
    have h2 : ((iterSum Λ h).card : ℝ) ≤ (levH w x0).card := by exact_mod_cast hLx0
    linarith
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hh1
  have hNr : 0 ≤ 2 * (p : ℝ) ^ g * rl l w := by
    have := rl_nonneg l w
    positivity
  have hinv : 1 / (h : ℝ) ≤ 2 * √(x / x0) := by
    have hyx : √(x / x0) = 1 / y := by
      rw [hy, one_div, ← Real.sqrt_inv, inv_div]
    rw [hyx]
    have hy0 : 0 < y := by linarith
    rw [div_le_iff₀ hhpos]
    have e : 2 * (1 / y) * (h : ℝ) = 2 * h / y := by ring
    rw [e, le_div_iff₀ hy0]
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh1
    linarith
  have hΛle : (Λ.card : ℝ) ≤ 1 + 2 * (p : ℝ) ^ g * rl l w / h := by
    have : (Λ.card : ℝ) ≤ (2 * (p : ℝ) ^ g * rl l w + (h - 1)) / h := by
      rw [le_div_iff₀ hhpos]
      linarith
    calc (Λ.card : ℝ) ≤ (2 * (p : ℝ) ^ g * rl l w + (h - 1)) / h := this
      _ ≤ 1 + 2 * (p : ℝ) ^ g * rl l w / h := by
        rw [div_le_iff₀ hhpos, add_mul, div_mul_cancel₀ _ hhpos.ne']
        linarith
  calc (Λ.card : ℝ) ≤ 1 + 2 * (p : ℝ) ^ g * rl l w / h := hΛle
    _ = 1 + 2 * (p : ℝ) ^ g * rl l w * (1 / h) := by ring
    _ ≤ 1 + 2 * (p : ℝ) ^ g * rl l w * (2 * √(x / x0)) := by gcongr
    _ = 1 + 4 * (p : ℝ) ^ g * rl l w * √(x / x0) := by ring

omit [DecidableEq ι] in
theorem rhoHat_le_sum_exp (w : ι → Fin g → ZMod p) :
    (p : ℝ) ^ g * rhoHat w ≤ ∑ τ, Real.exp (-(π ^ 2 / 2) * fH w τ) := by
  have hN : (0 : ℝ) < (p : ℝ) ^ g := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  rw [rhoHat, ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
  refine sum_le_sum fun τ _ => ?_
  calc ∏ j, |cosP (τ ⬝ᵥ w j)| ≤ ∏ j, Real.exp (-(π ^ 2 / 2) * phiH w τ j ^ 2) :=
        prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => abs_cosP_le_exp_halasz _
    _ = Real.exp (-(π ^ 2 / 2) * fH w τ) := by
        rw [← Real.exp_sum, fH, mul_sum]

omit [DecidableEq ι] in
theorem eq_zero_of_fH_eq_zero (hp2 : p ≠ 2) (w : ι → Fin g → ZMod p) {l : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ Fintype.card ι)
    (hsub : ∀ K : AddSubgroup (Fin g → ZMod p), K ≠ ⊤ →
      (0.18 : ℝ) * Fintype.card ι / l ≤ Nat.card {j // w j ∉ K})
    {τ : Fin g → ZMod p} (hτ : fH w τ = 0) : τ = 0 := by
  let Z : AddSubgroup (Fin g → ZMod p) :=
    { carrier := {τ | fH w τ = 0}
      zero_mem' := fH_zero w
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        have h1 := fH_add_le w a b
        rw [ha, hb, Real.sqrt_zero, add_zero] at h1
        have h2 := fH_nonneg w (a + b)
        nlinarith
      neg_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [fH_neg, ha] }
  have hZ : Z = ⊥ := by
    by_contra hne
    obtain ⟨σ, hσ, hfσ⟩ := exists_gt_x0_of_subgroup hp2 w hl hm hsub Z hne
    have h1 : fH w σ = 0 := hσ
    have : 0 < (Fintype.card ι : ℝ) / (8 * π ^ 2 * l) := by
      have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hm
      have : (0 : ℝ) < l := by exact_mod_cast hl
      positivity
    linarith
  have : τ ∈ Z := hτ
  rw [hZ, AddSubgroup.mem_bot] at this
  exact this

theorem halasz_alg {N r m l : ℝ} (hN : 0 < N) (hr : 0 < r) (hm : 0 < m) (hl : 0 < l) :
    √(π / ((π ^ 2 / 2) / (4 * N * r / √(m / (8 * π ^ 2 * l))) ^ 2)) / 2 / N =
      8 * √(π * l / m) * r := by
  have hs : 0 < m / (8 * π ^ 2 * l) := by positivity
  have hX : π / ((π ^ 2 / 2) / (4 * N * r / √(m / (8 * π ^ 2 * l))) ^ 2) =
      (2 * N * (8 * √(π * l / m) * r)) ^ 2 := by
    have e1 : (2 * N * (8 * √(π * l / m) * r)) ^ 2 = 256 * N ^ 2 * r ^ 2 * (π * l / m) := by
      rw [show (2 * N * (8 * √(π * l / m) * r)) ^ 2 = 256 * N ^ 2 * r ^ 2 * (√(π * l / m)) ^ 2 by
        ring, Real.sq_sqrt (by positivity)]
    rw [e1, div_pow, Real.sq_sqrt hs.le]
    field_simp
    ring
  rw [hX, Real.sqrt_sq (by positivity)]
  field_simp

omit [DecidableEq ι] in
theorem prop_halasz (hp2 : p ≠ 2) (w : ι → Fin g → ZMod p) {l : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ Fintype.card ι)
    (hsub : ∀ K : AddSubgroup (Fin g → ZMod p), K ≠ ⊤ →
      (0.18 : ℝ) * Fintype.card ι / l ≤ Nat.card {j // w j ∉ K}) :
    rhoHat w ≤ 1 / (p : ℝ) ^ g + 8 * √(π * l / Fintype.card ι) * rl l w +
      Real.exp (-(Fintype.card ι : ℝ) / (16 * l)) := by
  classical
  set m : ℝ := (Fintype.card ι : ℝ) with hmdef
  set x0 := m / (8 * π ^ 2 * l) with hx0
  set N : ℝ := (p : ℝ) ^ g with hNdef
  set c : ℝ := π ^ 2 / 2 with hcdef
  set r := rl l w with hrdef
  have hmR : (1 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hN : 0 < N := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  have hc : 0 < c := by positivity
  have hx0pos : 0 < x0 := by positivity
  have hr : 0 < r := by
    have h1 := card_levH_x0_le hp2 w hl hm
    have h2 : (1 : ℝ) ≤ (levH w x0).card := by
      have : 1 ≤ (levH w x0).card := card_pos.2 ⟨0, zero_mem_levH w hx0pos.le⟩
      exact_mod_cast this
    rw [← hx0] at h1
    have : 0 < 2 * N * r := by linarith
    have h2N : 0 < 2 * N := by positivity
    exact pos_of_mul_pos_right this h2N.le
  set A := 4 * N * r / √x0 with hA
  have hApos : 0 < A := by positivity
  have hlev : ∀ x, 0 < x → x ≤ x0 → ((levH w x).card : ℝ) ≤ 1 + A * √x := by
    intro x hx hxx0
    have h := card_levH_le hp2 w hl hm hsub hx hxx0
    rw [← hx0, Real.sqrt_div' _ hx0pos.le] at h
    calc ((levH w x).card : ℝ) ≤ 1 + 4 * N * r * (√x / √x0) := h
      _ = 1 + A * √x := by rw [hA]; ring
  set M := Fintype.card (Fin g → ZMod p) with hMdef
  have hMN : (M : ℝ) = N := by
    rw [hMdef, Fintype.card_fun, ZMod.card, Fintype.card_fin, hNdef]
    push_cast
    ring
  let e0 : Fin M ≃ (Fin g → ZMod p) := (Fintype.equivFin (Fin g → ZMod p)).symm
  let F : Fin M → ℝ := fun k => fH w (e0 k)
  let σ := Tuple.sort F
  have hmono : Monotone (F ∘ σ) := Tuple.monotone_sort F
  let E : Fin M ≃ (Fin g → ZMod p) := σ.trans e0
  have hE : ∀ k, E k = e0 (σ k) := fun k => rfl
  have hEmono : ∀ i k : Fin M, i ≤ k → fH w (E i) ≤ fH w (E k) := fun i k hik => hmono hik
  have hM1 : 1 ≤ M := Fintype.card_pos
  have hterm : ∀ k : Fin M, Real.exp (-c * fH w (E k)) ≤
      (if k.val = 0 then 1 else Real.exp (-(c / A ^ 2) * ((k.val : ℝ)) ^ 2)) +
        Real.exp (-c * x0) := by
    intro k
    have hnn1 : (0 : ℝ) ≤ if k.val = 0 then 1 else Real.exp (-(c / A ^ 2) * ((k.val : ℝ)) ^ 2) := by
      split_ifs
      · norm_num
      · exact (Real.exp_pos _).le
    by_cases hbig : x0 < fH w (E k)
    · have : Real.exp (-c * fH w (E k)) ≤ Real.exp (-c * x0) := by
        apply Real.exp_le_exp.2
        nlinarith
      linarith
    push Not at hbig
    by_cases hk0 : k.val = 0
    · rw [ite_eq_left hk0]
      have : Real.exp (-c * fH w (E k)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := fH_nonneg w (E k)
        nlinarith
      have := (Real.exp_pos (-c * x0)).le
      linarith
    rw [ite_eq_right hk0]
    have hfpos : 0 < fH w (E k) := by
      rcases (fH_nonneg w (E k)).lt_or_eq with h | h
      · exact h
      · exfalso
        have h0 : (⟨0, hM1⟩ : Fin M) ≤ k := Fin.le_iff_val_le_val.2 (Nat.zero_le _)
        have h0' : fH w (E ⟨0, hM1⟩) = 0 := le_antisymm (h ▸ hEmono _ _ h0) (fH_nonneg w _)
        have e1 := eq_zero_of_fH_eq_zero hp2 w hl hm hsub h.symm
        have e2 := eq_zero_of_fH_eq_zero hp2 w hl hm hsub h0'
        have : k = ⟨0, hM1⟩ := E.injective (e1.trans e2.symm)
        exact hk0 (by rw [this])
    have hcard : ((k.val + 1 : ℕ) : ℝ) ≤ (levH w (fH w (E k))).card := by
      have hsub' : (Finset.Iic k).image E ⊆ levH w (fH w (E k)) := by
        intro τ hτ
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hτ
        exact mem_levH.2 (hEmono i k (mem_Iic.1 hi))
      have := card_le_card hsub'
      rw [card_image_of_injective _ E.injective, Fin.card_Iic] at this
      exact_mod_cast this
    have hL := hlev _ hfpos hbig
    have hk : (k.val : ℝ) ≤ A * √(fH w (E k)) := by
      push_cast at hcard
      linarith
    have hk2 : ((k.val : ℝ)) ^ 2 / A ^ 2 ≤ fH w (E k) := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : ((k.val : ℝ)) ^ 2 ≤ (A * √(fH w (E k))) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hk 2
      rw [mul_pow, Real.sq_sqrt (fH_nonneg w _)] at h1
      linarith
    have : Real.exp (-c * fH w (E k)) ≤ Real.exp (-(c / A ^ 2) * ((k.val : ℝ)) ^ 2) := by
      apply Real.exp_le_exp.2
      have : -(c / A ^ 2) * ((k.val : ℝ)) ^ 2 = -c * (((k.val : ℝ)) ^ 2 / A ^ 2) := by ring
      rw [this]
      nlinarith
    have := (Real.exp_pos (-c * x0)).le
    linarith
  have hgauss : ∑ k : Fin M, (if k.val = 0 then (1 : ℝ) else
      Real.exp (-(c / A ^ 2) * ((k.val : ℝ)) ^ 2)) ≤ 1 + √(π / (c / A ^ 2)) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun v => if v = 0 then (1 : ℝ) else
      Real.exp (-(c / A ^ 2) * ((v : ℝ)) ^ 2)) M]
    obtain ⟨M', hM'⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    rw [hM', sum_range_succ']
    simp only [Nat.succ_ne_zero, ite_false, ite_true]
    have hcA : 0 < c / A ^ 2 := by positivity
    have h1 : ∑ n ∈ range M', Real.exp (-(c / A ^ 2) * (((n + 1 : ℕ) : ℝ)) ^ 2) ≤
        ∑' n : ℕ, gaussW (c / A ^ 2) ((n + 1 : ℕ) : ℤ) := by
      have hs := summable_gauss_succ hcA
      refine le_of_eq_of_le ?_ (hs.sum_le_tsum (range M') fun n _ => gaussW_nonneg _ _)
      refine sum_congr rfl fun n _ => ?_
      simp [gaussW]
    have h2 := tsum_gauss_succ_le hcA
    push_cast at h1 h2 ⊢
    linarith
  have hsum : ∑ τ, Real.exp (-c * fH w τ) ≤ 1 + √(π / (c / A ^ 2)) / 2 + N * Real.exp (-c * x0) := by
    rw [← Equiv.sum_comp E]
    calc ∑ k : Fin M, Real.exp (-c * fH w (E k))
        ≤ ∑ k : Fin M, ((if k.val = 0 then 1 else Real.exp (-(c / A ^ 2) * ((k.val : ℝ)) ^ 2)) +
            Real.exp (-c * x0)) := sum_le_sum fun k _ => hterm k
      _ = ∑ k : Fin M, (if k.val = 0 then (1 : ℝ) else Real.exp (-(c / A ^ 2) * ((k.val : ℝ)) ^ 2)) +
            M * Real.exp (-c * x0) := by
          rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ 1 + √(π / (c / A ^ 2)) / 2 + N * Real.exp (-c * x0) := by
          rw [hMN]
          linarith
  have hmain := (rhoHat_le_sum_exp w).trans hsum
  have hexp : Real.exp (-c * x0) = Real.exp (-m / (16 * l)) := by
    congr 1
    rw [hcdef, hx0]
    field_simp
    ring
  have halg : √(π / (c / A ^ 2)) / 2 / N = 8 * √(π * l / m) * r := by
    rw [hcdef, hA, hx0]
    exact halasz_alg hN hr (by linarith) (by linarith)
  have hρ : rhoHat w ≤ (1 + √(π / (c / A ^ 2)) / 2 + N * Real.exp (-c * x0)) / N := by
    rw [le_div_iff₀ hN, mul_comm]
    exact hmain
  calc rhoHat w ≤ (1 + √(π / (c / A ^ 2)) / 2 + N * Real.exp (-c * x0)) / N := hρ
    _ = 1 / N + √(π / (c / A ^ 2)) / 2 / N + Real.exp (-c * x0) := by
        field_simp
    _ = 1 / N + 8 * √(π * l / m) * r + Real.exp (-m / (16 * l)) := by
        rw [halg, hexp]

end DGS
