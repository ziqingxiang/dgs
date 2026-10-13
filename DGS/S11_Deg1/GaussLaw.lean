module

public import DGS.S10_Tools.Gauss
public import DGS.S10_Tools.Dilates
public import DGS.S11_Deg1.BlockProb

@[expose] public section

open Finset
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime] {σ : ℝ}

theorem summable_gaussClass_term (hσ : 0 < σ) (a : ZMod p) :
    Summable fun z : ℤ => if ((z : ZMod p) = a) then gaussW σ z else 0 :=
  summable_ite_gaussW hσ _

theorem gaussClass_nonneg (σ : ℝ) (a : ZMod p) : 0 ≤ gaussClass p σ a :=
  tsum_nonneg fun z => by split_ifs <;> simp [gaussW_nonneg]

theorem gaussW_le_gaussClass (hσ : 0 < σ) (a : ZMod p) : gaussW σ a.valMinAbs ≤ gaussClass p σ a := by
  have h := (summable_gaussClass_term hσ a).le_tsum a.valMinAbs (fun z _ => by
    split_ifs <;> simp [gaussW_nonneg])
  rw [ite_eq_left (ZMod.coe_valMinAbs a)] at h
  exact h

theorem sum_gaussClass_ne_zero (hσ : 0 < σ) :
    ∑ a ∈ univ.filter (· ≠ (0 : ZMod p)), gaussClass p σ a = gaussMu0 p σ := by
  unfold gaussClass gaussMu0
  rw [← Summable.tsum_finsetSum fun a _ => summable_gaussClass_term hσ a]
  congr 1
  funext z
  rw [sum_filter]
  have hz : ((z : ZMod p) = 0) ↔ (p : ℤ) ∣ z := ZMod.intCast_zmod_eq_zero_iff_dvd z p
  by_cases h0 : (p : ℤ) ∣ z
  · rw [ite_eq_left h0]
    refine sum_eq_zero fun a _ => ?_
    split_ifs with ha hza
    · exact absurd (hza ▸ hz.2 h0) ha
    · rfl
    · rfl
  · rw [ite_eq_right h0]
    rw [sum_eq_single (z : ZMod p)]
    · rw [ite_eq_left (fun h => h0 (hz.1 h)), ite_eq_left rfl]
    · intro b _ hb
      split_ifs with h1 h2
      · exact absurd h2.symm hb
      · rfl
      · rfl
    · intro h
      exact absurd (mem_univ _) h

theorem gaussMu0_pos (hσ : 0 < σ) : 0 < gaussMu0 p σ := by
  have hp1 : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have := Int.eq_one_of_dvd_one (by positivity) h
    have hp := (Fact.out : p.Prime).one_lt
    omega
  have h := (summable_ite_gaussW' hσ (fun z : ℤ => (p : ℤ) ∣ z)).le_tsum 1 (fun z _ => by
    split_ifs <;> simp [gaussW_nonneg])
  rw [ite_eq_right hp1] at h
  unfold gaussMu0
  exact lt_of_lt_of_le (gaussW_pos σ 1) h

noncomputable def gaussLaw (p : ℕ) [Fact p.Prime] (σ : ℝ) (a : ZMod p) : ℝ :=
  if a = 0 then 0 else gaussClass p σ a / gaussMu0 p σ

theorem gaussLaw_nonneg (hσ : 0 < σ) (a : ZMod p) : 0 ≤ gaussLaw p σ a := by
  unfold gaussLaw
  split_ifs
  · exact le_rfl
  · exact div_nonneg (gaussClass_nonneg σ a) (gaussMu0_pos hσ).le

theorem gaussLaw_zero : gaussLaw p σ 0 = 0 := by simp [gaussLaw]

theorem sum_gaussLaw (hσ : 0 < σ) : ∑ a, gaussLaw p σ a = 1 := by
  have hμ := gaussMu0_pos (p := p) hσ
  unfold gaussLaw
  rw [← sum_filter_add_sum_filter_not univ (· ≠ (0 : ZMod p))]
  have h1 : ∑ a ∈ univ.filter (· ≠ (0 : ZMod p)), (if a = 0 then 0 else gaussClass p σ a / gaussMu0 p σ) =
      ∑ a ∈ univ.filter (· ≠ (0 : ZMod p)), gaussClass p σ a / gaussMu0 p σ :=
    sum_congr rfl fun a ha => ite_eq_right (mem_filter.1 ha).2
  have h2 : ∑ a ∈ univ.filter (fun a => ¬ (a ≠ (0 : ZMod p))),
      (if a = 0 then 0 else gaussClass p σ a / gaussMu0 p σ) = 0 :=
    sum_eq_zero fun a ha => ite_eq_left (not_not.1 (mem_filter.1 ha).2)
  rw [h1, h2, add_zero, ← sum_div, sum_gaussClass_ne_zero hσ, div_self hμ.ne']

theorem gaussLaw_le (hσ : 0 < σ) {C : ℝ} (hC : ∀ a, gaussClass p σ a ≤ C) (a : ZMod p) :
    gaussLaw p σ a ≤ C / gaussMu0 p σ := by
  have hμ := gaussMu0_pos (p := p) hσ
  have hC0 : 0 ≤ C := (gaussClass_nonneg σ 0).trans (hC 0)
  unfold gaussLaw
  split_ifs
  · exact div_nonneg hC0 hμ.le
  · exact div_le_div_of_nonneg_right (hC a) hμ.le

section Support

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def lawD (p : ℕ) [Fact p.Prime] (σ : ℝ) (D : Finset ι) (j : ι) : ZMod p → ℝ :=
  if j ∈ D then gaussLaw p σ else fun a => if a = 0 then 1 else 0

omit [Fintype ι] in
theorem lawD_nonneg (hσ : 0 < σ) (D : Finset ι) (j : ι) (a : ZMod p) : 0 ≤ lawD p σ D j a := by
  by_cases hj : j ∈ D
  · simp only [lawD, ite_eq_left hj]
    exact gaussLaw_nonneg hσ a
  · simp only [lawD, ite_eq_right hj]
    split_ifs <;> norm_num

omit [Fintype ι] in
theorem sum_lawD (hσ : 0 < σ) (D : Finset ι) (j : ι) : ∑ a, lawD p σ D j a = 1 := by
  by_cases hj : j ∈ D
  · simp only [lawD, ite_eq_left hj]
    exact sum_gaussLaw hσ
  · simp [lawD, hj]

omit [Fintype ι] in
theorem lawD_of_mem {D : Finset ι} {j : ι} (hj : j ∈ D) : lawD p σ D j = gaussLaw p σ := by
  simp [lawD, hj]

theorem exp_normSqLift_le (hσ : 0 < σ) (D : Finset ι) (y : ι → ZMod p)
    (hy : ∀ j, y j ≠ 0 ↔ j ∈ D) :
    Real.exp (-σ * (normSqLift y : ℝ)) ≤ gaussMu0 p σ ^ D.card * ∏ j, lawD p σ D j (y j) := by
  have hμ := gaussMu0_pos (p := p) hσ
  have e1 : Real.exp (-σ * (normSqLift y : ℝ)) = ∏ j, gaussW σ (y j).valMinAbs := by
    rw [normSqLift]
    push_cast
    rw [mul_sum, Real.exp_sum]
    rfl
  have e2 : gaussMu0 p σ ^ D.card = ∏ j, (if j ∈ D then gaussMu0 p σ else 1) := by
    rw [prod_ite_mem, univ_inter, prod_const]
  rw [e1, e2, ← prod_mul_distrib]
  refine prod_le_prod₀ (fun j _ => (gaussW_pos σ _).le) fun j _ => ?_
  by_cases hj : j ∈ D
  · rw [ite_eq_left hj, lawD_of_mem hj, gaussLaw, ite_eq_right ((hy j).2 hj), mul_div_cancel₀ _ hμ.ne']
    exact gaussW_le_gaussClass hσ (y j)
  · have hy0 : y j = 0 := by
      by_contra h
      exact hj ((hy j).1 h)
    simp [hj, hy0, lawD, gaussW]

theorem sum_exp_normSqLift_le (hσ : 0 < σ) (D : Finset ι) (F : (ι → ZMod p) → ℝ)
    (hF : ∀ y, 0 ≤ F y) :
    ∑ y ∈ univ.filter (fun y : ι → ZMod p => ∀ j, y j ≠ 0 ↔ j ∈ D),
        Real.exp (-σ * (normSqLift y : ℝ)) * F y ≤
      gaussMu0 p σ ^ D.card * pexp (lawD p σ D) F := by
  have hμ := gaussMu0_pos (p := p) hσ
  unfold pexp
  rw [mul_sum]
  calc ∑ y ∈ univ.filter (fun y : ι → ZMod p => ∀ j, y j ≠ 0 ↔ j ∈ D),
        Real.exp (-σ * (normSqLift y : ℝ)) * F y
      ≤ ∑ y ∈ univ.filter (fun y : ι → ZMod p => ∀ j, y j ≠ 0 ↔ j ∈ D),
          gaussMu0 p σ ^ D.card * ((∏ j, lawD p σ D j (y j)) * F y) := by
        refine sum_le_sum fun y hy => ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (exp_normSqLift_le hσ D y (mem_filter.1 hy).2) (hF y)
    _ ≤ ∑ y, gaussMu0 p σ ^ D.card * ((∏ j, lawD p σ D j (y j)) * F y) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y _ _ =>
          mul_nonneg (pow_nonneg hμ.le _)
            (mul_nonneg (prod_nonneg fun j _ => lawD_nonneg hσ D j _) (hF y))

end Support

end DGS
