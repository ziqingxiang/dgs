module

public import DGS.S11_Deg1.GaussLaw
public import DGS.S11_Deg1.BlockProb
public import DGS.S10_Tools.BlockD

@[expose] public section

open Finset Matrix Module
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime]

theorem dot_two (ℓ g : Fin 2 → ZMod p) : ℓ ⬝ᵥ g = ℓ 0 * g 0 + ℓ 1 * g 1 := by
  simp [dotProduct, Fin.sum_univ_two]

theorem sum_dot_eq (ℓ : Fin 2 → ZMod p) (hℓ : ℓ ≠ 0) (F : ZMod p → ℝ) :
    ∑ g : Fin 2 → ZMod p, F (ℓ ⬝ᵥ g) = p * ∑ a, F a := by
  rw [← (finTwoArrowEquiv (ZMod p)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [finTwoArrowEquiv_symm_apply, dot_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases h1 : ℓ 1 = 0
  · have h0 : ℓ 0 ≠ 0 := by
      intro h0
      apply hℓ
      funext i
      fin_cases i
      · exact h0
      · exact h1
    rw [Finset.sum_comm]
    have : ∀ y : ZMod p, ∑ x : ZMod p, F (ℓ 0 * x + ℓ 1 * y) = ∑ a, F a := fun y =>
      Fintype.sum_equiv ((Equiv.mulLeft₀ (ℓ 0) h0).trans (Equiv.addRight (ℓ 1 * y))) _ _ fun x => rfl
    rw [Finset.sum_congr rfl fun y _ => this y, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  · have : ∀ x : ZMod p, ∑ y : ZMod p, F (ℓ 0 * x + ℓ 1 * y) = ∑ a, F a := fun x =>
      Fintype.sum_equiv ((Equiv.mulLeft₀ (ℓ 1) h1).trans (Equiv.addLeft (ℓ 0 * x))) _ _ fun y => rfl
    rw [Finset.sum_congr rfl fun x _ => this x, sum_const, card_univ, ZMod.card, nsmul_eq_mul]

theorem sum_dot_ne_zero (ℓ : Fin 2 → ZMod p) (hℓ : ℓ ≠ 0) :
    ∑ g : Fin 2 → ZMod p, (if ℓ ⬝ᵥ g ≠ 0 then (1 : ℝ) else 0) = p * (p - 1) := by
  rw [sum_dot_eq ℓ hℓ (fun a => if a ≠ 0 then (1 : ℝ) else 0)]
  congr 1
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_ne' univ (0 : ZMod p),
    card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  push_cast [hp]
  ring

theorem sum_dot_eq_zero_ne (ℓ : Fin 2 → ZMod p) (hℓ : ℓ ≠ 0) :
    ∑ g : Fin 2 → ZMod p, (if ℓ ⬝ᵥ g = 0 ∧ g ≠ 0 then (1 : ℝ) else 0) = p - 1 := by
  have e : ∀ g : Fin 2 → ZMod p, (if ℓ ⬝ᵥ g = 0 ∧ g ≠ 0 then (1 : ℝ) else 0) =
      (if ℓ ⬝ᵥ g = 0 then (1 : ℝ) else 0) - (if g = 0 then 1 else 0) := by
    intro g
    by_cases hg : g = 0
    · simp [hg]
    · simp [hg]
  simp_rw [e]
  rw [sum_sub_distrib, sum_dot_eq ℓ hℓ (fun a => if a = 0 then (1 : ℝ) else 0)]
  simp

variable (p) in
noncomputable def muP (σ : ℝ) : ℝ := ∑ a : ZMod p, if a ≠ 0 then gaussW σ a.valMinAbs else 0

theorem muP_pos (σ : ℝ) : 0 < muP p σ := by
  unfold muP
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  calc (0 : ℝ) < gaussW σ (1 : ZMod p).valMinAbs := gaussW_pos _ _
    _ = if (1 : ZMod p) ≠ 0 then gaussW σ (1 : ZMod p).valMinAbs else 0 := by rw [ite_eq_left h1]
    _ ≤ ∑ a : ZMod p, if a ≠ 0 then gaussW σ a.valMinAbs else 0 :=
        single_le_sum (f := fun a : ZMod p => if a ≠ 0 then gaussW σ a.valMinAbs else 0)
          (fun a _ => by split_ifs <;> simp [gaussW_nonneg]) (mem_univ _)

theorem muP_le_gaussMu0 {σ : ℝ} (hσ : 0 < σ) : muP p σ ≤ gaussMu0 p σ := by
  rw [← sum_gaussClass_ne_zero hσ, muP, ← sum_filter]
  exact sum_le_sum fun a _ => gaussW_le_gaussClass hσ a

def clsG (ℓ g : Fin 2 → ZMod p) : Fin 3 := if ℓ ⬝ᵥ g ≠ 0 then 1 else if g = 0 then 0 else 2

noncomputable def wtB (σ : ℝ) (inU : Bool) (ℓ g : Fin 2 → ZMod p) : ℝ :=
  if inU then 1 else gaussW σ (ℓ ⬝ᵥ g).valMinAbs

variable (p) in
noncomputable def massOf (σ : ℝ) (c : Fin 3) (inU : Bool) : ℝ :=
  if c = 1 then (if inU then (p : ℝ) * (p - 1) else p * muP p σ) else if c = 2 then (p : ℝ) - 1 else 1

noncomputable def lawOf (σ : ℝ) (ℓ : Fin 2 → ZMod p) (c : Fin 3) (inU : Bool) (g : Fin 2 → ZMod p) : ℝ :=
  if c = 1 then
    (if ℓ ⬝ᵥ g ≠ 0 then (if inU then 1 else gaussW σ (ℓ ⬝ᵥ g).valMinAbs) / massOf p σ 1 inU else 0)
  else if c = 2 then (if ℓ ⬝ᵥ g = 0 ∧ g ≠ 0 then 1 / ((p : ℝ) - 1) else 0)
  else (if g = 0 then 1 else 0)

theorem p_sub_one_pos : (0 : ℝ) < (p : ℝ) - 1 := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  linarith

theorem massOf_pos (σ : ℝ) (c : Fin 3) (inU : Bool) : 0 < massOf p σ c inU := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 := p_sub_one_pos (p := p)
  have h2 := muP_pos (p := p) σ
  unfold massOf
  split_ifs <;> positivity

theorem gaussW_le_one {σ : ℝ} (hσ : 0 ≤ σ) (z : ℤ) : gaussW σ z ≤ 1 := by
  unfold gaussW
  rw [Real.exp_le_one_iff]
  have : (0 : ℝ) ≤ (z : ℝ) ^ 2 := sq_nonneg _
  nlinarith

theorem wtB_nonneg (σ : ℝ) (inU : Bool) (ℓ g : Fin 2 → ZMod p) : 0 ≤ wtB σ inU ℓ g := by
  unfold wtB
  split_ifs
  · exact zero_le_one
  · exact gaussW_nonneg _ _

theorem lawOf_nonneg (σ : ℝ) (ℓ : Fin 2 → ZMod p) (c : Fin 3) (inU : Bool) (g : Fin 2 → ZMod p) :
    0 ≤ lawOf σ ℓ c inU g := by
  have h1 := p_sub_one_pos (p := p)
  have hm := massOf_pos (p := p) σ 1 inU
  unfold lawOf
  split_ifs <;> first | positivity | exact div_nonneg (gaussW_nonneg _ _) hm.le

theorem clsG_of_lawOf_ne_zero {σ : ℝ} {ℓ : Fin 2 → ZMod p} {c : Fin 3} {inU : Bool} {g : Fin 2 → ZMod p}
    (h : lawOf σ ℓ c inU g ≠ 0) : clsG ℓ g = c := by
  unfold lawOf at h
  unfold clsG
  by_cases hc1 : c = 1
  · subst hc1
    rw [ite_eq_left rfl] at h
    by_cases hg : ℓ ⬝ᵥ g ≠ 0
    · rw [ite_eq_left hg]
    · rw [ite_eq_right hg] at h
      exact absurd rfl h
  · rw [ite_eq_right hc1] at h
    by_cases hc2 : c = 2
    · subst hc2
      rw [ite_eq_left rfl] at h
      by_cases hg : ℓ ⬝ᵥ g = 0 ∧ g ≠ 0
      · rw [ite_eq_right (not_not.2 hg.1), ite_eq_right hg.2]
      · rw [ite_eq_right hg] at h
        exact absurd rfl h
    · rw [ite_eq_right hc2] at h
      have hc0 : c = 0 := by
        fin_cases c
        · rfl
        · exact absurd rfl hc1
        · exact absurd rfl hc2
      subst hc0
      by_cases hg : g = 0
      · subst hg
        simp
      · rw [ite_eq_right hg] at h
        exact absurd rfl h

theorem fin3_cases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp

theorem wt_cls_eq (σ : ℝ) (ℓ : Fin 2 → ZMod p) (c : Fin 3) (inU : Bool) (g : Fin 2 → ZMod p) :
    (if clsG ℓ g = c then wtB σ inU ℓ g else 0) = massOf p σ c inU * lawOf σ ℓ c inU g := by
  have hm1 := (massOf_pos (p := p) σ 1 inU).ne'
  have h1 := (p_sub_one_pos (p := p)).ne'
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  obtain rfl | rfl | rfl := fin3_cases c
  ·
    have hl : lawOf σ ℓ 0 inU g = if g = 0 then 1 else 0 := by
      rw [lawOf, ite_eq_right h01, ite_eq_right h02]
    have hm : massOf p σ 0 inU = 1 := by rw [massOf, ite_eq_right h01, ite_eq_right h02]
    rw [hl, hm, one_mul]
    by_cases hg0 : g = 0
    · subst hg0
      have hcls : clsG ℓ (0 : Fin 2 → ZMod p) = 0 := by
        unfold clsG
        rw [dotProduct_zero, ite_eq_right (not_not.2 rfl), ite_eq_left rfl]
      rw [ite_eq_left hcls, ite_eq_left rfl, wtB, dotProduct_zero, ZMod.valMinAbs_zero, gaussW_zero]
      split_ifs <;> rfl
    · have hcls : clsG ℓ g ≠ 0 := by
        unfold clsG
        split_ifs <;> decide
      rw [ite_eq_right hcls, ite_eq_right hg0]
  ·
    by_cases hg : ℓ ⬝ᵥ g ≠ 0
    · have hcls : clsG ℓ g = 1 := by unfold clsG; rw [ite_eq_left hg]
      rw [ite_eq_left hcls, lawOf, ite_eq_left rfl, ite_eq_left hg, wtB]
      field_simp
    · have hcls : clsG ℓ g ≠ 1 := by
        unfold clsG
        rw [ite_eq_right hg]
        split_ifs <;> decide
      rw [ite_eq_right hcls, lawOf, ite_eq_left rfl, ite_eq_right hg, mul_zero]
  ·
    have hm : massOf p σ 2 inU = (p : ℝ) - 1 := by rw [massOf, ite_eq_right h21, ite_eq_left rfl]
    by_cases hg : ℓ ⬝ᵥ g = 0 ∧ g ≠ 0
    · have hcls : clsG ℓ g = 2 := by
        unfold clsG
        rw [ite_eq_right (not_not.2 hg.1), ite_eq_right hg.2]
      rw [ite_eq_left hcls, lawOf, ite_eq_right h21, ite_eq_left rfl, ite_eq_left hg, hm, wtB, hg.1, ZMod.valMinAbs_zero,
        gaussW_zero]
      field_simp
      split_ifs <;> rfl
    · have hcls : clsG ℓ g ≠ 2 := by
        unfold clsG
        split_ifs with h3 h4
        · decide
        · decide
        · exact absurd ⟨not_not.1 h3, h4⟩ hg
      rw [ite_eq_right hcls, lawOf, ite_eq_right h21, ite_eq_left rfl, ite_eq_right hg, mul_zero]

theorem wtB_eq_sum (σ : ℝ) (inU : Bool) (ℓ g : Fin 2 → ZMod p) :
    wtB σ inU ℓ g = ∑ c : Fin 3, massOf p σ c inU * lawOf σ ℓ c inU g := by
  rw [← Finset.sum_congr rfl fun c _ => wt_cls_eq σ ℓ c inU g, sum_ite_eq]
  simp

section Patterns

variable {m : ℕ}

theorem sum_wt_le (σ : ℝ) (ℓ : Fin 2 → ZMod p) (U : Finset (Fin m)) (F : (Fin m → Fin 2 → ZMod p) → ℝ)
    (_hF : ∀ w, 0 ≤ F w) (H : (Fin m → Fin 3) → (Fin m → Fin 2 → ZMod p) → ℝ)
    (hH : ∀ cls w, (∀ j, clsG ℓ (w j) = cls j) → F w ≤ H cls w) :
    ∑ w : Fin m → Fin 2 → ZMod p, (∏ j, wtB σ (decide (j ∈ U)) ℓ (w j)) * F w ≤
      ∑ cls : Fin m → Fin 3, (∏ j, massOf p σ (cls j) (decide (j ∈ U))) *
        pexp (fun j => lawOf σ ℓ (cls j) (decide (j ∈ U))) (H cls) := by
  classical
  have e1 : ∀ w : Fin m → Fin 2 → ZMod p, ∏ j, wtB σ (decide (j ∈ U)) ℓ (w j) =
      ∑ cls : Fin m → Fin 3, (∏ j, massOf p σ (cls j) (decide (j ∈ U))) *
        ∏ j, lawOf σ ℓ (cls j) (decide (j ∈ U)) (w j) := by
    intro w
    simp_rw [wtB_eq_sum σ _ ℓ, Fintype.prod_sum]
    exact sum_congr rfl fun cls _ => prod_mul_distrib
  calc ∑ w : Fin m → Fin 2 → ZMod p, (∏ j, wtB σ (decide (j ∈ U)) ℓ (w j)) * F w
      = ∑ cls : Fin m → Fin 3, (∏ j, massOf p σ (cls j) (decide (j ∈ U))) *
          ∑ w : Fin m → Fin 2 → ZMod p, (∏ j, lawOf σ ℓ (cls j) (decide (j ∈ U)) (w j)) * F w := by
        simp_rw [e1, sum_mul, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun cls _ => sum_congr rfl fun w _ => by ring
    _ ≤ ∑ cls : Fin m → Fin 3, (∏ j, massOf p σ (cls j) (decide (j ∈ U))) *
          pexp (fun j => lawOf σ ℓ (cls j) (decide (j ∈ U))) (H cls) := by
        refine sum_le_sum fun cls _ => mul_le_mul_of_nonneg_left ?_
          (prod_nonneg fun j _ => (massOf_pos σ _ _).le)
        unfold pexp
        refine sum_le_sum fun w _ => ?_
        by_cases hw : ∀ j, clsG ℓ (w j) = cls j
        · exact mul_le_mul_of_nonneg_left (hH cls w hw) (prod_nonneg fun j _ => lawOf_nonneg σ ℓ _ _ _)
        · push Not at hw
          obtain ⟨j, hj⟩ := hw
          have h0 : lawOf σ ℓ (cls j) (decide (j ∈ U)) (w j) = 0 := by
            by_contra h
            exact hj (clsG_of_lawOf_ne_zero h)
          rw [prod_eq_zero (mem_univ j) h0, zero_mul, zero_mul]

theorem sum_prod_massOf (σ : ℝ) (U : Finset (Fin m)) :
    ∑ cls : Fin m → Fin 3, ∏ j, massOf p σ (cls j) (decide (j ∈ U)) =
      ∏ j, ∑ c : Fin 3, massOf p σ c (decide (j ∈ U)) := by
  classical
  rw [Fintype.prod_sum]

theorem sum_massOf (σ : ℝ) (inU : Bool) :
    ∑ c : Fin 3, massOf p σ c inU = if inU then (p : ℝ) ^ 2 else p * (1 + muP p σ) := by
  rw [Fin.sum_univ_three]
  cases inU <;> simp [massOf] <;> ring

end Patterns

def bcls (X : Fin 3) : Fin 3 × Bool := if X = 0 then (1, true) else if X = 1 then (1, false) else (2, true)

noncomputable def lawX (σ : ℝ) (ℓ : Fin 2 → ZMod p) (X : Fin 3) : (Fin 2 → ZMod p) → ℝ :=
  lawOf σ ℓ (bcls X).1 (bcls X).2

variable (p) in
noncomputable def massX (σ : ℝ) (X : Fin 3) : ℝ := massOf p σ (bcls X).1 (bcls X).2

theorem lawOf_two (σ : ℝ) (ℓ : Fin 2 → ZMod p) (inU : Bool) : lawOf σ ℓ 2 inU = lawX σ ℓ 2 := by
  funext g
  simp [lawX, lawOf, bcls]

theorem massOf_two (σ : ℝ) (inU : Bool) : massOf p σ 2 inU = massX p σ 2 := by
  simp [massX, massOf, bcls]

theorem lawX_nonneg (σ : ℝ) (ℓ : Fin 2 → ZMod p) (X : Fin 3) (g : Fin 2 → ZMod p) : 0 ≤ lawX σ ℓ X g :=
  lawOf_nonneg _ _ _ _ _

theorem lawX_zero (σ : ℝ) (ℓ : Fin 2 → ZMod p) (X : Fin 3) : lawX σ ℓ X 0 = 0 := by
  obtain rfl | rfl | rfl := fin3_cases X <;> simp [lawX, lawOf, bcls]

theorem massX_pos (σ : ℝ) (X : Fin 3) : 0 < massX p σ X := massOf_pos _ _ _

theorem lawX_zero_eq (σ : ℝ) (ℓ : Fin 2 → ZMod p) :
    lawX σ ℓ 0 = fun g => if ℓ ⬝ᵥ g ≠ 0 then 1 / ((p : ℝ) * (p - 1)) else 0 := by
  funext g
  simp [lawX, bcls, lawOf, massOf]

theorem lawX_one_eq (σ : ℝ) (ℓ : Fin 2 → ZMod p) :
    lawX σ ℓ 1 = fun g => if ℓ ⬝ᵥ g ≠ 0 then gaussW σ (ℓ ⬝ᵥ g).valMinAbs / ((p : ℝ) * muP p σ) else 0 := by
  funext g
  simp [lawX, bcls, lawOf, massOf]

theorem lawX_two_eq (σ : ℝ) (ℓ : Fin 2 → ZMod p) :
    lawX σ ℓ 2 = fun g => if ℓ ⬝ᵥ g = 0 ∧ g ≠ 0 then 1 / ((p : ℝ) - 1) else 0 := by
  funext g
  simp [lawX, bcls, lawOf]

theorem massX_zero_eq (σ : ℝ) : massX p σ 0 = (p : ℝ) * (p - 1) := by simp [massX, bcls, massOf]

theorem massX_one_eq (σ : ℝ) : massX p σ 1 = (p : ℝ) * muP p σ := by simp [massX, bcls, massOf]

theorem massX_two_eq (σ : ℝ) : massX p σ 2 = (p : ℝ) - 1 := by simp [massX, bcls, massOf]

theorem lawX_le {σ : ℝ} (hσ : 0 ≤ σ) (ℓ : Fin 2 → ZMod p) (X : Fin 3) (g : Fin 2 → ZMod p) :
    lawX σ ℓ X g ≤ 1 / massX p σ X := by
  have hm := massX_pos (p := p) σ X
  obtain rfl | rfl | rfl := fin3_cases X
  · rw [lawX_zero_eq, ← massX_zero_eq σ]
    dsimp only
    split_ifs <;> first | exact le_rfl | positivity
  · rw [lawX_one_eq, ← massX_one_eq σ]
    dsimp only
    split_ifs
    · exact div_le_div_of_nonneg_right (gaussW_le_one hσ _) hm.le
    · positivity
  · rw [lawX_two_eq, ← massX_two_eq σ]
    dsimp only
    split_ifs <;> first | exact le_rfl | positivity

theorem sum_lawX (σ : ℝ) (ℓ : Fin 2 → ZMod p) (hℓ : ℓ ≠ 0) (X : Fin 3) : ∑ g, lawX σ ℓ X g = 1 := by
  have h1 := (p_sub_one_pos (p := p)).ne'
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hμ := (muP_pos (p := p) σ).ne'
  obtain rfl | rfl | rfl := fin3_cases X
  · rw [lawX_zero_eq]
    have e : ∀ g : Fin 2 → ZMod p, (if ℓ ⬝ᵥ g ≠ 0 then 1 / ((p : ℝ) * (p - 1)) else 0) =
        (if ℓ ⬝ᵥ g ≠ 0 then (1 : ℝ) else 0) / ((p : ℝ) * (p - 1)) := fun g => by
      split_ifs <;> simp
    simp_rw [e]
    rw [← sum_div, sum_dot_ne_zero ℓ hℓ, div_self (mul_ne_zero hp h1)]
  · rw [lawX_one_eq]
    have e : ∀ g : Fin 2 → ZMod p, (if ℓ ⬝ᵥ g ≠ 0 then gaussW σ (ℓ ⬝ᵥ g).valMinAbs /
        ((p : ℝ) * muP p σ) else 0) = (fun a : ZMod p => if a ≠ 0 then gaussW σ a.valMinAbs else 0)
          (ℓ ⬝ᵥ g) / ((p : ℝ) * muP p σ) := fun g => by
      dsimp only
      split_ifs <;> simp
    simp_rw [e]
    have h2 : ∑ g : Fin 2 → ZMod p, (if ℓ ⬝ᵥ g ≠ 0 then gaussW σ (ℓ ⬝ᵥ g).valMinAbs else 0) =
        p * muP p σ := sum_dot_eq ℓ hℓ (fun a => if a ≠ 0 then gaussW σ a.valMinAbs else 0)
    rw [← sum_div, h2, div_self (mul_ne_zero hp hμ)]
  · rw [lawX_two_eq]
    have e : ∀ g : Fin 2 → ZMod p, (if ℓ ⬝ᵥ g = 0 ∧ g ≠ 0 then 1 / ((p : ℝ) - 1) else 0) =
        (if ℓ ⬝ᵥ g = 0 ∧ g ≠ 0 then (1 : ℝ) else 0) / ((p : ℝ) - 1) := fun g => by
      split_ifs <;> simp
    simp_rw [e]
    rw [← sum_div, sum_dot_eq_zero_ne ℓ hℓ, div_self h1]

open Classical in
theorem card_line (L : Submodule (ZMod p) (Fin 2 → ZMod p)) (hL : finrank (ZMod p) L = 1) :
    (univ.filter (· ∈ L)).card = p := by
  classical
  have h1 : (univ.filter (· ∈ L)).card = Fintype.card L := by
    rw [Fintype.card_subtype]
  rw [h1, Module.card_eq_pow_finrank (K := ZMod p) (V := L), hL, pow_one, ZMod.card]

theorem dot_injOn_line (ℓ : Fin 2 → ZMod p) (L : Submodule (ZMod p) (Fin 2 → ZMod p))
    (hL : finrank (ZMod p) L = 1) {a a' : Fin 2 → ZMod p} (ha : a ∈ L) (ha' : a' ∈ L)
    (hℓa : ℓ ⬝ᵥ a ≠ 0) (h : ℓ ⬝ᵥ a = ℓ ⬝ᵥ a') : a = a' := by
  have ha0 : (⟨a, ha⟩ : L) ≠ 0 := by
    intro h0
    have : a = 0 := congrArg Subtype.val h0
    rw [this, dotProduct_zero] at hℓa
    exact hℓa rfl
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨a, ha⟩ : L) ha0).1 hL ⟨a', ha'⟩
  have hc' : c • a = a' := congrArg Subtype.val hc
  rw [← hc', dotProduct_smul, smul_eq_mul] at h
  have hc1 : c = 1 := by
    have : (c - 1) * (ℓ ⬝ᵥ a) = 0 := by rw [sub_mul, ← h]; ring
    rcases mul_eq_zero.1 this with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hℓa
  rw [← hc', hc1, one_smul]

theorem subMeas_lawX_le (σ : ℝ) (ℓ : Fin 2 → ZMod p) (_hℓ : ℓ ≠ 0) (X : Fin 3) (hX : X ≠ 2)
    (L : Submodule (ZMod p) (Fin 2 → ZMod p)) (hL : finrank (ZMod p) L = 1) :
    subMeas (lawX σ ℓ X) L ≤ 1 / p := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 := p_sub_one_pos (p := p)
  have hμ := muP_pos (p := p) σ
  unfold subMeas
  set S := univ.filter (· ∈ L) with hS
  obtain rfl | rfl | rfl := fin3_cases X
  ·
    rw [lawX_zero_eq]
    dsimp only
    have hcount : ∑ a ∈ S, (if ℓ ⬝ᵥ a ≠ 0 then (1 : ℝ) else 0) ≤ (p : ℝ) - 1 := by
      have h2 : ∑ a ∈ S, (if ℓ ⬝ᵥ a ≠ 0 then (1 : ℝ) else 0) ≤ ∑ a ∈ S.erase 0, (1 : ℝ) := by
        rw [← sum_erase_add S _ (mem_filter.2 ⟨mem_univ _, L.zero_mem⟩), dotProduct_zero, ite_eq_right (by simp),
          add_zero]
        exact sum_le_sum fun a _ => by split_ifs <;> norm_num
      rw [sum_const, nsmul_eq_mul, mul_one, card_erase_of_mem (mem_filter.2 ⟨mem_univ _, L.zero_mem⟩),
        hS, card_line L hL] at h2
      have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
      push_cast [hp1] at h2
      exact h2
    have e : ∀ a, (if ℓ ⬝ᵥ a ≠ 0 then 1 / ((p : ℝ) * (p - 1)) else 0) =
        (if ℓ ⬝ᵥ a ≠ 0 then (1 : ℝ) else 0) / ((p : ℝ) * (p - 1)) := fun a => by split_ifs <;> simp
    simp_rw [e]
    rw [← sum_div, div_le_div_iff₀ (by positivity) hp]
    nlinarith
  ·
    rw [lawX_one_eq]
    dsimp only
    have hinj : Set.InjOn (fun a => ℓ ⬝ᵥ a) (S.filter fun a => ℓ ⬝ᵥ a ≠ 0) := by
      intro a ha a' ha' h
      simp only [coe_filter, Set.mem_ofPred_eq, hS, mem_filter, mem_univ, true_and] at ha ha'
      exact dot_injOn_line ℓ L hL ha.1 ha'.1 ha.2 h
    have hsum : ∑ a ∈ S, (if ℓ ⬝ᵥ a ≠ 0 then gaussW σ (ℓ ⬝ᵥ a).valMinAbs else 0) ≤ muP p σ := by
      rw [← sum_filter, ← sum_image (f := fun b : ZMod p => gaussW σ b.valMinAbs) hinj, muP, ← sum_filter]
      refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => gaussW_nonneg _ _
      intro b hb
      rw [mem_image] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      rw [mem_filter] at ha ⊢
      exact ⟨mem_univ _, ha.2⟩
    have e : ∀ a, (if ℓ ⬝ᵥ a ≠ 0 then gaussW σ (ℓ ⬝ᵥ a).valMinAbs / ((p : ℝ) * muP p σ) else 0) =
        (if ℓ ⬝ᵥ a ≠ 0 then gaussW σ (ℓ ⬝ᵥ a).valMinAbs else 0) / ((p : ℝ) * muP p σ) := fun a => by
      split_ifs <;> simp
    simp_rw [e]
    rw [← sum_div, div_le_div_iff₀ (by positivity) hp]
    nlinarith
  · exact absurd rfl hX

theorem lawOf_one_true (σ : ℝ) (ℓ : Fin 2 → ZMod p) : lawOf σ ℓ 1 true = lawX σ ℓ 0 := by
  simp [lawX, bcls]

theorem lawOf_one_false (σ : ℝ) (ℓ : Fin 2 → ZMod p) : lawOf σ ℓ 1 false = lawX σ ℓ 1 := by
  simp [lawX, bcls]

theorem massOf_one_true (σ : ℝ) : massOf p σ 1 true = massX p σ 0 := by simp [massX, bcls]

theorem massOf_one_false (σ : ℝ) : massOf p σ 1 false = massX p σ 1 := by simp [massX, bcls]

theorem massOf_zero (σ : ℝ) (inU : Bool) : massOf p σ 0 inU = 1 := by simp [massOf]

theorem sum_lawOf (σ : ℝ) (ℓ : Fin 2 → ZMod p) (hℓ : ℓ ≠ 0) (c : Fin 3) (inU : Bool) :
    ∑ g, lawOf σ ℓ c inU g = 1 := by
  obtain rfl | rfl | rfl := fin3_cases c
  · simp [lawOf]
  · cases inU
    · rw [lawOf_one_false]
      exact sum_lawX σ ℓ hℓ 1
    · rw [lawOf_one_true]
      exact sum_lawX σ ℓ hℓ 0
  · rw [lawOf_two]
    exact sum_lawX σ ℓ hℓ 2

section Classes

variable {m : ℕ}

def Dcls (U : Finset (Fin m)) (cls : Fin m → Fin 3) (X : Fin 3) : Finset (Fin m) :=
  if X = 0 then univ.filter (fun j => j ∈ U ∧ cls j = 1)
  else if X = 1 then univ.filter (fun j => j ∉ U ∧ cls j = 1)
  else univ.filter (fun j => cls j = 2)

theorem mem_Dcls_zero {U : Finset (Fin m)} {cls : Fin m → Fin 3} {j : Fin m} :
    j ∈ Dcls U cls 0 ↔ j ∈ U ∧ cls j = 1 := by
  simp [Dcls]

theorem mem_Dcls_one {U : Finset (Fin m)} {cls : Fin m → Fin 3} {j : Fin m} :
    j ∈ Dcls U cls 1 ↔ j ∉ U ∧ cls j = 1 := by
  simp [Dcls]

theorem mem_Dcls_two {U : Finset (Fin m)} {cls : Fin m → Fin 3} {j : Fin m} :
    j ∈ Dcls U cls 2 ↔ cls j = 2 := by
  simp [Dcls]

theorem Dcls_disjoint (U : Finset (Fin m)) (cls : Fin m → Fin 3) {X Y : Fin 3} (hXY : X ≠ Y) :
    Disjoint (Dcls U cls X) (Dcls U cls Y) := by
  rw [Finset.disjoint_left]
  intro j hX hY
  obtain rfl | rfl | rfl := fin3_cases X <;> obtain rfl | rfl | rfl := fin3_cases Y <;>
    simp_all [mem_Dcls_zero, mem_Dcls_one, mem_Dcls_two]

theorem sum_card_Dcls_le (U : Finset (Fin m)) (cls : Fin m → Fin 3) :
    ∑ X : Fin 3, (Dcls U cls X).card ≤ m := by
  rw [← card_biUnion fun X _ Y _ hXY => Dcls_disjoint U cls hXY]
  calc (univ.biUnion (Dcls U cls)).card ≤ (univ : Finset (Fin m)).card := card_le_univ _
    _ = m := by rw [card_univ, Fintype.card_fin]

theorem lawOf_of_mem_Dcls (σ : ℝ) (ℓ : Fin 2 → ZMod p) {U : Finset (Fin m)} {cls : Fin m → Fin 3}
    {X : Fin 3} {j : Fin m} (hj : j ∈ Dcls U cls X) :
    lawOf σ ℓ (cls j) (decide (j ∈ U)) = lawX σ ℓ X := by
  obtain rfl | rfl | rfl := fin3_cases X
  · rw [mem_Dcls_zero] at hj
    rw [hj.2, decide_eq_true hj.1, lawOf_one_true]
  · rw [mem_Dcls_one] at hj
    rw [hj.2, decide_eq_false hj.1, lawOf_one_false]
  · rw [mem_Dcls_two] at hj
    rw [hj, lawOf_two]

theorem prod_massOf_eq (σ : ℝ) (U : Finset (Fin m)) (cls : Fin m → Fin 3) :
    ∏ j, massOf p σ (cls j) (decide (j ∈ U)) = ∏ X : Fin 3, massX p σ X ^ (Dcls U cls X).card := by
  classical
  have e : ∀ j, massOf p σ (cls j) (decide (j ∈ U)) =
      ∏ X : Fin 3, (if j ∈ Dcls U cls X then massX p σ X else 1) := by
    intro j
    rw [Fin.prod_univ_three]
    simp only [mem_Dcls_zero, mem_Dcls_one, mem_Dcls_two]
    obtain h | h | h := fin3_cases (cls j)
    · rw [h, massOf_zero]
      simp
    · by_cases hj : j ∈ U
      · rw [h, decide_eq_true hj, massOf_one_true]
        simp [hj]
      · rw [h, decide_eq_false hj, massOf_one_false]
        simp [hj]
    · rw [h, massOf_two]
      simp
  simp_rw [e]
  rw [prod_comm]
  refine prod_congr rfl fun X _ => ?_
  rw [prod_ite_mem, univ_inter, prod_const]

end Classes

end DGS
