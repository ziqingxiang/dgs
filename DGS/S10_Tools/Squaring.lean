module

public import DGS.S10_Tools.Dilates

@[expose] public section

open Finset Matrix
open scoped Real ComplexConjugate

namespace DGS

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

abbrev SignPair (m : ℕ) := (Fin m → Bool) × (Fin m → Bool)

def sgnP (p : ℕ) (ξ : Fin m → Bool) : Fin m → ZMod p := fun j => ((sgnZ (ξ j) : ℤ) : ZMod p)

def uPair (p : ℕ) (c : SignPair m) : Fin m → ZMod p :=
  fun j => if c.1 j = c.2 j then 0 else ((sgnZ (c.1 j) : ℤ) : ZMod p)

def vPair (p : ℕ) (c : SignPair m) : Fin m → ZMod p :=
  fun j => if c.1 j = c.2 j then ((sgnZ (c.1 j) : ℤ) : ZMod p) else 0

noncomputable def quadSum (B : Matrix (Fin m) (Fin m) (ZMod p)) (t : ZMod p) : ℂ :=
  ((2 : ℂ) ^ m)⁻¹ * ∑ ξ : Fin m → Bool, ZMod.stdAddChar (t * (sgnP p ξ ⬝ᵥ (B *ᵥ sgnP p ξ)))

theorem sgnZ_cast_ne_zero (b : Bool) : ((sgnZ b : ℤ) : ZMod p) ≠ 0 := by
  cases b <;> simp [sgnZ]

theorem uPair_eq_zero_iff (c : SignPair m) (j : Fin m) : uPair p c j = 0 ↔ c.1 j = c.2 j := by
  unfold uPair
  split_ifs with h
  · simp [h]
  · simp [h, sgnZ_cast_ne_zero]

theorem sgnP_fst (c : SignPair m) : sgnP p c.1 = uPair p c + vPair p c := by
  funext j
  simp only [sgnP, uPair, vPair, Pi.add_apply]
  split_ifs <;> simp

theorem sgnP_snd (c : SignPair m) : sgnP p c.2 = vPair p c - uPair p c := by
  funext j
  simp only [sgnP, uPair, vPair, Pi.sub_apply]
  split_ifs with h
  · rw [h]
    simp
  · cases h1 : c.1 j <;> cases h2 : c.2 j <;> simp_all [sgnZ]

theorem quad_diff (B : Matrix (Fin m) (Fin m) (ZMod p)) (hB : B.IsSymm) (u v : Fin m → ZMod p) :
    (u + v) ⬝ᵥ (B *ᵥ (u + v)) - (v - u) ⬝ᵥ (B *ᵥ (v - u)) = 4 * ((B *ᵥ u) ⬝ᵥ v) := by
  have h1 : u ⬝ᵥ (B *ᵥ v) = (B *ᵥ u) ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hB.eq]
  have h2 : v ⬝ᵥ (B *ᵥ u) = (B *ᵥ u) ⬝ᵥ v := dotProduct_comm _ _
  simp only [mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub]
  linear_combination (2 : ZMod p) * h1 + 2 * h2

def flipPair (s : Fin m → Bool) (c : SignPair m) : SignPair m :=
  (fun j => if s j = true ∧ c.1 j = c.2 j then !c.1 j else c.1 j,
   fun j => if s j = true ∧ c.1 j = c.2 j then !c.2 j else c.2 j)

theorem sgnZ_not (b : Bool) : sgnZ (!b) = -sgnZ b := by
  cases b <;> rfl

theorem flipPair_involutive (s : Fin m → Bool) : Function.Involutive (flipPair s) := by
  intro c
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
  · by_cases hs : s j = true <;> by_cases h : c.1 j = c.2 j <;> simp [flipPair, hs, h]

omit [Fact (Nat.Prime p)] in
theorem uPair_flipPair (s : Fin m → Bool) (c : SignPair m) : uPair p (flipPair s c) = uPair p c := by
  funext j
  by_cases hs : s j = true <;> by_cases h : c.1 j = c.2 j <;> simp [uPair, flipPair, hs, h]

theorem vPair_flipPair (s : Fin m → Bool) (c : SignPair m) (j : Fin m) :
    vPair p (flipPair s c) j = if s j then -vPair p c j else vPair p c j := by
  by_cases hs : s j = true <;> by_cases h : c.1 j = c.2 j <;> simp [vPair, flipPair, hs, h, sgnZ_not]

theorem cosP_neg (x : ZMod p) : cosP (-x) = cosP x := by
  rw [cosP_eq_of_cast (-x) (-(x.val : ℤ)) (by simp), cosP]
  rw [show 2 * π * (((-(x.val : ℤ)) : ℤ) : ℝ) / p = -(2 * π * (x.val : ℝ) / p) by push_cast; ring,
    Real.cos_neg]

theorem cosP_zero : cosP (0 : ZMod p) = 1 := by
  simp [cosP]

theorem abs_cosP_mul_vPair (c : SignPair m) (j : Fin m) (a : ZMod p) :
    |cosP (a * vPair p c j)| = if uPair p c j = 0 then |cosP a| else 1 := by
  by_cases h : c.1 j = c.2 j
  · rw [ite_eq_left ((uPair_eq_zero_iff c j).2 h)]
    simp only [vPair, ite_eq_left h]
    cases c.1 j
    · simp [sgnZ, cosP_neg]
    · simp [sgnZ]
  · rw [ite_eq_right (fun hu => h ((uPair_eq_zero_iff c j).1 hu))]
    simp [vPair, h, cosP_zero]

theorem lem_squaring (B : Matrix (Fin m) (Fin m) (ZMod p)) (hB : B.IsSymm) (t : ZMod p) :
    ‖quadSum B t‖ ^ 2 ≤ expect (fun c : SignPair m =>
      ∏ j : {j // uPair p c j = 0}, |cosP (4 * t * (B *ᵥ uPair p c) j)|) := by
  set ψ := (ZMod.stdAddChar : AddChar (ZMod p) ℂ) with hψ
  set G : SignPair m → ℂ := fun c => ψ (4 * t * ((B *ᵥ uPair p c) ⬝ᵥ vPair p c)) with hG
  set a : ℂ := ((2 : ℂ) ^ m)⁻¹ with ha
  have ha_conj : conj a = a := by
    rw [ha, map_inv₀, map_pow, map_ofNat]
  have h1 : ‖quadSum B t‖ ^ 2 = ‖a ^ 2 * ∑ c, G c‖ := by
    have e1 : quadSum B t * conj (quadSum B t) = a ^ 2 * ∑ c, G c := by
      rw [quadSum, map_mul, ← ha, ha_conj, map_sum, mul_mul_mul_comm, ← sq, Finset.sum_mul_sum,
        ← Fintype.sum_prod_type']
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, hG]
      congr 1
      rw [← sub_eq_add_neg, ← mul_sub, sgnP_fst, sgnP_snd, quad_diff B hB]
      ring
    rw [← e1, norm_mul, RCLike.norm_conj, sq]
  have hflip : ∀ s : Fin m → Bool, ∑ c, G c = ∑ c, G (flipPair s c) := fun s =>
    (Equiv.sum_comp (Function.Involutive.toPerm _ (flipPair_involutive s)) G).symm
  have havg : ∀ c : SignPair m, ∑ s : Fin m → Bool, G (flipPair s c) =
      (2 : ℂ) ^ m * ∏ j, (cosP (4 * t * (B *ᵥ uPair p c) j * vPair p c j) : ℂ) := by
    intro c
    have e2 : ∀ s : Fin m → Bool, G (flipPair s c) =
        ∏ j, ψ (if s j then -(4 * t * (B *ᵥ uPair p c) j * vPair p c j)
          else 4 * t * (B *ᵥ uPair p c) j * vPair p c j) := by
      intro s
      rw [hG]
      simp only
      rw [uPair_flipPair, dotProduct, mul_sum, addChar_map_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [vPair_flipPair]
      split_ifs <;> ring_nf
    simp_rw [e2]
    rw [← Fintype.prod_sum (fun j (b : Bool) => ψ (if b then -(4 * t * (B *ᵥ uPair p c) j *
      vPair p c j) else 4 * t * (B *ᵥ uPair p c) j * vPair p c j))]
    rw [show (2 : ℂ) ^ m = ∏ _j : Fin m, (2 : ℂ) by simp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool, ite_eq_left rfl, ite_eq_right Bool.false_ne_true, add_comm, stdAddChar_add_neg]
  have h2 : ∑ c, G c = ∑ c : SignPair m, ∏ j, (cosP (4 * t * (B *ᵥ uPair p c) j * vPair p c j) : ℂ) := by
    have h2m : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
    apply mul_left_cancel₀ h2m
    calc (2 : ℂ) ^ m * ∑ c, G c = ∑ s : Fin m → Bool, ∑ c, G c := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ = ∑ s : Fin m → Bool, ∑ c, G (flipPair s c) := Finset.sum_congr rfl fun s _ => hflip s
      _ = ∑ c, ∑ s : Fin m → Bool, G (flipPair s c) := Finset.sum_comm
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => havg c
  rw [h1, h2]
  have hcard : (Fintype.card (SignPair m) : ℝ) = 2 ^ m * 2 ^ m := by
    simp [Fintype.card_prod]
  calc ‖a ^ 2 * ∑ c : SignPair m, ∏ j, (cosP (4 * t * (B *ᵥ uPair p c) j * vPair p c j) : ℂ)‖
      ≤ ‖a‖ ^ 2 * ∑ c : SignPair m, ∏ j, |cosP (4 * t * (B *ᵥ uPair p c) j * vPair p c j)| := by
        rw [norm_mul, norm_pow]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) (by positivity)
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [norm_prod]
        refine Finset.prod_congr rfl fun j _ => ?_
        exact Complex.norm_real _
    _ = expect (fun c : SignPair m =>
          ∏ j : {j // uPair p c j = 0}, |cosP (4 * t * (B *ᵥ uPair p c) j)|) := by
        unfold expect
        rw [hcard, ha, norm_inv, norm_pow, RCLike.norm_ofNat, div_eq_inv_mul]
        congr 1
        · rw [inv_pow, ← pow_mul, ← pow_add]
          ring_nf
        · refine Finset.sum_congr rfl fun c _ => ?_
          simp_rw [abs_cosP_mul_vPair]
          rw [← Finset.prod_filter]
          exact Finset.prod_subtype _ (fun j => by simp) _

theorem lem_squaring_bound (hp2 : p ≠ 2) (B : Matrix (Fin m) (Fin m) (ZMod p)) (hB : B.IsSymm)
    {t : ZMod p} (ht : t ≠ 0) {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 200)
    (hprob : prob (fun x : SignPair m =>
      (muMin (fun j : {j // uPair p x j = 0} => (B *ᵥ uPair p x) j) : ℝ) ≤ c * m * (p : ℝ) ^ 2) ≤
        Real.exp (-(m : ℝ) / 100)) :
    ‖quadSum B t‖ ^ 2 ≤ 2 * Real.exp (-2 * c * m) := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h4t : (4 : ZMod p) * t ≠ 0 := by
    refine mul_ne_zero ?_ ht
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero (two_ne_zero_zmod hp2) (two_ne_zero_zmod hp2)
  set P : SignPair m → Prop := fun x =>
    (muMin (fun j : {j // uPair p x j = 0} => (B *ᵥ uPair p x) j) : ℝ) ≤ c * m * (p : ℝ) ^ 2 with hP
  have hpt : ∀ x : SignPair m, ∏ j : {j // uPair p x j = 0}, |cosP (4 * t * (B *ᵥ uPair p x) j)| ≤
      (if P x then 1 else 0) + Real.exp (-2 * c * m) := by
    intro x
    by_cases hx : P x
    · rw [ite_eq_left hx]
      have : ∏ j : {j // uPair p x j = 0}, |cosP (4 * t * (B *ᵥ uPair p x) j)| ≤ 1 :=
        Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ => abs_cosP_le_one _
      linarith [Real.exp_pos (-2 * c * m)]
    · rw [ite_eq_right hx, zero_add]
      have h1 := lem_dilates hp2 (fun j : {j // uPair p x j = 0} => (B *ᵥ uPair p x) j) h4t
      refine h1.trans (Real.exp_le_exp.2 ?_)
      rw [hP] at hx
      push Not at hx
      have : -2 * (muMin (fun j : {j // uPair p x j = 0} => (B *ᵥ uPair p x) j) : ℝ) / (p : ℝ) ^ 2 ≤
          -2 * (c * m * (p : ℝ) ^ 2) / (p : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      calc _ ≤ -2 * (c * m * (p : ℝ) ^ 2) / (p : ℝ) ^ 2 := this
        _ = -2 * c * m := by field_simp
  have hE : expect (fun x : SignPair m =>
      ∏ j : {j // uPair p x j = 0}, |cosP (4 * t * (B *ᵥ uPair p x) j)|) ≤
      prob P + Real.exp (-2 * c * m) := by
    refine (expect_mono hpt).trans (le_of_eq ?_)
    rw [expect_add, expect_const]
    congr 1
    convert expect_indicator' P
  have hexp : Real.exp (-(m : ℝ) / 100) ≤ Real.exp (-2 * c * m) := by
    apply Real.exp_le_exp.2
    have : 2 * c ≤ 1 / 100 := by linarith
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  calc ‖quadSum B t‖ ^ 2 ≤ _ := lem_squaring B hB t
    _ ≤ prob P + Real.exp (-2 * c * m) := hE
    _ ≤ Real.exp (-2 * c * m) + Real.exp (-2 * c * m) := by
        have := hprob.trans hexp
        rw [hP]
        linarith
    _ = 2 * Real.exp (-2 * c * m) := by ring

end DGS
