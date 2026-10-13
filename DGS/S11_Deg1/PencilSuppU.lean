module

public import DGS.S11_Deg1.PencilGood
public import DGS.S11_Deg1.FourierInv

@[expose] public section

open Finset Matrix Module

namespace DGS

variable {m : ℕ}

def suppU (x : SignPair m) : Finset (Fin m) := univ.filter fun j => x.1 j ≠ x.2 j

theorem bxor_bxor_cancel (a b : Bool) : xor a (xor a b) = b := by cases a <;> cases b <;> rfl

def pairDiffEquiv : SignPair m ≃ (Fin m → Bool) × (Fin m → Bool) where
  toFun x := (x.1, fun j => xor (x.1 j) (x.2 j))
  invFun y := (y.1, fun j => xor (y.1 j) (y.2 j))
  left_inv _x := Prod.ext rfl (funext fun _j => bxor_bxor_cancel _ _)
  right_inv _y := Prod.ext rfl (funext fun _j => bxor_bxor_cancel _ _)

theorem pairDiffEquiv_symm_apply (ξ d : Fin m → Bool) :
    pairDiffEquiv.symm (ξ, d) = (ξ, fun j => xor (ξ j) (d j)) := rfl

theorem suppU_pairDiff (ξ d : Fin m → Bool) :
    suppU (pairDiffEquiv.symm (ξ, d)) = univ.filter fun j => d j = true := by
  ext j
  have h : (pairDiffEquiv.symm (ξ, d)).1 j ≠ (pairDiffEquiv.symm (ξ, d)).2 j ↔ d j = true := by
    rw [pairDiffEquiv_symm_apply]
    by_cases hξ : ξ j <;> by_cases hd : d j <;> simp [hξ, hd]
  simp only [suppU, mem_filter, mem_univ, true_and]
  exact h

variable {p : ℕ} [Fact p.Prime]

variable (p) in
def uOn (U : Finset (Fin m)) (ξ : Fin m → Bool) : Fin m → ZMod p := diagSet U *ᵥ sgnP p ξ

theorem uPair_pairDiff (ξ d : Fin m → Bool) :
    uPair p (pairDiffEquiv.symm (ξ, d)) = uOn p (univ.filter fun j => d j = true) ξ := by
  funext j
  rw [uOn, diagSet_mulVec, pairDiffEquiv_symm_apply]
  simp only [uPair, mem_filter, mem_univ, true_and, sgnP]
  by_cases hξ : ξ j <;> by_cases hd : d j <;> simp [hξ, hd]

theorem uPair_eq_zero_iff_not_mem (x : SignPair m) (j : Fin m) : uPair p x j = 0 ↔ j ∉ suppU x := by
  rw [uPair_eq_zero_iff, suppU, mem_filter]
  simp

theorem prob_CuR_zero_le (hp2 : p ≠ 2) (C : Matrix (Fin m) (Fin m) (ZMod p)) (U R : Finset (Fin m)) :
    prob (fun ξ : Fin m → Bool => ∀ j ∈ R, (C *ᵥ uOn p U ξ) j = 0) ≤
      1 / 2 ^ (diagSet R * C * diagSet U).rank := by
  have hF : (1 : ZMod p) ≠ -1 := one_ne_neg_one_zmod hp2
  have h := prob_affine_mem_le hF (diagSet R * C * diagSet U).mulVecLin 0 ⊥
  rw [finrank_bot, pow_zero] at h
  refine le_trans (le_of_eq (prob_congr fun ξ => ?_)) h
  rw [add_zero, Submodule.mem_bot, mulVecLin_apply, ← mulVec_mulVec, ← mulVec_mulVec, uOn,
    sgnP_eq_twoValued]
  constructor
  · intro h0
    funext j
    rw [diagSet_mulVec]
    split_ifs with hj
    · exact h0 j hj
    · rfl
  · intro h0 j hj
    have := congrFun h0 j
    rw [diagSet_mulVec, ite_eq_left hj] at this
    exact this

theorem card_small_subsets_le (X : Finset (Fin m)) :
    (((X.powerset.filter fun S => 100 * S.card < m).card : ℕ) : ℝ) ≤
      (64 : ℝ) ^ (m / 100) * (65 / 64) ^ X.card := by
  set K := m / 100 with hK
  have h1 : ∀ S ∈ X.powerset.filter (fun S => 100 * S.card < m),
      (1 : ℝ) ≤ (64 : ℝ) ^ K * ((1 : ℝ) / 64) ^ S.card := by
    intro S hS
    rw [mem_filter] at hS
    have hSK : S.card ≤ K := by omega
    have e : (64 : ℝ) ^ K = 64 ^ (K - S.card) * 64 ^ S.card := by
      rw [← pow_add, Nat.sub_add_cancel hSK]
    rw [e, mul_assoc, ← mul_pow, show (64 : ℝ) * (1 / 64) = 1 by norm_num, one_pow, mul_one]
    exact one_le_pow₀ (by norm_num)
  calc (((X.powerset.filter fun S => 100 * S.card < m).card : ℕ) : ℝ)
      = ∑ _S ∈ X.powerset.filter (fun S => 100 * S.card < m), (1 : ℝ) := by
        rw [sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ S ∈ X.powerset.filter (fun S => 100 * S.card < m), (64 : ℝ) ^ K * ((1 : ℝ) / 64) ^ S.card :=
        sum_le_sum h1
    _ ≤ ∑ S ∈ X.powerset, (64 : ℝ) ^ K * ((1 : ℝ) / 64) ^ S.card :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
    _ = (64 : ℝ) ^ K * (65 / 64) ^ X.card := by
        rw [← mul_sum]
        congr 1
        have := Finset.sum_pow_mul_eq_add_pow ((1 : ℝ) / 64) 1 X
        simp only [one_pow, mul_one] at this
        rw [this]
        norm_num

theorem two_pow_eq_exp (n : ℕ) : (2 : ℝ) ^ n = Real.exp (Real.log 2 * n) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]

theorem supp_numeric {N r : ℕ} (hN : 5 * N ≤ 3 * m) (hr : 0.13 * (m : ℝ) ≤ r) :
    (64 : ℝ) ^ (m / 100) * (65 / 64) ^ N * (1 / 2 ^ r) ≤ Real.exp (-(m : ℝ) / 30) := by
  have hl1 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2 : Real.log 2 ≤ 0.6932 := by have := Real.log_two_lt_d9; linarith
  have hK : ((m / 100 : ℕ) : ℝ) ≤ (m : ℝ) / 100 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (m / 100) * 100 ≤ m := Nat.div_mul_le_self m 100
    exact_mod_cast this
  have hNR : (N : ℝ) ≤ 0.6 * m := by
    have : ((5 * N : ℕ) : ℝ) ≤ ((3 * m : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at this
    linarith
  have h64 : (64 : ℝ) ^ (m / 100) ≤ Real.exp (4.2 * (m / 100 : ℕ)) := by
    rw [show (64 : ℝ) ^ (m / 100) = 2 ^ (6 * (m / 100)) by rw [pow_mul]; norm_num, two_pow_eq_exp]
    apply Real.exp_le_exp.2
    push_cast
    have : (0 : ℝ) ≤ ((m / 100 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h65 : ((65 : ℝ) / 64) ^ N ≤ Real.exp (N / 64) := by
    rw [show (N : ℝ) / 64 = N * (1 / 64) by ring, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by norm_num)
    have := Real.add_one_le_exp ((1 : ℝ) / 64)
    linarith
  have h2r : (1 : ℝ) / 2 ^ r ≤ Real.exp (-(0.69 * 0.13 * m)) := by
    rw [two_pow_eq_exp, one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.2
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    nlinarith
  calc (64 : ℝ) ^ (m / 100) * (65 / 64) ^ N * (1 / 2 ^ r)
      ≤ Real.exp (4.2 * (m / 100 : ℕ)) * Real.exp (N / 64) * Real.exp (-(0.69 * 0.13 * m)) := by
        gcongr
    _ = Real.exp (4.2 * (m / 100 : ℕ) + N / 64 - 0.69 * 0.13 * m) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(m : ℝ) / 30) := by
        apply Real.exp_le_exp.2
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        linarith

theorem lem_pencilsupp_supp {ω : Pairs m → Bool} (hω : GoodPS m ω) (hp23 : 23 ≤ p)
    (hpX : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) {b0 b1 : ZMod p}
    (hQ : IsUnit (QAm b0 b1 (modP p (seidelOf ω))).det) :
    prob (fun x : SignPair m => 2 * m ≤ 5 * (suppU x).card ∧ 5 * (suppU x).card ≤ 3 * m ∧
      ∃ a0 a1 : ZMod p, (a0 ≠ 0 ∨ a1 ≠ 0) ∧
        100 * (univ.filter fun j => uPair p x j = 0 ∧
          ((PAm a0 a1 (modP p (seidelOf ω)) * (QAm b0 b1 (modP p (seidelOf ω)))⁻¹) *ᵥ uPair p x) j ≠ 0).card
          < m) ≤
      (p : ℝ) ^ 2 * Real.exp (-(m : ℝ) / 30) := by
  classical
  have hp2 : p ≠ 2 := by omega
  set A := modP p (seidelOf ω) with hA
  set Cm : ZMod p → ZMod p → Matrix (Fin m) (Fin m) (ZMod p) := fun a0 a1 => PAm a0 a1 A * (QAm b0 b1 A)⁻¹
    with hCm
  set c : ℝ := Real.exp (-(m : ℝ) / 30) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  rw [← prob_equiv pairDiffEquiv.symm]
  refine prob_le_of_forall_snd (fun d => ?_) (by positivity)
  set U := univ.filter fun j => d j = true with hU
  have hev : ∀ ξ : Fin m → Bool,
      (2 * m ≤ 5 * (suppU (pairDiffEquiv.symm (ξ, d))).card ∧
        5 * (suppU (pairDiffEquiv.symm (ξ, d))).card ≤ 3 * m ∧
        ∃ a0 a1 : ZMod p, (a0 ≠ 0 ∨ a1 ≠ 0) ∧
          100 * (univ.filter fun j => uPair p (pairDiffEquiv.symm (ξ, d)) j = 0 ∧
            (Cm a0 a1 *ᵥ uPair p (pairDiffEquiv.symm (ξ, d))) j ≠ 0).card < m) →
      (2 * m ≤ 5 * U.card ∧ 5 * U.card ≤ 3 * m) ∧
        ∃ a : ZMod p × ZMod p, (a.1 ≠ 0 ∨ a.2 ≠ 0) ∧
          100 * (Uᶜ.filter fun j => (Cm a.1 a.2 *ᵥ uOn p U ξ) j ≠ 0).card < m := by
    intro ξ ⟨h1, h2, a0, a1, ha, h3⟩
    rw [suppU_pairDiff] at h1 h2
    refine ⟨⟨h1, h2⟩, (a0, a1), ha, ?_⟩
    have e : (univ.filter fun j => uPair p (pairDiffEquiv.symm (ξ, d)) j = 0 ∧
        (Cm a0 a1 *ᵥ uPair p (pairDiffEquiv.symm (ξ, d))) j ≠ 0) =
        Uᶜ.filter fun j => (Cm a0 a1 *ᵥ uOn p U ξ) j ≠ 0 := by
      ext j
      rw [mem_filter, mem_filter, uPair_eq_zero_iff_not_mem, suppU_pairDiff, uPair_pairDiff, mem_compl]
      simp only [mem_univ, true_and]
      exact Iff.rfl
    rw [e] at h3
    exact h3
  refine le_trans (prob_mono hev) ?_
  by_cases hUc : 2 * m ≤ 5 * U.card ∧ 5 * U.card ≤ 3 * m
  ·
    have hbound : ∀ a : ZMod p × ZMod p, prob (fun ξ : Fin m → Bool => (a.1 ≠ 0 ∨ a.2 ≠ 0) ∧
        100 * (Uᶜ.filter fun j => (Cm a.1 a.2 *ᵥ uOn p U ξ) j ≠ 0).card < m) ≤ c := by
      rintro ⟨a0, a1⟩
      by_cases ha : a0 ≠ 0 ∨ a1 ≠ 0
      · set Sset := Uᶜ.powerset.filter fun S => 100 * S.card < m with hSset
        have hsub : ∀ ξ : Fin m → Bool, ((a0, a1).1 ≠ 0 ∨ (a0, a1).2 ≠ 0) ∧
            100 * (Uᶜ.filter fun j => (Cm (a0, a1).1 (a0, a1).2 *ᵥ uOn p U ξ) j ≠ 0).card < m →
            ∃ S ∈ Sset, ∀ j ∈ Uᶜ \ S, (Cm a0 a1 *ᵥ uOn p U ξ) j = 0 := by
          intro ξ ⟨_, hlt⟩
          refine ⟨Uᶜ.filter fun j => (Cm a0 a1 *ᵥ uOn p U ξ) j ≠ 0, ?_, ?_⟩
          · rw [hSset, mem_filter, mem_powerset]
            exact ⟨filter_subset _ _, hlt⟩
          · intro j hj
            rw [mem_sdiff, mem_filter] at hj
            by_contra h0
            exact hj.2 ⟨hj.1, h0⟩
        have hS : ∀ S ∈ Sset, prob (fun ξ : Fin m → Bool => ∀ j ∈ Uᶜ \ S, (Cm a0 a1 *ᵥ uOn p U ξ) j = 0) ≤
            1 / 2 ^ (diagSet (Uᶜ \ S) * Cm a0 a1 * diagSet U).rank :=
          fun S _ => prob_CuR_zero_le hp2 _ U _
        have hrank : ∀ S ∈ Sset, 0.13 * (m : ℝ) ≤ (diagSet (Uᶜ \ S) * Cm a0 a1 * diagSet U).rank := by
          intro S hSmem
          rw [hSset, mem_filter, mem_powerset] at hSmem
          have hSU : Uᶜ \ (Uᶜ \ S) = S := Finset.sdiff_sdiff_eq_self hSmem.1
          have hadm : AdmUR U (Uᶜ \ S) := by
            refine ⟨hUc.1, hUc.2, ?_, ?_⟩
            · exact Finset.disjoint_left.2 fun j hj hjU => (mem_compl.1 (mem_sdiff.1 hj).1) hjU
            · rw [hSU]
              exact hSmem.2.le
          exact rank_CRU_of_goodPS hω hp23 hpX hadm ha hQ
        have hNc : 5 * Uᶜ.card ≤ 3 * m := by
          have := Finset.card_add_card_compl U
          simp only [Fintype.card_fin] at this
          omega
        calc prob (fun ξ : Fin m → Bool => ((a0, a1).1 ≠ 0 ∨ (a0, a1).2 ≠ 0) ∧
              100 * (Uᶜ.filter fun j => (Cm (a0, a1).1 (a0, a1).2 *ᵥ uOn p U ξ) j ≠ 0).card < m)
            ≤ prob (fun ξ : Fin m → Bool => ∃ S ∈ Sset, ∀ j ∈ Uᶜ \ S, (Cm a0 a1 *ᵥ uOn p U ξ) j = 0) :=
              prob_mono hsub
          _ ≤ ∑ S ∈ Sset, prob (fun ξ : Fin m → Bool => ∀ j ∈ Uᶜ \ S, (Cm a0 a1 *ᵥ uOn p U ξ) j = 0) :=
              prob_exists_le_sum _ _
          _ ≤ ∑ S ∈ Sset, (64 : ℝ) ^ (m / 100) * (65 / 64) ^ Uᶜ.card *
                (1 / 2 ^ (diagSet (Uᶜ \ S) * Cm a0 a1 * diagSet U).rank) /
                ((64 : ℝ) ^ (m / 100) * (65 / 64) ^ Uᶜ.card) := by
              refine sum_le_sum fun S hSmem => (hS S hSmem).trans (le_of_eq ?_)
              field_simp
          _ ≤ ∑ _S ∈ Sset, c / ((64 : ℝ) ^ (m / 100) * (65 / 64) ^ Uᶜ.card) := by
              refine sum_le_sum fun S hSmem => ?_
              gcongr
              exact supp_numeric hNc (hrank S hSmem)
          _ = (Sset.card : ℝ) * (c / ((64 : ℝ) ^ (m / 100) * (65 / 64) ^ Uᶜ.card)) := by
              rw [sum_const, nsmul_eq_mul]
          _ ≤ ((64 : ℝ) ^ (m / 100) * (65 / 64) ^ Uᶜ.card) *
                (c / ((64 : ℝ) ^ (m / 100) * (65 / 64) ^ Uᶜ.card)) := by
              gcongr
              exact card_small_subsets_le Uᶜ
          _ = c := by field_simp
      · rw [prob_congr (Q := fun _ => False) fun ξ => ⟨fun h => ha h.1, False.elim⟩, prob_false]
        exact hc0
    calc prob (fun ξ : Fin m → Bool => (2 * m ≤ 5 * U.card ∧ 5 * U.card ≤ 3 * m) ∧
          ∃ a : ZMod p × ZMod p, (a.1 ≠ 0 ∨ a.2 ≠ 0) ∧
            100 * (Uᶜ.filter fun j => (Cm a.1 a.2 *ᵥ uOn p U ξ) j ≠ 0).card < m)
        ≤ prob (fun ξ : Fin m → Bool => ∃ a : ZMod p × ZMod p, (a.1 ≠ 0 ∨ a.2 ≠ 0) ∧
            100 * (Uᶜ.filter fun j => (Cm a.1 a.2 *ᵥ uOn p U ξ) j ≠ 0).card < m) :=
          prob_mono fun ξ h => h.2
      _ ≤ ∑ a : ZMod p × ZMod p, prob (fun ξ : Fin m → Bool => (a.1 ≠ 0 ∨ a.2 ≠ 0) ∧
            100 * (Uᶜ.filter fun j => (Cm a.1 a.2 *ᵥ uOn p U ξ) j ≠ 0).card < m) :=
          prob_exists_le_sum_fintype _
      _ ≤ ∑ _a : ZMod p × ZMod p, c := sum_le_sum fun a _ => hbound a
      _ = (p : ℝ) ^ 2 * c := by
          rw [sum_const, card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
          push_cast
          ring
  · rw [prob_congr (Q := fun _ => False) fun ξ => ⟨fun h => hUc h.1, False.elim⟩, prob_false]
    positivity

end DGS
