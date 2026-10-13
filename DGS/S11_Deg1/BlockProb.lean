module

public import DGS.S10_Tools.Chains

@[expose] public section

open Finset

namespace DGS

section Pexp

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]

noncomputable def pexp (ν : ι → G → ℝ) (F : (ι → G) → ℝ) : ℝ :=
  ∑ y, (∏ i, ν i (y i)) * F y

omit [DecidableEq G] in
theorem pmeas_eq_pexp (ν : ι → G → ℝ) (B : (ι → G) → Prop) [DecidablePred B] :
    pmeas ν B = pexp ν (fun y => if B y then 1 else 0) := by
  unfold pmeas pexp
  refine sum_congr rfl fun y _ => ?_
  by_cases hb : B y <;> simp [hb]

omit [DecidableEq G] in
theorem pexp_mono (ν : ι → G → ℝ) (hν0 : ∀ i a, 0 ≤ ν i a) {F F' : (ι → G) → ℝ}
    (h : ∀ y, F y ≤ F' y) : pexp ν F ≤ pexp ν F' := by
  unfold pexp
  exact sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (prod_nonneg fun i _ => hν0 i _)

omit [DecidableEq G] in
theorem pexp_nonneg (ν : ι → G → ℝ) (hν0 : ∀ i a, 0 ≤ ν i a) {F : (ι → G) → ℝ}
    (h : ∀ y, 0 ≤ F y) : 0 ≤ pexp ν F := by
  unfold pexp
  exact sum_nonneg fun y _ => mul_nonneg (prod_nonneg fun i _ => hν0 i _) (h y)

omit [DecidableEq G] in
theorem pexp_add (ν : ι → G → ℝ) (F F' : (ι → G) → ℝ) :
    pexp ν (fun y => F y + F' y) = pexp ν F + pexp ν F' := by
  unfold pexp
  rw [← sum_add_distrib]
  exact sum_congr rfl fun y _ => mul_add _ _ _

omit [DecidableEq G] in
theorem pexp_const_mul (ν : ι → G → ℝ) (c : ℝ) (F : (ι → G) → ℝ) :
    pexp ν (fun y => c * F y) = c * pexp ν F := by
  unfold pexp
  rw [mul_sum]
  exact sum_congr rfl fun y _ => by ring

omit [DecidableEq G] in
theorem pexp_sum {κ : Type*} (ν : ι → G → ℝ) (s : Finset κ) (F : κ → (ι → G) → ℝ) :
    pexp ν (fun y => ∑ a ∈ s, F a y) = ∑ a ∈ s, pexp ν (F a) := by
  unfold pexp
  simp_rw [mul_sum]
  exact sum_comm

omit [DecidableEq G] in
theorem pexp_const (ν : ι → G → ℝ) (hν1 : ∀ i, ∑ a, ν i a = 1) (c : ℝ) :
    pexp ν (fun _ => c) = c := by
  unfold pexp
  rw [← sum_mul, sum_prod_prob ν hν1, one_mul]

end Pexp

theorem exists_blocks {ι : Type*} [DecidableEq ι] (D : Finset ι) (k : ℕ) :
    ∀ h : ℕ, h * k ≤ D.card → ∃ B : Fin h → Finset ι, (∀ i, B i ⊆ D) ∧ (∀ i, (B i).card = k) ∧
      Pairwise fun i i' => Disjoint (B i) (B i')
  | 0, _ => ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | h + 1, hD => by
    obtain ⟨B0, hB0D, hB0⟩ := exists_subset_card_eq (s := D) (n := k) (by nlinarith)
    have hD' : h * k ≤ (D \ B0).card := by
      rw [card_sdiff_of_subset hB0D, hB0]
      have : (h + 1) * k = h * k + k := by ring
      omega
    obtain ⟨B', hB'D, hB'card, hB'disj⟩ := exists_blocks (D \ B0) k h hD'
    refine ⟨Fin.cons B0 B', fun i => ?_, fun i => ?_, fun i i' hii' => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact hB0D
      · exact (hB'D i).trans sdiff_subset
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact hB0
      · exact hB'card i
    · have hdisj0 : ∀ j, Disjoint B0 (B' j) := fun j =>
        disjoint_of_subset_right (hB'D j) disjoint_sdiff
      induction i using Fin.cases with
      | zero =>
        induction i' using Fin.cases with
        | zero => exact absurd rfl hii'
        | succ j => simpa using hdisj0 j
      | succ j =>
        induction i' using Fin.cases with
        | zero => simpa using (hdisj0 j).symm
        | succ j' =>
          simp only [Fin.cons_succ]
          exact hB'disj fun h => hii' (by rw [h])

theorem pexp_blocks {ι G : Type*} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G] {h : ℕ}
    (ν : ι → G → ℝ) (hν1 : ∀ j, ∑ a, ν j a = 1) (B : Fin h → Finset ι)
    (hB : Pairwise fun i i' => Disjoint (B i) (B i')) (F : ∀ i, (B i → G) → ℝ) :
    pexp ν (fun y => ∏ i, F i (fun j : B i => y j)) = ∏ i, pexp (fun j : B i => ν j) (F i) := by
  classical
  set U := univ.biUnion B with hU
  have hsplit : ∀ y : ι → G, ∏ j, ν j (y j) =
      (∏ i, ∏ j : B i, ν j (y j)) * ∏ j : {j // j ∉ U}, ν j (y j) := by
    intro y
    rw [← prod_mul_prod_compl U, prod_biUnion (fun i _ i' _ hii' => hB hii')]
    congr 1
    · exact prod_congr rfl fun i _ => (prod_coe_sort (B i) _).symm
    · exact prod_subtype Uᶜ (fun j => by simp) _
  let φ : (ι → G) → (∀ i, B i → G) × ({j // j ∉ U} → G) := fun y => (fun i j => y j, fun j => y j)
  have hφ : Function.Bijective φ := by
    refine (Fintype.bijective_iff_injective_and_card φ).2 ⟨?_, ?_⟩
    · intro y y' hyy'
      funext j
      by_cases hj : j ∈ U
      · obtain ⟨i, -, hji⟩ := mem_biUnion.1 hj
        exact congrFun (congrFun (congrArg Prod.fst hyy') i) ⟨j, hji⟩
      · exact congrFun (congrArg Prod.snd hyy') ⟨j, hj⟩
    · have hU_card : ∑ i, (B i).card = U.card :=
        (card_biUnion (fun i _ i' _ hii' => hB hii')).symm
      have hcompl : Fintype.card {j // j ∉ U} = Fintype.card ι - U.card := by
        rw [Fintype.card_subtype_compl, Fintype.card_coe]
      have hUle : U.card ≤ Fintype.card ι := card_le_univ U
      have e1 : Fintype.card (ι → G) = Fintype.card G ^ Fintype.card ι := Fintype.card_fun
      have e2 : Fintype.card ((∀ i, B i → G) × ({j // j ∉ U} → G)) =
          (∏ i, Fintype.card G ^ (B i).card) * Fintype.card G ^ (Fintype.card ι - U.card) := by
        rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_fun, hcompl]
        congr 1
        refine prod_congr rfl fun i _ => ?_
        rw [Fintype.card_fun, Fintype.card_coe]
      rw [e1, e2, prod_pow_eq_pow_sum, hU_card, ← pow_add, Nat.add_sub_cancel' hUle]
  calc pexp ν (fun y => ∏ i, F i (fun j : B i => y j))
      = ∑ y : ι → G, (∏ i, (∏ j : B i, ν j (y j)) * F i (fun j : B i => y j)) *
          ∏ j : {j // j ∉ U}, ν j (y j) := by
        unfold pexp
        refine sum_congr rfl fun y _ => ?_
        rw [hsplit, prod_mul_distrib]
        ring
    _ = ∑ x : (∀ i, B i → G) × ({j // j ∉ U} → G),
          (∏ i, (∏ j : B i, ν j (x.1 i j)) * F i (x.1 i)) * ∏ j : {j // j ∉ U}, ν j (x.2 j) :=
        Fintype.sum_bijective φ hφ _ _ fun y => rfl
    _ = (∑ x1 : ∀ i, B i → G, ∏ i, (∏ j : B i, ν j (x1 i j)) * F i (x1 i)) *
          ∑ x2 : {j // j ∉ U} → G, ∏ j : {j // j ∉ U}, ν j (x2 j) := by
        rw [Fintype.sum_prod_type, sum_mul_sum]
    _ = ∏ i, pexp (fun j : B i => ν j) (F i) := by
        rw [sum_prod_prob (fun j : {j // j ∉ U} => ν j) (fun j => hν1 j), mul_one,
          ← Fintype.prod_sum (fun i (x : B i → G) => (∏ j : B i, ν j (x j)) * F i x)]
        simp only [pexp]

theorem pow_le_levels {ρ r0 : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hr0 : 0 < r0) (N A : ℕ)
    (hA : 1 < 2 ^ A * r0) :
    ρ ^ N ≤ r0 ^ N + ∑ a ∈ range A, (2 * (2 ^ a * r0)) ^ N * (if 2 ^ a * r0 ≤ ρ then 1 else 0) := by
  classical
  have hnn : ∀ a ∈ range A, 0 ≤ (2 * (2 ^ a * r0)) ^ N * (if 2 ^ a * r0 ≤ ρ then (1 : ℝ) else 0) :=
    fun a _ => mul_nonneg (by positivity) (by split_ifs <;> norm_num)
  by_cases hlow : ρ < r0
  · have : ρ ^ N ≤ r0 ^ N := pow_le_pow_left₀ hρ0 hlow.le N
    linarith [sum_nonneg hnn]
  · push Not at hlow
    have hex : ∃ a, ρ < 2 ^ (a + 1) * r0 := ⟨A, by
      have : (2 : ℝ) ^ A * r0 ≤ 2 ^ (A + 1) * r0 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ A)) hr0.le
      linarith⟩
    set a0 := Nat.find hex with ha0
    have h1 : ρ < 2 ^ (a0 + 1) * r0 := Nat.find_spec hex
    have h2 : 2 ^ a0 * r0 ≤ ρ := by
      rcases Nat.eq_zero_or_pos a0 with h0 | h0
      · rw [h0, pow_zero, one_mul]
        exact hlow
      · have := Nat.find_min hex (show a0 - 1 < a0 by omega)
        push Not at this
        rwa [show a0 - 1 + 1 = a0 by omega] at this
    have ha0A : a0 ∈ range A := by
      rw [mem_range]
      by_contra hcon
      push Not at hcon
      have : (2 : ℝ) ^ A * r0 ≤ 2 ^ a0 * r0 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcon) hr0.le
      linarith
    have hterm := single_le_sum hnn ha0A
    rw [ite_eq_left h2, mul_one] at hterm
    have : ρ ^ N ≤ (2 * (2 ^ a0 * r0)) ^ N := by
      apply pow_le_pow_left₀ hρ0
      calc ρ ≤ 2 ^ (a0 + 1) * r0 := h1.le
        _ = 2 * (2 ^ a0 * r0) := by ring
    linarith [pow_nonneg hr0.le N]

theorem pexp_pow_le_levels {ι G : Type*} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    (ν : ι → G → ℝ)
    (hν0 : ∀ i a, 0 ≤ ν i a) (hν1 : ∀ i, ∑ a, ν i a = 1) (ρ : (ι → G) → ℝ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∀ y, ρ y ≤ 1) {r0 : ℝ} (hr0 : 0 < r0) (N A : ℕ) (hA : 1 < 2 ^ A * r0) :
    pexp ν (fun y => ρ y ^ N) ≤ r0 ^ N + ∑ a ∈ range A, (2 * (2 ^ a * r0)) ^ N *
      pexp ν (fun y => if 2 ^ a * r0 ≤ ρ y then 1 else 0) := by
  classical
  refine (pexp_mono ν hν0 fun y => pow_le_levels (hρ0 y) (hρ1 y) hr0 N A hA).trans (le_of_eq ?_)
  rw [pexp_add, pexp_const ν hν1, pexp_sum]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  rw [pexp_const_mul]

end DGS
