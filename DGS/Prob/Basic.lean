module

public import DGS.External
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open Filter Topology

namespace DGS

theorem finset_sum_div {ι : Type*} (s : Finset ι) (f : ι → ℝ) (a : ℝ) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

section Prob

variable {Ω Ω' : Type*}

theorem probG_eq_prob (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : probG n P = prob P := rfl

variable [Finite Ω]

omit [Finite Ω] in
theorem prob_nonneg (P : Ω → Prop) : 0 ≤ prob P := by
  unfold prob
  positivity

theorem prob_le_one (P : Ω → Prop) : prob P ≤ 1 := by
  unfold prob
  rcases Nat.eq_zero_or_pos (Nat.card Ω) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finite.card_subtype_le P

theorem prob_mono {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) : prob P ≤ prob Q := by
  unfold prob
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast Nat.card_le_card_of_injective
    (fun x : {ω // P ω} => (⟨x.1, h x.1 x.2⟩ : {ω // Q ω}))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))

omit [Finite Ω] in
theorem prob_congr {P Q : Ω → Prop} (h : ∀ ω, P ω ↔ Q ω) : prob P = prob Q := by
  have : P = Q := funext fun ω => propext (h ω)
  rw [this]

omit [Finite Ω] in
theorem prob_false : prob (fun _ : Ω => False) = 0 := by
  have : IsEmpty {_ω : Ω // False} := ⟨fun x => x.2⟩
  have h : Nat.card {_ω : Ω // False} = 0 := Nat.card_of_isEmpty
  show (Nat.card {_ω : Ω // False} : ℝ) / Nat.card Ω = 0
  rw [h, Nat.cast_zero, zero_div]

theorem prob_true [Nonempty Ω] : prob (fun _ : Ω => True) = 1 := by
  have h1 : Nat.card {_ω : Ω // True} = Nat.card Ω :=
    Nat.card_congr (Equiv.subtypeUnivEquiv (p := fun _ : Ω => True) fun _ => trivial)
  have hpos : (0 : ℝ) < Nat.card Ω := by exact_mod_cast Nat.card_pos (α := Ω)
  show (Nat.card {_ω : Ω // True} : ℝ) / Nat.card Ω = 1
  rw [h1]
  exact div_self hpos.ne'

theorem card_subtype_add_card_subtype_not (P : Ω → Prop) :
    Nat.card {ω // P ω} + Nat.card {ω // ¬ P ω} = Nat.card Ω := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl P)

theorem prob_compl [Nonempty Ω] (P : Ω → Prop) : prob (fun ω => ¬ P ω) = 1 - prob P := by
  have h := card_subtype_add_card_subtype_not P
  have h' : Nat.card {ω // ¬ P ω} + Nat.card {ω // P ω} = Nat.card Ω := by omega
  have hpos : (0 : ℝ) < Nat.card Ω := by exact_mod_cast Nat.card_pos (α := Ω)
  rw [eq_sub_iff_add_eq]
  unfold prob
  rw [← add_div, div_eq_one_iff_eq hpos.ne']
  exact_mod_cast h'

omit [Finite Ω] in
theorem prob_or_le (P Q : Ω → Prop) : prob (fun ω => P ω ∨ Q ω) ≤ prob P + prob Q := by
  have h : Nat.card {ω // P ω ∨ Q ω} ≤ Nat.card {ω // P ω} + Nat.card {ω // Q ω} :=
    Set.card_union_le {ω | P ω} {ω | Q ω}
  unfold prob
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast h

omit [Finite Ω] in
theorem prob_exists_le_sum {ι : Type*} (s : Finset ι) (P : ι → Ω → Prop) :
    prob (fun ω => ∃ i ∈ s, P i ω) ≤ ∑ i ∈ s, prob (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : prob (fun ω => ∃ i ∈ (∅ : Finset ι), P i ω) = prob (fun _ : Ω => False) :=
      prob_congr fun ω => by simp
    simp only [h, prob_false, Finset.sum_empty, le_refl]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h : prob (fun ω => ∃ i ∈ insert a s, P i ω) =
        prob (fun ω => P a ω ∨ ∃ i ∈ s, P i ω) :=
      prob_congr fun ω => Finset.exists_mem_insert a s (fun i => P i ω)
    exact (h.trans_le (prob_or_le _ _)).trans (add_le_add le_rfl ih)

omit [Finite Ω] in
theorem prob_exists_le_sum_fintype {ι : Type*} [Fintype ι] (P : ι → Ω → Prop) :
    prob (fun ω => ∃ i, P i ω) ≤ ∑ i, prob (P i) := by
  have h : prob (fun ω => ∃ i, P i ω) = prob (fun ω => ∃ i ∈ (Finset.univ : Finset ι), P i ω) :=
    prob_congr fun ω => by simp
  rw [h]
  exact prob_exists_le_sum _ _

omit [Finite Ω] in
theorem prob_equiv [Finite Ω'] (e : Ω ≃ Ω') (P : Ω' → Prop) : prob (fun ω => P (e ω)) = prob P := by
  have h1 : Nat.card {ω // P (e ω)} = Nat.card {ω' // P ω'} :=
    Nat.card_congr (e.subtypeEquivOfSubtype (p := P))
  unfold prob
  rw [h1, Nat.card_congr e]

omit [Finite Ω] in
theorem prob_fst [Finite Ω'] [Nonempty Ω'] (P : Ω → Prop) :
    prob (fun x : Ω × Ω' => P x.1) = prob P := by
  have h1 : Nat.card {x : Ω × Ω' // P x.1} = Nat.card ({ω // P ω} × Ω') :=
    Nat.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd (p := P))
  have hpos : (0 : ℝ) < Nat.card Ω' := by exact_mod_cast Nat.card_pos (α := Ω')
  unfold prob
  rw [h1, Nat.card_prod, Nat.card_prod, Nat.cast_mul, Nat.cast_mul, mul_div_mul_right _ _ hpos.ne']

theorem prob_snd [Finite Ω'] [Nonempty Ω] (P : Ω' → Prop) :
    prob (fun x : Ω × Ω' => P x.2) = prob P :=
  (prob_equiv (Equiv.prodComm Ω Ω') (fun y : Ω' × Ω => P y.1)).trans (prob_fst P)

omit [Finite Ω] in
theorem prob_prod_eq_avg [Fintype Ω] [Finite Ω'] (P : Ω × Ω' → Prop) :
    prob P = (∑ ω, prob (fun ω' => P (ω, ω'))) / Fintype.card Ω := by
  have h1 : Nat.card {x : Ω × Ω' // P x} = ∑ ω, Nat.card {ω' : Ω' // P (ω, ω')} :=
    (Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b => P (a, b))).trans Nat.card_sigma
  unfold prob
  rw [h1, Nat.card_prod, Nat.card_eq_fintype_card (α := Ω), Nat.cast_sum, Nat.cast_mul,
    mul_comm (Fintype.card Ω : ℝ), ← div_div, finset_sum_div]

theorem prob_le_of_forall_fst [Finite Ω'] {P : Ω × Ω' → Prop} {c : ℝ}
    (h : ∀ ω, prob (fun ω' => P (ω, ω')) ≤ c) (hc : 0 ≤ c) : prob P ≤ c := by
  have := Fintype.ofFinite Ω
  rw [prob_prod_eq_avg P]
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]
    exact hc
  · have hpos' : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hpos
    rw [div_le_iff₀ hpos']
    calc ∑ ω, prob (fun ω' => P (ω, ω')) ≤ ∑ _ω : Ω, c := Finset.sum_le_sum fun ω _ => h ω
      _ = c * Fintype.card Ω := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

theorem prob_le_of_forall_snd [Finite Ω'] {P : Ω × Ω' → Prop} {c : ℝ}
    (h : ∀ ω', prob (fun ω => P (ω, ω')) ≤ c) (hc : 0 ≤ c) : prob P ≤ c := by
  rw [← prob_equiv (Equiv.prodComm Ω' Ω) P]
  exact prob_le_of_forall_fst (fun ω' => by simpa using h ω') hc

omit [Finite Ω] in
theorem prob_and_indep [Finite Ω'] (P : Ω → Prop) (Q : Ω' → Prop) :
    prob (fun x : Ω × Ω' => P x.1 ∧ Q x.2) = prob P * prob Q := by
  have h1 : Nat.card {x : Ω × Ω' // P x.1 ∧ Q x.2} = Nat.card ({ω // P ω} × {ω' // Q ω'}) :=
    Nat.card_congr (Equiv.subtypeProdEquivProd (p := P) (q := Q))
  unfold prob
  rw [h1, Nat.card_prod, Nat.card_prod, Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]

end Prob

section Expect

variable {Ω : Type*} [Fintype Ω]

noncomputable def expect (X : Ω → ℝ) : ℝ := (∑ ω, X ω) / Fintype.card Ω

theorem expect_indicator (P : Ω → Prop) [DecidablePred P] :
    expect (fun ω => if P ω then (1 : ℝ) else 0) = prob P := by
  have h1 : Nat.card {ω // P ω} = (Finset.univ.filter P).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold expect prob
  rw [Finset.sum_boole, h1, Nat.card_eq_fintype_card (α := Ω)]

theorem prob_ge_le_expect_div (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) {a : ℝ} (ha : 0 < a) :
    prob (fun ω => a ≤ X ω) ≤ expect X / a := by
  classical
  rw [← expect_indicator]
  unfold expect
  rw [div_right_comm, finset_sum_div Finset.univ X a]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => ?_) (Nat.cast_nonneg _)
  split_ifs with h
  · rw [le_div_iff₀ ha, one_mul]
    exact h
  · exact div_nonneg (hX ω) ha.le

theorem expect_congr {X Y : Ω → ℝ} (h : ∀ ω, X ω = Y ω) : expect X = expect Y := by
  rw [show X = Y from funext h]

theorem expect_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : expect X ≤ expect Y := by
  unfold expect
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω) (Nat.cast_nonneg _)

theorem expect_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ expect X := by
  unfold expect
  exact div_nonneg (Finset.sum_nonneg fun ω _ => h ω) (Nat.cast_nonneg _)

theorem expect_const [Nonempty Ω] (c : ℝ) : expect (fun _ : Ω => c) = c := by
  unfold expect
  have h : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ h]

theorem expect_add (X Y : Ω → ℝ) : expect (fun ω => X ω + Y ω) = expect X + expect Y := by
  unfold expect
  rw [Finset.sum_add_distrib, add_div]

theorem expect_const_mul (c : ℝ) (X : Ω → ℝ) : expect (fun ω => c * X ω) = c * expect X := by
  unfold expect
  rw [← Finset.mul_sum, mul_div_assoc]

theorem expect_sum {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ) :
    expect (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, expect (X i) := by
  unfold expect
  rw [Finset.sum_comm, finset_sum_div]

theorem expect_equiv {Ω' : Type*} [Fintype Ω'] (e : Ω ≃ Ω') (X : Ω' → ℝ) :
    expect (fun ω => X (e ω)) = expect X := by
  unfold expect
  rw [Fintype.card_congr e, Equiv.sum_comp e X]

theorem expect_prod {Ω' : Type*} [Fintype Ω'] (X : Ω × Ω' → ℝ) :
    expect X = expect (fun ω => expect (fun ω' => X (ω, ω'))) := by
  unfold expect
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← finset_sum_div, div_div, mul_comm]

theorem expect_indicator' (P : Ω → Prop) :
    expect (fun ω => @ite ℝ (P ω) (Classical.dec _) 1 0) = prob P := by
  classical
  convert expect_indicator P

end Expect

section Limits

variable {Ω : ℕ → Type*} [∀ n, Finite (Ω n)]

theorem tendsto_prob_one_of_compl [∀ n, Nonempty (Ω n)] {P : ∀ n, Ω n → Prop}
    (h : Tendsto (fun n => prob (fun ω => ¬ P n ω)) atTop (𝓝 0)) :
    Tendsto (fun n => prob (P n)) atTop (𝓝 1) := by
  have : (fun n => prob (P n)) = fun n => 1 - prob (fun ω => ¬ P n ω) := by
    funext n
    rw [prob_compl]
    ring
  rw [this]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

omit [∀ n, Finite (Ω n)] in
theorem tendsto_prob_zero_of_le {P : ∀ n, Ω n → Prop} {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, prob (P n) ≤ u n) :
    Tendsto (fun n => prob (P n)) atTop (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall fun _ => prob_nonneg _) h hu

end Limits

end DGS
