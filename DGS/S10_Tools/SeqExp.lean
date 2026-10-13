module

public import DGS.S10_Tools.Signs

@[expose] public section

open Finset

namespace DGS

section Aux

variable {Ω Ω' : Type*}

theorem prob_and_le_mul [Fintype Ω] [Fintype Ω'] (A : Ω → Prop) (B : Ω → Ω' → Prop) {c : ℝ}
    (_hc : 0 ≤ c) (h : ∀ ω, prob (B ω) ≤ c) :
    prob (fun x : Ω × Ω' => A x.1 ∧ B x.1 x.2) ≤ prob A * c := by
  classical
  rw [prob_prod_eq_avg]
  have hA : prob A = (∑ ω, if A ω then (1 : ℝ) else 0) / Fintype.card Ω := by
    rw [← expect_indicator]
    rfl
  rw [hA, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hω : A ω
  · rw [ite_eq_left hω, one_mul]
    exact (prob_congr fun ω' => by simp [hω]).trans_le (h ω)
  · rw [ite_eq_right hω, zero_mul]
    exact (prob_congr (Q := fun _ => False) fun ω' => by simp [hω]).trans_le (by rw [prob_false])

end Aux

variable {G : Type*} [AddCommGroup G]

def pairsSplit (m : ℕ) : (Pairs (m + 1) → Bool) ≃ (Fin m → Bool) × (Pairs m → Bool) where
  toFun ω := (fun j => ω ⟨(0, j.succ), Fin.succ_pos j⟩,
    fun q => ω ⟨(q.1.1.succ, q.1.2.succ), Fin.succ_lt_succ_iff.2 q.2⟩)
  invFun x q :=
    if h : q.1.1 = 0 then x.1 (q.1.2.pred (Fin.ne_zero_of_lt q.2))
    else x.2 ⟨(q.1.1.pred h, q.1.2.pred (Fin.ne_zero_of_lt q.2)), by
      show q.1.1.pred h < q.1.2.pred (Fin.ne_zero_of_lt q.2)
      exact Fin.pred_lt_pred_iff.2 q.2⟩
  left_inv ω := by
    funext q
    obtain ⟨⟨a, b⟩, hab⟩ := q
    by_cases h : a = 0
    · subst h
      simp only [↓reduceDIte]
      congr 2
      simp
    · simp only [h, dite_false]
      congr 2
      simp
  right_inv x := by
    obtain ⟨r, ω'⟩ := x
    refine Prod.ext ?_ ?_
    · funext j
      simp
    · funext q
      simp only [Fin.succ_ne_zero, dite_false, Fin.pred_succ]

variable {m : ℕ}

theorem seidelOf_split_zero_succ (ω : Pairs (m + 1) → Bool) (j : Fin m) :
    seidelOf ω 0 j.succ = sgnZ ((pairsSplit m ω).1 j) := by
  rw [seidelOf, symOf_apply_lt _ _ _ (Fin.succ_pos j)]
  rfl

theorem seidelOf_split_succ_zero (ω : Pairs (m + 1) → Bool) (i : Fin m) :
    seidelOf ω i.succ 0 = sgnZ ((pairsSplit m ω).1 i) := by
  rw [seidelOf, symOf_comm, ← seidelOf, seidelOf_split_zero_succ]

theorem seidelOf_split_succ_succ (ω : Pairs (m + 1) → Bool) (i j : Fin m) :
    seidelOf ω i.succ j.succ = seidelOf (pairsSplit m ω).2 i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [seidelOf, seidelOf, symOf_apply_lt _ _ _ (Fin.succ_lt_succ_iff.2 h),
      symOf_apply_lt _ _ _ h]
    rfl
  · simp [seidelOf]
  · rw [seidelOf, seidelOf, symOf_apply_gt _ _ _ (Fin.succ_lt_succ_iff.2 h),
      symOf_apply_gt _ _ _ h]
    rfl

def zeroSuffixEquiv (m : ℕ) : Fin m ≃ {j : Fin (m + 1) // 0 < j} where
  toFun j := ⟨j.succ, Fin.succ_pos j⟩
  invFun j := j.1.pred (Fin.ne_zero_of_lt j.2)
  left_inv j := by simp
  right_inv j := by simp

def succSuffixEquiv (i : Fin m) : {j : Fin m // i < j} ≃ {j : Fin (m + 1) // i.succ < j} where
  toFun j := ⟨j.1.succ, Fin.succ_lt_succ_iff.2 j.2⟩
  invFun j := ⟨j.1.pred (Fin.ne_zero_of_lt j.2), by
    rw [← Fin.succ_lt_succ_iff, Fin.succ_pred]
    exact j.2⟩
  left_inv j := by simp
  right_inv j := by simp

theorem lem_seqexp : ∀ (m : ℕ) (w t : Fin m → G),
    prob (fun ω : Pairs m → Bool => ∀ i, ∑ j, seidelOf ω i j • w j = t i) ≤
      ∏ i : Fin m, rhoG (fun j : {j : Fin m // i < j} => w j)
  | 0, w, t => by
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact prob_le_one _
  | m + 1, w, t => by
    set w' : Fin m → G := fun j => w j.succ with hw'
    let A : (Fin m → Bool) → Prop := fun r => sgnSum w' r = t 0
    let B : (Fin m → Bool) → (Pairs m → Bool) → Prop := fun r ω' =>
      ∀ i : Fin m, ∑ j, seidelOf ω' i j • w' j = t i.succ - sgnZ (r i) • w 0
    have hev : ∀ ω : Pairs (m + 1) → Bool, (∀ i, ∑ j, seidelOf ω i j • w j = t i) ↔
        (A (pairsSplit m ω).1 ∧ B (pairsSplit m ω).1 (pairsSplit m ω).2) := by
      intro ω
      rw [Fin.forall_fin_succ]
      apply and_congr
      · rw [Fin.sum_univ_succ]
        have h00 : seidelOf ω 0 0 = 0 := symOf_apply_self _ _ _ 0
        rw [h00, zero_smul, zero_add]
        simp only [seidelOf_split_zero_succ]
        rfl
      · apply forall_congr'
        intro i
        rw [Fin.sum_univ_succ, seidelOf_split_succ_zero]
        simp only [seidelOf_split_succ_succ]
        rw [eq_sub_iff_add_eq, add_comm]
    have h1 : prob (fun ω : Pairs (m + 1) → Bool => ∀ i, ∑ j, seidelOf ω i j • w j = t i) =
        prob (fun x : (Fin m → Bool) × (Pairs m → Bool) => A x.1 ∧ B x.1 x.2) := by
      rw [← prob_equiv (pairsSplit m) (fun x => A x.1 ∧ B x.1 x.2)]
      exact prob_congr hev
    have hprod_nonneg : 0 ≤ ∏ i : Fin m, rhoG (fun j : {j : Fin m // i < j} => w' j) :=
      prod_nonneg fun i _ => rhoG_nonneg _
    have h2 := prob_and_le_mul A B hprod_nonneg fun r =>
      lem_seqexp m w' (fun i => t i.succ - sgnZ (r i) • w 0)
    have h3 : prob A ≤ rhoG w' := prob_sgnSum_le_rhoG w' (t 0)
    have h4 : rhoG w' = rhoG (fun j : {j : Fin (m + 1) // 0 < j} => w j) :=
      rhoG_comp_equiv (zeroSuffixEquiv m) (fun j : {j : Fin (m + 1) // 0 < j} => w j)
    have h5 : ∀ i : Fin m, rhoG (fun j : {j : Fin m // i < j} => w' j) =
        rhoG (fun j : {j : Fin (m + 1) // i.succ < j} => w j) := fun i =>
      rhoG_comp_equiv (succSuffixEquiv i) (fun j : {j : Fin (m + 1) // i.succ < j} => w j)
    rw [h1, Fin.prod_univ_succ, ← h4]
    simp only [← h5]
    exact h2.trans (mul_le_mul_of_nonneg_right h3 hprod_nonneg)

def pairsPerm (σ : Equiv.Perm (Fin m)) (ω : Pairs m → Bool) : Pairs m → Bool :=
  fun q => decide (seidelOf ω (σ q.1.1) (σ q.1.2) = 1)

theorem seidelOf_pairsPerm (σ : Equiv.Perm (Fin m)) (ω : Pairs m → Bool) (a b : Fin m) :
    seidelOf (pairsPerm σ ω) a b = seidelOf ω (σ a) (σ b) := by
  have key : ∀ a b : Fin m, a < b → seidelOf (pairsPerm σ ω) a b = seidelOf ω (σ a) (σ b) := by
    intro a b h
    rw [seidelOf, symOf_apply_lt _ _ _ h, pairsPerm]
    have hne : σ a ≠ σ b := fun h' => (ne_of_lt h) (σ.injective h')
    rcases (isSeidel_seidelOf ω).2.2 (σ a) (σ b) hne with h1 | h1 <;> simp [h1]
  rcases lt_trichotomy a b with h | rfl | h
  · exact key a b h
  · simp [seidelOf]
  · rw [seidelOf, symOf_comm, ← seidelOf, key b a h, seidelOf, symOf_comm]

theorem pairsPerm_symm_pairsPerm (σ : Equiv.Perm (Fin m)) (ω : Pairs m → Bool) :
    pairsPerm σ.symm (pairsPerm σ ω) = ω := by
  funext q
  obtain ⟨⟨a, b⟩, hab⟩ := q
  simp only [pairsPerm]
  rw [seidelOf_pairsPerm, Equiv.apply_symm_apply, Equiv.apply_symm_apply, seidelOf,
    symOf_apply_lt _ _ _ hab]
  cases ω ⟨(a, b), hab⟩ <;> simp

def pairsPermEquiv (σ : Equiv.Perm (Fin m)) : (Pairs m → Bool) ≃ (Pairs m → Bool) where
  toFun := pairsPerm σ
  invFun := pairsPerm σ.symm
  left_inv ω := pairsPerm_symm_pairsPerm σ ω
  right_inv ω := by
    have := pairsPerm_symm_pairsPerm σ.symm ω
    rwa [Equiv.symm_symm] at this

theorem event_perm (σ : Equiv.Perm (Fin m)) (w t : Fin m → G) (ω : Pairs m → Bool) :
    (∀ i, ∑ j, seidelOf (pairsPerm σ ω) i j • w (σ j) = t (σ i)) ↔
      (∀ i, ∑ j, seidelOf ω i j • w j = t i) := by
  simp only [seidelOf_pairsPerm]
  constructor
  · intro h i
    have := h (σ.symm i)
    rw [Equiv.apply_symm_apply] at this
    rw [← this]
    exact (Equiv.sum_comp σ (fun j => seidelOf ω i j • w j)).symm
  · intro h i
    rw [← h (σ i)]
    exact Equiv.sum_comp σ (fun j => seidelOf ω (σ i) j • w j)

theorem lem_seqexp_perm (w t : Fin m → G) (σ : Equiv.Perm (Fin m)) :
    prob (fun ω : Pairs m → Bool => ∀ i, ∑ j, seidelOf ω i j • w j = t i) ≤
      ∏ i : Fin m, rhoG (fun j : {j : Fin m // i < j} => w (σ j)) := by
  have h1 : prob (fun ω : Pairs m → Bool => ∀ i, ∑ j, seidelOf ω i j • w j = t i) =
      prob (fun ω : Pairs m → Bool => ∀ i, ∑ j, seidelOf ω i j • w (σ j) = t (σ i)) := by
    rw [← prob_equiv (pairsPermEquiv σ)
      (fun ω : Pairs m → Bool => ∀ i, ∑ j, seidelOf ω i j • w (σ j) = t (σ i))]
    exact prob_congr fun ω => (event_perm σ w t ω).symm
  rw [h1]
  exact lem_seqexp m (fun j => w (σ j)) (fun i => t (σ i))

def lastEquiv {c : ℕ} (hc : c ≤ m) : {j : Fin m // m - c ≤ j.val} ≃ Fin c where
  toFun j := ⟨j.1.val - (m - c), by have := j.1.2; omega⟩
  invFun k := ⟨⟨m - c + k.val, by have := k.2; omega⟩, by simp⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    simp only
    have := j.2
    omega
  right_inv k := by
    apply Fin.ext
    simp

theorem prod_range_ite_lt (x : ℝ) {a m : ℕ} (ham : a ≤ m) :
    ∏ k ∈ range m, (if k < a then x else 1) = x ^ a := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le ham
  rw [prod_range_add]
  have h1 : ∏ k ∈ range a, (if k < a then x else 1) = x ^ a := by
    rw [prod_congr rfl fun k hk => ite_eq_left (mem_range.1 hk), prod_const, card_range]
  have h2 : ∏ k ∈ range c, (if a + k < a then x else 1) = 1 :=
    prod_eq_one fun k _ => ite_eq_right (by omega)
  rw [h1, h2, mul_one]

theorem lem_seqexp_block (w t : Fin m → G) (b : Finset (Fin m)) :
    prob (fun ω : Pairs m → Bool => ∀ i, ∑ j, seidelOf ω i j • w j = t i) ≤
      rhoG (fun j : b => w j) ^ (m - b.card) := by
  classical
  set c := b.card with hc
  have hcm : c ≤ m := by
    have := card_le_univ b
    rwa [Fintype.card_fin] at this
  let e : {j : Fin m // m - c ≤ j.val} ≃ {x // x ∈ b} := (lastEquiv hcm).trans b.equivFin.symm
  let σ : Equiv.Perm (Fin m) := Equiv.extendSubtype e
  have hσ_in : ∀ j : Fin m, σ j ∈ b → m - c ≤ j.val := by
    intro j hj
    by_contra h
    have := Equiv.extendSubtype_apply_of_not_mem e j h
    have h2 := (e.toCompl ⟨j, h⟩).2
    rw [← this] at h2
    exact h2 hj
  have hσ_e : ∀ (j : Fin m) (hj : m - c ≤ j.val), σ j = e ⟨j, hj⟩ := fun j hj =>
    Equiv.extendSubtype_apply_of_mem e j hj
  have hfac : ∀ i : Fin m, i.val < m - c →
      rhoG (fun j : {j : Fin m // i < j} => w (σ j)) ≤ rhoG (fun j : b => w j) := by
    intro i hi
    refine (rhoG_le_restrict (fun j : {j : Fin m // i < j} => σ j.1 ∈ b) _).trans (le_of_eq ?_)
    let E : {j' : {j : Fin m // i < j} // σ j'.1 ∈ b} ≃ {x // x ∈ b} :=
      { toFun := fun j' => ⟨σ j'.1.1, j'.2⟩
        invFun := fun x => ⟨⟨(e.symm x).1, by
            have := (e.symm x).2
            show i.val < (e.symm x).1.val
            omega⟩, by
            rw [hσ_e _ (e.symm x).2]
            simp⟩
        left_inv := fun j' => by
          apply Subtype.ext
          apply Subtype.ext
          have hj := hσ_in _ j'.2
          simp only
          have h1 : (⟨σ j'.1.1, j'.2⟩ : {x // x ∈ b}) = e ⟨j'.1.1, hj⟩ := by
            apply Subtype.ext
            simp only
            rw [hσ_e _ hj]
          rw [h1, Equiv.symm_apply_apply]
        right_inv := fun x => by
          apply Subtype.ext
          simp only
          rw [hσ_e _ (e.symm x).2]
          simp }
    exact rhoG_comp_equiv E (fun x : b => w x)
  refine (lem_seqexp_perm w t σ).trans ?_
  calc ∏ i : Fin m, rhoG (fun j : {j : Fin m // i < j} => w (σ j))
      ≤ ∏ i : Fin m, (if i.val < m - c then rhoG (fun j : b => w j) else 1) := by
        refine prod_le_prod₀ (fun i _ => rhoG_nonneg _) fun i _ => ?_
        split_ifs with hi
        · exact hfac i hi
        · exact rhoG_le_one _
    _ = rhoG (fun j : b => w j) ^ (m - c) := by
        rw [Fin.prod_univ_eq_prod_range (fun k => if k < m - c then rhoG (fun j : b => w j) else 1) m]
        exact prod_range_ite_lt _ (Nat.sub_le m c)

end DGS
