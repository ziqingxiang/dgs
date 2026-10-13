module

public import DGS.S10_Tools.Signs

@[expose] public section

open Finset

namespace DGS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {ι : Type*} [Fintype ι] [DecidableEq ι]

def sgnSumIdx {l : ℕ} (w : ι → G) (x : (Fin (2 * l) → ι) × (Fin (2 * l) → Bool)) : G :=
  ∑ r, sgnZ (x.2 r) • w (x.1 r)

def vanSet (l : ℕ) (w : ι → G) : Finset ((Fin (2 * l) → ι) × (Fin (2 * l) → Bool)) :=
  univ.filter fun x => sgnSumIdx w x = 0

def Rl (l : ℕ) (w : ι → G) : ℕ := (vanSet l w).card

noncomputable def rl (l : ℕ) (w : ι → G) : ℝ := (Rl l w : ℝ) / (2 * Fintype.card ι : ℝ) ^ (2 * l)

def nDist {l : ℕ} (i : Fin (2 * l) → ι) : ℕ := (univ.image i).card

def Rl' (l : ℕ) (w : ι → G) : ℕ := ((vanSet l w).filter fun x => 3 * l ≤ 2 * nDist x.1).card

omit [DecidableEq ι] in
theorem rl_nonneg (l : ℕ) (w : ι → G) : 0 ≤ rl l w := by
  unfold rl
  positivity

theorem Rl'_le_Rl (l : ℕ) (w : ι → G) : Rl' l w ≤ Rl l w :=
  card_filter_le _ _

theorem card_fewDist_le (l : ℕ) (hD : (3 * l - 1) / 2 ≤ Fintype.card ι) :
    (univ.filter fun i : Fin (2 * l) → ι => 2 * nDist i < 3 * l).card ≤
      (Fintype.card ι) ^ ((3 * l - 1) / 2) * ((3 * l - 1) / 2) ^ (2 * l) := by
  set D := (3 * l - 1) / 2 with hDdef
  calc (univ.filter fun i : Fin (2 * l) → ι => 2 * nDist i < 3 * l).card
      ≤ ((univ : Finset ι).powersetCard D |>.biUnion fun S =>
          Fintype.piFinset fun _ : Fin (2 * l) => S).card := by
        refine card_le_card fun i hi => ?_
        rw [mem_filter] at hi
        have hc : (univ.image i).card ≤ D := by
          have := hi.2
          unfold nDist at this
          omega
        obtain ⟨S, hS1, -, hS3⟩ := exists_subsuperset_card_eq (subset_univ (univ.image i)) hc
          (by rw [card_univ]; exact hD)
        refine mem_biUnion.2 ⟨S, mem_powersetCard.2 ⟨subset_univ _, hS3⟩, ?_⟩
        rw [Fintype.mem_piFinset]
        intro r
        exact hS1 (mem_image_of_mem i (mem_univ r))
    _ ≤ ∑ S ∈ (univ : Finset ι).powersetCard D, (Fintype.piFinset fun _ : Fin (2 * l) => S).card :=
        card_biUnion_le
    _ = ((univ : Finset ι).powersetCard D).card * D ^ (2 * l) := by
        rw [sum_congr rfl fun S hS => ?_, sum_const, smul_eq_mul]
        rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin,
          (mem_powersetCard.1 hS).2]
    _ ≤ (Fintype.card ι) ^ D * D ^ (2 * l) := by
        rw [card_powersetCard, card_univ]
        exact Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)

theorem card_degenerate_le (l : ℕ) (hD : (3 * l - 1) / 2 ≤ Fintype.card ι) :
    (univ.filter fun x : (Fin (2 * l) → ι) × (Fin (2 * l) → Bool) => 2 * nDist x.1 < 3 * l).card ≤
      4 ^ l * ((Fintype.card ι) ^ ((3 * l - 1) / 2) * ((3 * l - 1) / 2) ^ (2 * l)) := by
  have h1 : (univ.filter fun x : (Fin (2 * l) → ι) × (Fin (2 * l) → Bool) =>
      2 * nDist x.1 < 3 * l) =
      (univ.filter fun i : Fin (2 * l) → ι => 2 * nDist i < 3 * l) ×ˢ univ := by
    ext x
    simp
  rw [h1, card_product, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h4 : 2 ^ (2 * l) = 4 ^ l := by rw [pow_mul]; norm_num
  rw [h4, mul_comm]
  exact Nat.mul_le_mul_left _ (card_fewDist_le l hD)

theorem degen_bound (l : ℕ) (hl : 1 ≤ l) (w : ι → G) (hj : 3 * l ≤ 2 * Fintype.card ι) :
    (rl l w - (Fintype.card ι : ℝ) ^ (-(l : ℝ) / 2) * (3 * l / 2 : ℝ) ^ (2 * l)) *
      (2 * Fintype.card ι : ℝ) ^ (2 * l) ≤ Rl' l w := by
  set j := Fintype.card ι with hjdef
  set D := (3 * l - 1) / 2 with hDdef
  have hjpos : 0 < j := by omega
  have hDj : D ≤ j := by omega
  have hsplit : Rl l w ≤ Rl' l w + 4 ^ l * (j ^ D * D ^ (2 * l)) := by
    have h1 := card_filter_add_card_filter_not (s := vanSet l w)
      (fun x : (Fin (2 * l) → ι) × (Fin (2 * l) → Bool) => 3 * l ≤ 2 * nDist x.1)
    have h2 : ((vanSet l w).filter fun x => ¬ 3 * l ≤ 2 * nDist x.1).card ≤
        4 ^ l * (j ^ D * D ^ (2 * l)) := by
      refine le_trans (card_le_card fun x hx => ?_) (card_degenerate_le l hDj)
      rw [mem_filter] at hx ⊢
      exact ⟨mem_univ _, by omega⟩
    unfold Rl Rl'
    omega
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hjpos
  have hjR0 : (0 : ℝ) < j := by exact_mod_cast hjpos
  have hfrac : ((4 ^ l * (j ^ D * D ^ (2 * l)) : ℕ) : ℝ) ≤
      (j : ℝ) ^ (-(l : ℝ) / 2) * (3 * l / 2 : ℝ) ^ (2 * l) * (2 * (j : ℝ)) ^ (2 * l) := by
    push_cast
    have hD1 : (D : ℝ) ≤ 3 * l / 2 := by
      have : 2 * D ≤ 3 * l := by omega
      have : (2 * D : ℝ) ≤ 3 * l := by exact_mod_cast this
      linarith
    have hD2 : (D : ℝ) ^ (2 * l) ≤ (3 * l / 2 : ℝ) ^ (2 * l) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hD1 _
    have hj1 : (j : ℝ) ^ D ≤ (j : ℝ) ^ (-(l : ℝ) / 2) * (j : ℝ) ^ (2 * l) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hjR0]
      apply Real.rpow_le_rpow_of_exponent_le hjR
      push_cast
      linarith
    have h4 : (2 * (j : ℝ)) ^ (2 * l) = 4 ^ l * (j : ℝ) ^ (2 * l) := by
      rw [mul_pow, pow_mul]
      norm_num
    rw [h4]
    have hA : 0 ≤ (j : ℝ) ^ (-(l : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hB : (0 : ℝ) ≤ (D : ℝ) ^ (2 * l) := by positivity
    have hC : (0 : ℝ) ≤ (j : ℝ) ^ D := by positivity
    calc (4 : ℝ) ^ l * ((j : ℝ) ^ D * (D : ℝ) ^ (2 * l))
        ≤ 4 ^ l * (((j : ℝ) ^ (-(l : ℝ) / 2) * (j : ℝ) ^ (2 * l)) * (3 * l / 2 : ℝ) ^ (2 * l)) := by
          gcongr
      _ = _ := by ring
  have hR : (Rl l w : ℝ) = rl l w * (2 * (j : ℝ)) ^ (2 * l) := by
    rw [rl, ← hjdef]
    have : (2 * (j : ℝ)) ^ (2 * l) ≠ 0 := by positivity
    field_simp
  have hsplitR : (Rl l w : ℝ) ≤ Rl' l w + ((4 ^ l * (j ^ D * D ^ (2 * l)) : ℕ) : ℝ) := by
    exact_mod_cast hsplit
  rw [sub_mul]
  linarith

def uniqPos {l : ℕ} (i : Fin (2 * l) → ι) : Finset (Fin (2 * l)) :=
  univ.filter fun r => ∀ r', r' ≠ r → i r' ≠ i r

omit [Fintype ι] in
theorem card_uniqPos_ge {l : ℕ} (i : Fin (2 * l) → ι) :
    2 * nDist i ≤ (uniqPos i).card + 2 * l := by
  classical
  set S := univ.image i with hS
  have h1 : (univ : Finset (Fin (2 * l))).card = ∑ x ∈ S, (univ.filter fun r => i r = x).card :=
    card_eq_sum_card_image i univ
  have h2 : (uniqPos i).card = ∑ x ∈ S, ((uniqPos i).filter fun r => i r = x).card :=
    card_eq_sum_card_fiberwise (f := i) (t := S) fun r _ => mem_image_of_mem i (mem_univ r)
  have h3 : ∀ x ∈ S, 2 ≤ (univ.filter fun r => i r = x).card +
      ((uniqPos i).filter fun r => i r = x).card := by
    intro x hx
    obtain ⟨r, -, rfl⟩ := mem_image.1 hx
    by_cases hc : 2 ≤ (univ.filter fun r' => i r' = i r).card
    · omega
    · have hr : r ∈ uniqPos i := by
        rw [uniqPos, mem_filter]
        refine ⟨mem_univ _, fun r' hr' heq => hc ?_⟩
        have : ({r, r'} : Finset (Fin (2 * l))) ⊆ univ.filter fun r'' => i r'' = i r := by
          intro y hy
          rw [mem_insert, mem_singleton] at hy
          rcases hy with rfl | rfl <;> simp [heq]
        have h2' := card_le_card this
        rw [card_pair (Ne.symm hr')] at h2'
        exact h2'
      have h4 : 1 ≤ (univ.filter fun r' => i r' = i r).card :=
        card_pos.2 ⟨r, mem_filter.2 ⟨mem_univ _, rfl⟩⟩
      have h5 : 1 ≤ ((uniqPos i).filter fun r' => i r' = i r).card :=
        card_pos.2 ⟨r, mem_filter.2 ⟨hr, rfl⟩⟩
      omega
  have h4 := sum_le_sum h3
  rw [sum_const, smul_eq_mul, sum_add_distrib, ← h1, ← h2, card_univ, Fintype.card_fin] at h4
  unfold nDist
  rw [← hS]
  linarith

def vsWit (l : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Finset (Fin (2 * l) × ((Fin (2 * l) → ι) × (Fin (2 * l) → Bool))) :=
  univ.filter fun ω => ∀ r', r' ≠ ω.1 → ω.2.1 r' ≠ ω.2.1 ω.1

theorem card_vsWit_le (l : ℕ) :
    (vsWit l ι).card ≤ 2 * l * (Fintype.card ι) ^ (2 * l) * 4 ^ l := by
  refine (card_filter_le _ _).trans (le_of_eq ?_)
  rw [card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]
  have h4 : 2 ^ (2 * l) = 4 ^ l := by rw [pow_mul]; norm_num
  rw [h4]
  ring

theorem card_validWit_ge (l : ℕ) (w : ι → G) :
    l * Rl' l w ≤ ((vsWit l ι).filter fun ω => sgnSumIdx w ω.2 = 0).card := by
  classical
  set X := (vanSet l w).filter fun x => 3 * l ≤ 2 * nDist x.1 with hX
  set T := X.biUnion fun x => (uniqPos x.1).image fun r => (r, x) with hT
  have hTsub : T ⊆ (vsWit l ι).filter fun ω => sgnSumIdx w ω.2 = 0 := by
    intro ω hω
    obtain ⟨x, hx, hω'⟩ := mem_biUnion.1 hω
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hω'
    rw [hX, mem_filter, vanSet, mem_filter] at hx
    rw [uniqPos, mem_filter] at hr
    rw [mem_filter, vsWit, mem_filter]
    exact ⟨⟨mem_univ _, hr.2⟩, hx.1.2⟩
  have hTcard : T.card = ∑ x ∈ X, (uniqPos x.1).card := by
    rw [hT, card_biUnion]
    · refine sum_congr rfl fun x _ => ?_
      exact card_image_of_injective _ fun r r' h => (Prod.mk.inj h).1
    · intro x _ y _ hxy
      rw [Function.onFun, disjoint_left]
      intro ω h1 h2
      obtain ⟨r, -, rfl⟩ := mem_image.1 h1
      obtain ⟨r', -, h⟩ := mem_image.1 h2
      exact hxy (Prod.mk.inj h).2.symm
  have hle : l * X.card ≤ T.card := by
    rw [hTcard, mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun x hx => ?_
    rw [hX, mem_filter] at hx
    have := card_uniqPos_ge x.1
    omega
  exact hle.trans (card_le_card hTsub)

omit [DecidableEq ι] in
theorem Rl_restrict_le (l : ℕ) (P : ι → Prop) [DecidablePred P] (w : ι → G) :
    Rl l (fun j : {j // P j} => w j) ≤ Rl l w := by
  unfold Rl vanSet
  refine card_le_card_of_injOn (fun x => (fun r => (x.1 r : ι), x.2)) ?_ ?_
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hx ⊢
    exact hx
  · intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    refine Prod.ext (funext fun r => Subtype.ext (congrFun h.1 r)) h.2

end DGS
