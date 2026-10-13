module

public import DGS.S10_Tools.VanishingSums

@[expose] public section

open Finset

namespace DGS

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]

noncomputable def pmeas (ν : ι → G → ℝ) (B : (ι → G) → Prop) [DecidablePred B] : ℝ :=
  ∑ y, if B y then ∏ i, ν i (y i) else 0

omit [DecidableEq G] in
theorem sum_prod_prob (ν : ι → G → ℝ) (hν1 : ∀ i, ∑ a, ν i a = 1) :
    ∑ y : ι → G, ∏ i, ν i (y i) = 1 := by
  rw [← Fintype.prod_sum ν]
  simp [hν1]

omit [DecidableEq G] in
theorem pmeas_le_one (ν : ι → G → ℝ) (hν0 : ∀ i a, 0 ≤ ν i a) (hν1 : ∀ i, ∑ a, ν i a = 1)
    (B : (ι → G) → Prop) [DecidablePred B] : pmeas ν B ≤ 1 := by
  rw [← sum_prod_prob ν hν1, pmeas]
  refine sum_le_sum fun y _ => ?_
  split_ifs
  · exact le_rfl
  · exact prod_nonneg fun i _ => hν0 i _

omit [DecidableEq G] in
theorem pmeas_nonneg (ν : ι → G → ℝ) (hν0 : ∀ i a, 0 ≤ ν i a) (B : (ι → G) → Prop)
    [DecidablePred B] : 0 ≤ pmeas ν B :=
  sum_nonneg fun y _ => by split_ifs <;> simp [prod_nonneg fun i _ => hν0 i _]

omit [DecidableEq G] in
theorem pmeas_mono (ν : ι → G → ℝ) (hν0 : ∀ i a, 0 ≤ ν i a) {B B' : (ι → G) → Prop}
    [DecidablePred B] [DecidablePred B'] (h : ∀ y, B y → B' y) : pmeas ν B ≤ pmeas ν B' := by
  refine sum_le_sum fun y _ => ?_
  by_cases hB : B y
  · rw [ite_eq_left hB, ite_eq_left (h y hB)]
  · rw [ite_eq_right hB]
    split_ifs
    · exact prod_nonneg fun i _ => hν0 i _
    · exact le_rfl

theorem sum_prod_ite_le (ν : ι → G → ℝ) (hν0 : ∀ i a, 0 ≤ ν i a) (hν1 : ∀ i, ∑ a, ν i a = 1)
    (i : ι) (A : (ι → G) → Finset G) (f : (ι → G) → ℝ) (hf0 : ∀ y, 0 ≤ f y)
    (hA : ∀ y y' : ι → G, (∀ j, j ≠ i → y j = y' j) → A y = A y')
    (hf : ∀ y y' : ι → G, (∀ j, j ≠ i → y j = y' j) → f y = f y')
    {κ : ℝ} (hκ : ∀ y, ∑ a ∈ A y, ν i a ≤ κ) :
    ∑ y, (∏ j, ν j (y j)) * (if y i ∈ A y then f y else 0) ≤
      κ * ∑ y, (∏ j, ν j (y j)) * f y := by
  rcases isEmpty_or_nonempty G with hG | ⟨⟨a0⟩⟩
  · have : IsEmpty (ι → G) := ⟨fun y => hG.false (y i)⟩
    simp
  set e := Equiv.funSplitAt i G with he
  set yy : G → ({j // j ≠ i} → G) → (ι → G) := fun a z => e.symm (a, z) with hyy
  have hyi : ∀ a z, yy a z i = a := fun a z => by simp [hyy, he]
  have hyj : ∀ a z (j : ι) (hj : j ≠ i), yy a z j = z ⟨j, hj⟩ := fun a z j hj => by
    simp [hyy, he, hj]
  have hagree : ∀ a a' z, ∀ j, j ≠ i → yy a z j = yy a' z j := fun a a' z j hj => by
    rw [hyj a z j hj, hyj a' z j hj]
  set Q : ({j // j ≠ i} → G) → ℝ := fun z => ∏ j : {j // j ≠ i}, ν j (z j) with hQ
  have hQ0 : ∀ z, 0 ≤ Q z := fun z => prod_nonneg fun j _ => hν0 j _
  have hP : ∀ a z, ∏ j, ν j (yy a z j) = ν i a * Q z := by
    intro a z
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, hyi]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    rw [hyj a z j.1 j.2]
  have hsplit : ∀ F : (ι → G) → ℝ, ∑ y, F y = ∑ z : {j // j ≠ i} → G, ∑ a, F (yy a z) := by
    intro F
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, sum_comm]
  rw [hsplit, hsplit, mul_sum]
  refine sum_le_sum fun z _ => ?_
  have hA0 : ∀ a, A (yy a z) = A (yy a0 z) := fun a => hA _ _ (hagree a a0 z)
  have hf0' : ∀ a, f (yy a z) = f (yy a0 z) := fun a => hf _ _ (hagree a a0 z)
  simp only [hP, hyi, hA0, hf0']
  have h1 : ∑ a, ν i a * Q z * (if a ∈ A (yy a0 z) then f (yy a0 z) else 0) =
      Q z * f (yy a0 z) * ∑ a ∈ A (yy a0 z), ν i a := by
    simp_rw [mul_ite, mul_zero]
    rw [← sum_filter, filter_mem_eq_inter, univ_inter, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    ring
  have h2 : ∑ a, ν i a * Q z * f (yy a0 z) = Q z * f (yy a0 z) := by
    rw [← sum_mul, ← sum_mul, hν1, one_mul]
  rw [h1, h2]
  have := hκ (yy a0 z)
  have hQf : 0 ≤ Q z * f (yy a0 z) := mul_nonneg (hQ0 z) (hf0 _)
  nlinarith

variable {Ω T : Type*} [Fintype T]

noncomputable def chainW (W : T → Finset ι → Finset Ω) (idx : Ω → ι) (A : Ω → (ι → G) → Finset G)
    (lam : T → ℕ → ℝ) : ℕ → Finset ι → (ι → G) → ℝ
  | 0, _, _ => 1
  | n + 1, b, y => ∑ τ, ∑ ω ∈ W τ b,
      if y (idx ω) ∈ A ω y then chainW W idx A lam n (b.erase (idx ω)) y / lam τ b.card else 0

variable (W : T → Finset ι → Finset Ω) (idx : Ω → ι) (A : Ω → (ι → G) → Finset G) (lam : T → ℕ → ℝ)

omit [Fintype ι] [Fintype G] in
theorem chainW_nonneg (hlam : ∀ τ j, 0 < lam τ j) :
    ∀ n b y, 0 ≤ chainW W idx A lam n b y
  | 0, b, y => by simp [chainW]
  | n + 1, b, y => by
    simp only [chainW]
    refine sum_nonneg fun τ _ => sum_nonneg fun ω _ => ?_
    split_ifs
    · exact div_nonneg (chainW_nonneg hlam n _ y) (hlam τ _).le
    · exact le_rfl

omit [Fintype ι] [Fintype G] in
theorem chainW_local (hidx : ∀ τ b ω, ω ∈ W τ b → idx ω ∈ b)
    (hloc : ∀ τ b ω, ω ∈ W τ b → ∀ y y' : ι → G, (∀ j ∈ b, j ≠ idx ω → y j = y' j) →
      A ω y = A ω y') :
    ∀ n b (y y' : ι → G), (∀ j ∈ b, y j = y' j) → chainW W idx A lam n b y = chainW W idx A lam n b y'
  | 0, b, y, y', _ => by simp [chainW]
  | n + 1, b, y, y', h => by
    simp only [chainW]
    refine sum_congr rfl fun τ _ => sum_congr rfl fun ω hω => ?_
    have h1 : y (idx ω) = y' (idx ω) := h _ (hidx τ b ω hω)
    have h2 : A ω y = A ω y' := hloc τ b ω hω y y' fun j hj _ => h j hj
    have h3 : chainW W idx A lam n (b.erase (idx ω)) y = chainW W idx A lam n (b.erase (idx ω)) y' :=
      chainW_local hidx hloc n _ y y' fun j hj => h j (mem_of_mem_erase hj)
    rw [h1, h2, h3]

omit [Fintype ι] [Fintype G] in
theorem one_le_chainW (hlam : ∀ τ j, 0 < lam τ j) (hidx : ∀ τ b ω, ω ∈ W τ b → idx ω ∈ b)
    (s : ℕ) (y : ι → G)
    (hy : ∀ b : Finset ι, s < b.card →
      ∃ τ, lam τ b.card ≤ ((W τ b).filter fun ω => y (idx ω) ∈ A ω y).card) :
    ∀ n (b : Finset ι), b.card = s + n → 1 ≤ chainW W idx A lam n b y
  | 0, b, _ => by simp [chainW]
  | n + 1, b, hb => by
    obtain ⟨τ, hτ⟩ := hy b (by omega)
    simp only [chainW]
    have hterm : ∀ τ' ω, 0 ≤ (if y (idx ω) ∈ A ω y then
        chainW W idx A lam n (b.erase (idx ω)) y / lam τ' b.card else 0) := by
      intro τ' ω
      split_ifs
      · exact div_nonneg (chainW_nonneg W idx A lam hlam n _ y) (hlam τ' _).le
      · exact le_rfl
    calc (1 : ℝ) ≤ ((W τ b).filter fun ω => y (idx ω) ∈ A ω y).card / lam τ b.card := by
          rw [le_div_iff₀ (hlam τ _), one_mul]
          exact hτ
      _ = ∑ ω ∈ (W τ b).filter (fun ω => y (idx ω) ∈ A ω y), 1 / lam τ b.card := by
          rw [sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ ∑ ω ∈ (W τ b).filter (fun ω => y (idx ω) ∈ A ω y),
            chainW W idx A lam n (b.erase (idx ω)) y / lam τ b.card := by
          refine sum_le_sum fun ω hω => ?_
          have hidxb := hidx τ b ω (mem_filter.1 hω).1
          have hcard : (b.erase (idx ω)).card = s + n := by
            rw [card_erase_of_mem hidxb]
            omega
          have := one_le_chainW hlam hidx s y hy n _ hcard
          exact div_le_div_of_nonneg_right this (hlam τ _).le
      _ = ∑ ω ∈ W τ b, (if y (idx ω) ∈ A ω y then
            chainW W idx A lam n (b.erase (idx ω)) y / lam τ b.card else 0) := by
          rw [sum_filter]
      _ ≤ ∑ τ', ∑ ω ∈ W τ' b, (if y (idx ω) ∈ A ω y then
            chainW W idx A lam n (b.erase (idx ω)) y / lam τ' b.card else 0) :=
          single_le_sum (f := fun τ' => ∑ ω ∈ W τ' b, (if y (idx ω) ∈ A ω y then
            chainW W idx A lam n (b.erase (idx ω)) y / lam τ' b.card else 0))
            (fun τ' _ => sum_nonneg fun ω _ => hterm τ' ω) (mem_univ τ)

theorem integral_chainW_le (ν : ι → G → ℝ) (hν0 : ∀ i a, 0 ≤ ν i a) (hν1 : ∀ i, ∑ a, ν i a = 1)
    (hlam : ∀ τ j, 0 < lam τ j) (hidx : ∀ τ b ω, ω ∈ W τ b → idx ω ∈ b)
    (hloc : ∀ τ b ω, ω ∈ W τ b → ∀ y y' : ι → G, (∀ j ∈ b, j ≠ idx ω → y j = y' j) →
      A ω y = A ω y')
    (κ : T → ℝ) (hκ : ∀ τ b ω, ω ∈ W τ b → ∀ y, ∑ a ∈ A ω y, ν (idx ω) a ≤ κ τ)
    (hκ0 : ∀ τ, 0 ≤ κ τ) (s : ℕ) (M : ℕ → ℝ)
    (hM : ∀ b : Finset ι, s < b.card → ∑ τ, κ τ * (W τ b).card / lam τ b.card ≤ M b.card) :
    ∀ n (b : Finset ι), b.card = s + n →
      ∑ y, (∏ i, ν i (y i)) * chainW W idx A lam n b y ≤ ∏ j ∈ Ioc s (s + n), M j
  | 0, b, _ => by
    simp only [chainW, mul_one, add_zero, Ioc_self, prod_empty]
    rw [sum_prod_prob ν hν1]
  | n + 1, b, hb => by
    have IH := integral_chainW_le ν hν0 hν1 hlam hidx hloc κ hκ hκ0 s M hM n
    have hMnn : ∀ j ∈ Ioc s (s + (n + 1)), 0 ≤ M j := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := mem_Ioc.1 hj
      obtain ⟨c, -, hc⟩ := exists_subset_card_eq (s := b) (n := j) (by omega)
      have := hM c (by omega)
      rw [hc] at this
      refine le_trans ?_ this
      exact sum_nonneg fun τ _ => div_nonneg (mul_nonneg (hκ0 τ) (Nat.cast_nonneg _))
        (hlam τ _).le
    set X := ∏ j ∈ Ioc s (s + n), M j with hX
    have hX0 : 0 ≤ X := prod_nonneg fun j hj => hMnn j (by
      obtain ⟨h1, h2⟩ := mem_Ioc.1 hj
      exact mem_Ioc.2 ⟨h1, by omega⟩)
    have hone : ∀ τ, ∀ ω ∈ W τ b, ∑ y, (∏ i, ν i (y i)) *
        (if y (idx ω) ∈ A ω y then chainW W idx A lam n (b.erase (idx ω)) y else 0) ≤ κ τ * X := by
      intro τ ω hω
      have hib := hidx τ b ω hω
      have hcard : (b.erase (idx ω)).card = s + n := by
        rw [card_erase_of_mem hib]
        omega
      refine (sum_prod_ite_le ν hν0 hν1 (idx ω) (A ω) (chainW W idx A lam n (b.erase (idx ω)))
        (chainW_nonneg W idx A lam hlam n _) ?_ ?_ (hκ τ b ω hω)).trans ?_
      · intro y y' h
        exact hloc τ b ω hω y y' fun j _ hj => h j hj
      · intro y y' h
        exact chainW_local W idx A lam hidx hloc n _ y y' fun j hj =>
          h j (ne_of_mem_erase hj)
      · exact mul_le_mul_of_nonneg_left (IH _ hcard) (hκ0 τ)
    calc ∑ y, (∏ i, ν i (y i)) * chainW W idx A lam (n + 1) b y
        = ∑ τ, ∑ ω ∈ W τ b, (1 / lam τ b.card) * ∑ y, (∏ i, ν i (y i)) *
            (if y (idx ω) ∈ A ω y then chainW W idx A lam n (b.erase (idx ω)) y else 0) := by
          simp only [chainW, mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun τ _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun ω _ => sum_congr rfl fun y _ => ?_
          split_ifs <;> ring
      _ ≤ ∑ τ, ∑ ω ∈ W τ b, (1 / lam τ b.card) * (κ τ * X) :=
          sum_le_sum fun τ _ => sum_le_sum fun ω hω =>
            mul_le_mul_of_nonneg_left (hone τ ω hω) (div_nonneg zero_le_one (hlam τ _).le)
      _ = (∑ τ, κ τ * (W τ b).card / lam τ b.card) * X := by
          rw [sum_mul]
          refine sum_congr rfl fun τ _ => ?_
          rw [sum_const, nsmul_eq_mul]
          ring
      _ ≤ M b.card * X := mul_le_mul_of_nonneg_right (hM b (by omega)) hX0
      _ = ∏ j ∈ Ioc s (s + (n + 1)), M j := by
          rw [hb, ← add_assoc, prod_Ioc_succ_top (by omega), mul_comm]

theorem lem_chains (ν : ι → G → ℝ) (hν0 : ∀ i a, 0 ≤ ν i a) (hν1 : ∀ i, ∑ a, ν i a = 1)
    (hlam : ∀ τ j, 0 < lam τ j) (hidx : ∀ τ b ω, ω ∈ W τ b → idx ω ∈ b)
    (hloc : ∀ τ b ω, ω ∈ W τ b → ∀ y y' : ι → G, (∀ j ∈ b, j ≠ idx ω → y j = y' j) →
      A ω y = A ω y')
    (κ : T → ℝ) (hκ : ∀ τ b ω, ω ∈ W τ b → ∀ y, ∑ a ∈ A ω y, ν (idx ω) a ≤ κ τ)
    (hκ0 : ∀ τ, 0 ≤ κ τ) (s : ℕ) (M : ℕ → ℝ)
    (hM : ∀ b : Finset ι, s < b.card → ∑ τ, κ τ * (W τ b).card / lam τ b.card ≤ M b.card)
    (B : (ι → G) → Prop) [DecidablePred B]
    (hB : ∀ y, B y → ∀ b : Finset ι, s < b.card →
      ∃ τ, lam τ b.card ≤ ((W τ b).filter fun ω => y (idx ω) ∈ A ω y).card) :
    pmeas ν B ≤ ∏ j ∈ Ioc s (Fintype.card ι), M j := by
  rcases le_or_gt (Fintype.card ι) s with hs | hs
  · rw [Ioc_eq_empty (by omega), prod_empty]
    exact pmeas_le_one ν hν0 hν1 B
  set n := Fintype.card ι - s with hn
  have hcard : (univ : Finset ι).card = s + n := by rw [card_univ]; omega
  have h1 := integral_chainW_le W idx A lam ν hν0 hν1 hlam hidx hloc κ hκ hκ0 s M hM n univ hcard
  rw [show s + n = Fintype.card ι by omega] at h1
  refine le_trans ?_ h1
  unfold pmeas
  refine sum_le_sum fun y _ => ?_
  have hP : 0 ≤ ∏ i, ν i (y i) := prod_nonneg fun i _ => hν0 i _
  split_ifs with hy
  · have := one_le_chainW W idx A lam hlam hidx s y (hB y hy) n univ hcard
    nlinarith
  · exact mul_nonneg hP (chainW_nonneg W idx A lam hlam n univ y)

end DGS
