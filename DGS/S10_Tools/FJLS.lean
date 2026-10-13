module

public import DGS.S10_Tools.Chains

@[expose] public section

open Finset

namespace DGS

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def vsW (l : ℕ) (b : Finset ι) : Finset (Fin (2 * l) × ((Fin (2 * l) → ι) × (Fin (2 * l) → Bool))) :=
  (vsWit l {x // x ∈ b}).image fun ω => (ω.1, (fun r => (ω.2.1 r : ι)), ω.2.2)

def vsIdx {l : ℕ} (ω : Fin (2 * l) × ((Fin (2 * l) → ι) × (Fin (2 * l) → Bool))) : ι := ω.2.1 ω.1

def vsA {l : ℕ} (ω : Fin (2 * l) × ((Fin (2 * l) → ι) × (Fin (2 * l) → Bool))) (y : ι → G) :
    Finset G :=
  {-(sgnZ (ω.2.2 ω.1) • ∑ r ∈ univ.erase ω.1, sgnZ (ω.2.2 r) • y (ω.2.1 r))}

theorem sgnZ_mul_self (b : Bool) : sgnZ b * sgnZ b = 1 := by cases b <;> rfl

omit [Fintype G] [DecidableEq G] [Fintype ι] [DecidableEq ι] in
theorem vsA_valid_iff {l : ℕ} (ω : Fin (2 * l) × ((Fin (2 * l) → ι) × (Fin (2 * l) → Bool)))
    (y : ι → G) : y (vsIdx ω) ∈ vsA ω y ↔ ∑ r, sgnZ (ω.2.2 r) • y (ω.2.1 r) = 0 := by
  rw [vsA, mem_singleton, vsIdx, ← add_sum_erase _ _ (mem_univ ω.1)]
  set S := ∑ r ∈ univ.erase ω.1, sgnZ (ω.2.2 r) • y (ω.2.1 r)
  set σ := sgnZ (ω.2.2 ω.1)
  have hσ : σ * σ = 1 := sgnZ_mul_self _
  constructor
  · intro h
    rw [h, smul_neg, smul_smul, hσ, one_smul, neg_add_cancel]
  · intro h
    have h2 : σ • (σ • y (ω.2.1 ω.1) + S) = 0 := by rw [h, smul_zero]
    rw [smul_add, smul_smul, hσ, one_smul] at h2
    exact eq_neg_of_add_eq_zero_left h2

omit [Fintype ι] in
theorem vsIdx_mem {l : ℕ} {b : Finset ι} {ω} (hω : ω ∈ vsW l b) : vsIdx ω ∈ b := by
  obtain ⟨ω', -, rfl⟩ := mem_image.1 hω
  exact (ω'.2.1 ω'.1).2

omit [Fintype G] [DecidableEq G] [Fintype ι] in
theorem vsA_local {l : ℕ} {b : Finset ι} {ω} (hω : ω ∈ vsW l b) (y y' : ι → G)
    (h : ∀ j ∈ b, j ≠ vsIdx ω → y j = y' j) : vsA ω y = vsA ω y' := by
  obtain ⟨ω', hω', rfl⟩ := mem_image.1 hω
  rw [vsWit, mem_filter] at hω'
  unfold vsA
  congr 3
  refine sum_congr rfl fun r hr => ?_
  congr 1
  refine h _ (ω'.2.1 r).2 fun heq => hω'.2 r (ne_of_mem_erase hr) ?_
  exact Subtype.ext heq

omit [Fintype ι] in
theorem card_vsW_le (l : ℕ) (b : Finset ι) :
    (vsW l b).card ≤ 2 * l * b.card ^ (2 * l) * 4 ^ l := by
  refine card_image_le.trans ?_
  have := card_vsWit_le (ι := {x // x ∈ b}) l
  rwa [Fintype.card_coe] at this

omit [Fintype G] [Fintype ι] in
theorem card_valid_vsW_ge (l : ℕ) (b : Finset ι) (y : ι → G) :
    l * Rl' l (fun j : b => y j) ≤ ((vsW l b).filter fun ω => y (vsIdx ω) ∈ vsA ω y).card := by
  refine (card_validWit_ge l (fun j : b => y j)).trans ?_
  rw [← card_image_of_injective _ (f := fun ω : Fin (2 * l) × ((Fin (2 * l) → {x // x ∈ b}) ×
      (Fin (2 * l) → Bool)) => (ω.1, (fun r => (ω.2.1 r : ι)), ω.2.2)) ?_]
  · refine card_le_card fun ω hω => ?_
    obtain ⟨ω', hω', rfl⟩ := mem_image.1 hω
    rw [mem_filter] at hω' ⊢
    refine ⟨mem_image_of_mem _ hω'.1, ?_⟩
    rw [vsA_valid_iff]
    exact hω'.2
  · intro x x' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine Prod.ext h1 (Prod.ext (funext fun r => Subtype.ext (congrFun h2 r)) h3)

theorem cor_fjls (ν : G → ℝ) (hν0 : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1) {νmax : ℝ}
    (hνmax : ∀ a, ν a ≤ νmax) {l : ℕ} (hl : 1 ≤ l) (s : ℕ) {t : ℝ} (ht : 0 < t)
    (B : (ι → G) → Prop) [DecidablePred B]
    (hB : ∀ y, B y → ∀ b : Finset ι, s < b.card →
      t * (2 * b.card : ℝ) ^ (2 * l) / Fintype.card G ≤ Rl' l (fun j : b => y j)) :
    pmeas (fun _ => ν) B ≤ (2 * Fintype.card G * νmax / t) ^ (Fintype.card ι - s) := by
  set N : ℝ := (Fintype.card G : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast Fintype.card_pos_iff.2 ⟨0⟩
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hνmax0 : 0 ≤ νmax := (hν0 0).trans (hνmax 0)
  let lam : Unit → ℕ → ℝ := fun _ j => l * t * (2 * (max j 1 : ℕ) : ℝ) ^ (2 * l) / N
  have hlam : ∀ τ j, 0 < lam τ j := by
    intro τ j
    have : (1 : ℝ) ≤ (max j 1 : ℕ) := by exact_mod_cast le_max_right j 1
    show 0 < (l : ℝ) * t * (2 * (max j 1 : ℕ) : ℝ) ^ (2 * l) / N
    positivity
  have h := lem_chains (fun _ : Unit => vsW l) vsIdx vsA lam (fun _ => ν)
    (fun _ a => hν0 a) (fun _ => hν1) hlam (fun _ b ω hω => vsIdx_mem hω)
    (fun _ b ω hω => vsA_local hω) (fun _ => νmax)
    (fun _ b ω hω y => by
      rw [vsA, sum_singleton]
      exact hνmax _)
    (fun _ => hνmax0) s (fun _ => 2 * N * νmax / t) ?_ B ?_
  · rw [prod_const, Nat.card_Ioc] at h
    exact h
  · intro b hb
    rw [Fintype.sum_unique]
    have hb1 : 1 ≤ b.card := by omega
    have hmax : (max b.card 1 : ℕ) = b.card := max_eq_left hb1
    show νmax * (vsW l b).card /
      ((l : ℝ) * t * (2 * (max b.card 1 : ℕ) : ℝ) ^ (2 * l) / N) ≤ 2 * N * νmax / t
    rw [hmax]
    have hc := card_vsW_le l b
    have hc' : ((vsW l b).card : ℝ) ≤ 2 * l * (b.card : ℝ) ^ (2 * l) * 4 ^ l := by
      exact_mod_cast hc
    have hbR : (1 : ℝ) ≤ b.card := by exact_mod_cast hb1
    have hpow : (2 * (b.card : ℝ)) ^ (2 * l) = 4 ^ l * (b.card : ℝ) ^ (2 * l) := by
      rw [mul_pow, pow_mul]
      norm_num
    rw [hpow, div_le_div_iff₀ (by positivity) ht]
    have hbpow : (0 : ℝ) < (b.card : ℝ) ^ (2 * l) := by positivity
    calc νmax * ((vsW l b).card : ℝ) * t
        ≤ νmax * (2 * l * (b.card : ℝ) ^ (2 * l) * 4 ^ l) * t := by gcongr
      _ = 2 * N * νmax * (l * t * (4 ^ l * (b.card : ℝ) ^ (2 * l)) / N) := by
          field_simp
  · intro y hy b hb
    refine ⟨(), ?_⟩
    have hb1 : 1 ≤ b.card := by omega
    have hmax : (max b.card 1 : ℕ) = b.card := max_eq_left hb1
    show (l : ℝ) * t * (2 * (max b.card 1 : ℕ) : ℝ) ^ (2 * l) / N ≤ _
    rw [hmax]
    have h1 := hB y hy b hb
    have h2 := card_valid_vsW_ge (G := G) l b y
    have h2' : (l : ℝ) * (Rl' l (fun j : b => y j) : ℝ) ≤
        (((vsW l b).filter fun ω => y (vsIdx ω) ∈ vsA ω y).card : ℝ) := by
      exact_mod_cast h2
    calc (l : ℝ) * t * (2 * (b.card : ℝ)) ^ (2 * l) / N
        = l * (t * (2 * (b.card : ℝ)) ^ (2 * l) / N) := by ring
      _ ≤ l * (Rl' l (fun j : b => y j) : ℝ) := by
          apply mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ _ := h2'

end DGS
