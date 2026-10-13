module

public import DGS.S11_Deg1.Deg1

@[expose] public section

open Finset

namespace DGS

section Dissoc

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

def Dissociated (w : Fin m → ZMod p) (B : Finset (Fin m)) : Prop :=
  ∀ c : Fin m → ℤ, (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → (∀ i ∉ B, c i = 0) →
    ∑ i ∈ B, (c i : ZMod p) * w i = 0 → ∀ i, c i = 0

theorem dissociated_empty (w : Fin m → ZMod p) : Dissociated w ∅ :=
  fun _ _ hc _ i => hc i (notMem_empty i)

theorem sgnZ_ne_zero (x : Bool) : sgnZ x ≠ 0 := by
  cases x <;> simp

def halfDiff (ξ ξ' : Fin m → Bool) : Fin m → ℤ := fun i => if ξ i = ξ' i then 0 else sgnZ (ξ i)

theorem halfDiff_mem (ξ ξ' : Fin m → Bool) (i : Fin m) :
    halfDiff ξ ξ' i = -1 ∨ halfDiff ξ ξ' i = 0 ∨ halfDiff ξ ξ' i = 1 := by
  unfold halfDiff
  split_ifs
  · simp
  · cases ξ i <;> simp

theorem two_mul_halfDiff (ξ ξ' : Fin m → Bool) (i : Fin m) :
    (2 : ℤ) * halfDiff ξ ξ' i = sgnZ (ξ i) - sgnZ (ξ' i) := by
  unfold halfDiff
  split_ifs with h
  · rw [h]
    ring
  · cases hξ : ξ i <;> cases hξ' : ξ' i <;> simp_all

theorem sgnSum_sub_eq (w : Fin m → ZMod p) (ξ ξ' : Fin m → Bool) :
    sgnSum w ξ - sgnSum w ξ' = 2 * ∑ i, (halfDiff ξ ξ' i : ZMod p) * w i := by
  unfold sgnSum
  rw [← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [zsmul_eq_mul, zsmul_eq_mul, ← sub_mul, ← mul_assoc]
  congr 1
  have h := congrArg (fun z : ℤ => (z : ZMod p)) (two_mul_halfDiff ξ ξ' i)
  push_cast at h
  rw [h]

theorem prob_sgnSum_le_of_dissociated (hp : p ≠ 2) {w : Fin m → ZMod p} {B : Finset (Fin m)}
    (hB : Dissociated w B) (a : ZMod p) :
    (2 : ℝ) ^ B.card * prob (fun ξ : Fin m → Bool => sgnSum w ξ = a) ≤ 1 := by
  classical
  let f : {ξ : Fin m → Bool // sgnSum w ξ = a} → ({i // i ∉ B} → Bool) := fun ξ i => ξ.1 i
  have hf : Function.Injective f := by
    intro ξ ξ' h
    have hoff : ∀ i, i ∉ B → ξ.1 i = ξ'.1 i := fun i hi => congrFun h ⟨i, hi⟩
    have hcB : ∀ i ∉ B, halfDiff ξ.1 ξ'.1 i = 0 := fun i hi => by simp [halfDiff, hoff i hi]
    have hsum : ∑ i ∈ B, (halfDiff ξ.1 ξ'.1 i : ZMod p) * w i = 0 := by
      have h1 := sgnSum_sub_eq w ξ.1 ξ'.1
      rw [ξ.2, ξ'.2, sub_self] at h1
      have h2 : ∑ i, (halfDiff ξ.1 ξ'.1 i : ZMod p) * w i = 0 := by
        rcases mul_eq_zero.1 h1.symm with h | h
        · exact absurd h (two_ne_zero_zmod hp)
        · exact h
      rw [← h2]
      refine sum_subset (subset_univ B) fun i _ hi => ?_
      rw [hcB i hi]
      simp
    have hc0 := hB _ (halfDiff_mem ξ.1 ξ'.1) hcB hsum
    apply Subtype.ext
    funext i
    by_contra hne
    have h0 := hc0 i
    simp only [halfDiff, hne, ite_false] at h0
    exact sgnZ_ne_zero _ h0
  have hcard : Nat.card {ξ : Fin m → Bool // sgnSum w ξ = a} ≤ 2 ^ (m - B.card) := by
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card {ξ : Fin m → Bool // sgnSum w ξ = a} ≤ Fintype.card ({i // i ∉ B} → Bool) :=
          Fintype.card_le_of_injective f hf
      _ = 2 ^ (m - B.card) := by
          rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_fin,
            Fintype.card_coe]
  have hBm : B.card ≤ m := by simpa using card_le_univ B
  have h2 : (2 : ℝ) ^ B.card * 2 ^ (m - B.card) = 2 ^ m := by
    rw [← pow_add, Nat.add_sub_cancel' hBm]
  unfold prob
  rw [Nat.card_eq_fintype_card (α := Fin m → Bool), Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    mul_div_assoc', div_le_one (by positivity)]
  have hcard' : (Nat.card {ξ : Fin m → Bool // sgnSum w ξ = a} : ℝ) ≤ 2 ^ (m - B.card) := by
    exact_mod_cast hcard
  calc (2 : ℝ) ^ B.card * (Nat.card {ξ : Fin m → Bool // sgnSum w ξ = a} : ℝ)
      ≤ 2 ^ B.card * 2 ^ (m - B.card) := by gcongr
    _ = ((2 ^ m : ℕ) : ℝ) := by push_cast; exact h2

theorem lem_dissoc (hp : p ≠ 2) (w : Fin m → ZMod p) :
    ∃ (B : Finset (Fin m)) (y : Fin m → Fin m → ℤ), (2 : ℝ) ^ B.card * rhoG w ≤ 1 ∧
      (∀ b i, y b i = -1 ∨ y b i = 0 ∨ y b i = 1) ∧
      w = ∑ b ∈ B, w b • fun i => (y b i : ZMod p) := by
  classical
  obtain ⟨B, hBmem, hBmax⟩ := exists_max_image ((univ : Finset (Finset (Fin m))).filter (Dissociated w))
    card ⟨∅, mem_filter.2 ⟨mem_univ _, dissociated_empty w⟩⟩
  have hB : Dissociated w B := (mem_filter.1 hBmem).2
  have hρ : (2 : ℝ) ^ B.card * rhoG w ≤ 1 := by
    have h2 : (0 : ℝ) < 2 ^ B.card := by positivity
    have h := rhoG_le_of_forall (w := w) (c := ((2 : ℝ) ^ B.card)⁻¹) fun a => by
      have h1 := prob_sgnSum_le_of_dissociated hp hB a
      calc prob (fun ξ : Fin m → Bool => sgnSum w ξ = a)
          = ((2 : ℝ) ^ B.card)⁻¹ * ((2 : ℝ) ^ B.card * prob (fun ξ : Fin m → Bool => sgnSum w ξ = a)) := by
            field_simp
        _ ≤ ((2 : ℝ) ^ B.card)⁻¹ * 1 := by gcongr
        _ = ((2 : ℝ) ^ B.card)⁻¹ := mul_one _
    calc (2 : ℝ) ^ B.card * rhoG w ≤ 2 ^ B.card * ((2 : ℝ) ^ B.card)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ h2.ne'
  have hrep : ∀ j, ∃ t : Fin m → ℤ, (∀ b, t b = -1 ∨ t b = 0 ∨ t b = 1) ∧
      w j = ∑ b ∈ B, (t b : ZMod p) * w b := by
    intro j
    by_cases hj : j ∈ B
    · refine ⟨fun b => if b = j then 1 else 0, fun b => by dsimp only; split_ifs <;> simp, ?_⟩
      rw [sum_eq_single j (fun b _ hb => by simp [hb]) (fun h => absurd hj h)]
      simp
    · have hnot : ¬ Dissociated w (insert j B) := by
        intro hd
        have h1 := hBmax (insert j B) (mem_filter.2 ⟨mem_univ _, hd⟩)
        rw [card_insert_of_notMem hj] at h1
        omega
      unfold Dissociated at hnot
      push Not at hnot
      obtain ⟨c, hc, hcB, hsum, i, hi⟩ := hnot
      rw [sum_insert hj] at hsum
      have hcj : c j ≠ 0 := by
        intro hcj0
        apply hi
        refine hB c hc (fun k hk => ?_) ?_ i
        · by_cases hkj : k = j
          · rw [hkj]
            exact hcj0
          · exact hcB k (by simp [hkj, hk])
        · rw [hcj0] at hsum
          simpa using hsum
      have hcj2 : (c j : ZMod p) * c j = 1 := by
        rcases hc j with h | h | h
        · rw [h]
          simp
        · exact absurd h hcj
        · rw [h]
          simp
      refine ⟨fun b => -(c j * c b), fun b => ?_, ?_⟩
      · rcases hc j with h1 | h1 | h1 <;> rcases hc b with h2 | h2 | h2 <;> simp [h1, h2]
      · have h1 : (c j : ZMod p) * w j = -∑ x ∈ B, (c x : ZMod p) * w x := eq_neg_of_add_eq_zero_left hsum
        calc w j = (c j : ZMod p) * ((c j : ZMod p) * w j) := by rw [← mul_assoc, hcj2, one_mul]
          _ = (c j : ZMod p) * -∑ x ∈ B, (c x : ZMod p) * w x := by rw [h1]
          _ = ∑ b ∈ B, ((-(c j * c b) : ℤ) : ZMod p) * w b := by
              rw [mul_neg, mul_sum, ← sum_neg_distrib]
              refine sum_congr rfl fun b _ => ?_
              push_cast
              ring
  choose t ht hwt using hrep
  refine ⟨B, fun b i => t i b, hρ, fun b i => ht i b, ?_⟩
  funext i
  rw [Finset.sum_apply]
  conv_lhs => rw [hwt i]
  refine sum_congr rfl fun b _ => ?_
  simp [mul_comm]

end Dissoc

end DGS
