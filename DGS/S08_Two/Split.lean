module

public import DGS.S08_Two.Coupling

@[expose] public section

open Matrix Polynomial Module

namespace DGS

variable {n : ℕ}

local notation "V" => Fin n → ZMod 2

def SplitAt (S : Finset (Fin n)) (L : Submodule (ZMod 2) V) : Prop :=
  IsMaxIso S (L.map (projS S)) ∧ IsMaxIso Sᶜ (L.map (projS Sᶜ)) ∧
    L = L.map (projS S) ⊔ L.map (projS Sᶜ)

theorem projS_dot_projS (S : Finset (Fin n)) (y z : V) :
    projS S y ⬝ᵥ projS S z = (y * z) ⬝ᵥ indS S := by
  simp only [dotProduct, projS_apply, indS, Pi.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

theorem dot_eq_projS_add (S : Finset (Fin n)) (y z : V) :
    y ⬝ᵥ z = projS S y ⬝ᵥ projS S z + projS Sᶜ y ⬝ᵥ projS Sᶜ z := by
  simp only [dotProduct, projS_apply, Finset.mem_compl, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S <;> simp [hi]

theorem exists_splitAt {L : Submodule (ZMod 2) V} (hL : IsMaxIso Finset.univ L) (hB : BadL L) :
    ∃ S : Finset (Fin n), S.Nonempty ∧ S ≠ Finset.univ ∧ S.card / 2 + Sᶜ.card / 2 = n / 2 ∧
      SplitAt S L := by
  classical
  obtain ⟨w, hw, hwe⟩ : ∃ w ∈ orthC (prodSpanL L),
      w ∉ Submodule.span (ZMod 2) {ones n (ZMod 2)} := by
    by_contra h
    push Not at h
    apply hB
    have h1 : orthC (prodSpanL L) ≤ Submodule.span (ZMod 2) {ones n (ZMod 2)} := h
    have h2 := orthC_anti h1
    rwa [orthC_orthC] at h2
  set S := Finset.univ.filter fun i => w i ≠ 0 with hSdef
  have hwS : w = indS S := by
    funext i
    simp only [indS, hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · exact zmod2_eq_one_of_ne_zero h
    · push Not at h
      exact h
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hwe
    rw [hwS, h]
    have : indS (∅ : Finset (Fin n)) = 0 := by
      funext i
      simp [indS]
    rw [this]
    exact Submodule.zero_mem _
  have hSuniv : S ≠ Finset.univ := by
    intro h
    apply hwe
    rw [hwS, h, indS_univ]
    exact Submodule.mem_span_singleton_self _
  have hiso1 : ∀ y ∈ L, ∀ z ∈ L, projS S y ⬝ᵥ projS S z = 0 := by
    intro y hy z hz
    rw [projS_dot_projS, ← hwS]
    exact hw _ (Submodule.subset_span ⟨y, hy, z, hz, rfl⟩)
  have hiso2 : ∀ y ∈ L, ∀ z ∈ L, projS Sᶜ y ⬝ᵥ projS Sᶜ z = 0 := by
    intro y hy z hz
    have h1 := dot_eq_projS_add S y z
    rw [hL.2.1 y hy z hz, hiso1 y hy z hz, zero_add] at h1
    exact h1.symm
  have hmap1 : L.map (projS S) ≤ coordSub S := by
    rintro _ ⟨y, -, rfl⟩
    exact projS_mem S y
  have hmap2 : L.map (projS Sᶜ) ≤ coordSub Sᶜ := by
    rintro _ ⟨y, -, rfl⟩
    exact projS_mem Sᶜ y
  have hiso1' : ∀ x ∈ L.map (projS S), ∀ x' ∈ L.map (projS S), x ⬝ᵥ x' = 0 := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact hiso1 y hy z hz
  have hiso2' : ∀ x ∈ L.map (projS Sᶜ), ∀ x' ∈ L.map (projS Sᶜ), x ⬝ᵥ x' = 0 := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact hiso2 y hy z hz
  have hd1 := finrank_iso_le hmap1 hiso1'
  have hd2 := finrank_iso_le hmap2 hiso2'
  have hle : L ≤ L.map (projS S) ⊔ L.map (projS Sᶜ) := by
    intro y hy
    rw [← projS_add_projS_compl S y]
    exact Submodule.add_mem_sup ⟨y, hy, rfl⟩ ⟨y, hy, rfl⟩
  have hd3 := Submodule.finrank_mono hle
  have hd4 := Submodule.finrank_add_le_finrank_add_finrank (L.map (projS S)) (L.map (projS Sᶜ))
  have hcard : S.card + Sᶜ.card = n := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ S
    rw [Fintype.card_fin] at this
    omega
  have hL2 := hL.2.2
  rw [Finset.card_univ, Fintype.card_fin] at hL2
  refine ⟨S, hSne, hSuniv, by omega, ⟨hmap1, hiso1', by omega⟩, ⟨hmap2, hiso2', by omega⟩, ?_⟩
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

theorem natCard_le_sum_of_exists {α ι : Type*} [Finite α] (P : α → Prop) (T : Finset ι)
    (Q : ι → α → Prop) (h : ∀ a, P a → ∃ i ∈ T, Q i a) :
    Nat.card {a // P a} ≤ ∑ i ∈ T, Nat.card {a // Q i a} := by
  classical
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc (Finset.univ.filter P).card ≤ (T.biUnion fun i => Finset.univ.filter (Q i)).card := by
        apply Finset.card_le_card
        intro a ha
        rw [Finset.mem_filter] at ha
        obtain ⟨i, hi, hq⟩ := h a ha.2
        exact Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩⟩
    _ ≤ ∑ i ∈ T, (Finset.univ.filter (Q i)).card := Finset.card_biUnion_le

theorem card_split_le (S : Finset (Fin n)) :
    Nat.card {L : Submodule (ZMod 2) V // SplitAt S L} ≤
      Nat.card {L : Submodule (ZMod 2) V // IsMaxIso S L} *
        Nat.card {L : Submodule (ZMod 2) V // IsMaxIso Sᶜ L} := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun L => (⟨L.1.map (projS S), L.2.1⟩, ⟨L.1.map (projS Sᶜ), L.2.2.1⟩)) ?_
  intro L L' h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  apply Subtype.ext
  calc L.1 = L.1.map (projS S) ⊔ L.1.map (projS Sᶜ) := L.2.2.2
    _ = L'.1.map (projS S) ⊔ L'.1.map (projS Sᶜ) := by rw [h.1, h.2]
    _ = L'.1 := L'.2.2.2.symm

def splitSupports (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S : Finset (Fin n) =>
    S.Nonempty ∧ S ≠ Finset.univ ∧ S.card / 2 + Sᶜ.card / 2 = n / 2

theorem card_bad_maxIso_le :
    Nat.card {L : Submodule (ZMod 2) V // IsMaxIso Finset.univ L ∧ BadL L} ≤
      ∑ S ∈ splitSupports n, theta (kap S - 1) * theta (kap Sᶜ - 1) := by
  classical
  refine (natCard_le_sum_of_exists _ (splitSupports n) (fun S L => SplitAt S L) ?_).trans ?_
  · rintro L ⟨hL, hB⟩
    obtain ⟨S, h1, h2, h3, h4⟩ := exists_splitAt hL hB
    exact ⟨S, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2, h3⟩, h4⟩
  · refine Finset.sum_le_sum fun S hS => ?_
    obtain ⟨-, h1, h2, -⟩ := Finset.mem_filter.1 hS
    have h2' : Sᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]
      exact h2
    rw [← card_maxIso h1, ← card_maxIso h2']
    exact card_split_le S

end DGS
