module

public import DGS.Ext.Kneser.Stab

@[expose] public section

open Finset
open scoped Pointwise

namespace DGS

universe u

section Kneser

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def KneserIneq (A B : Finset G) : Prop :=
  (A + addStab (A + B)).card + (B + addStab (A + B)).card ≤ (A + B).card + (addStab (A + B)).card

def IsConv (A B C : Finset G) : Prop :=
  C ⊆ A + B ∧ (A ∩ B).card + ((A ∪ B) + addStab C).card ≤ C.card + (addStab C).card

theorem eq_singleton_zero_of_card_le_one {X : Finset G} (h : (addStab X).card ≤ 1) :
    addStab X = {0} :=
  (eq_singleton_iff_unique_mem.2 ⟨zero_mem_addStab X, fun g hg =>
    card_le_one.1 h g hg 0 (zero_mem_addStab X)⟩)

theorem kneser_contra {A B C : Finset G}
    (IH : ∀ A' B' : Finset G, A'.Nonempty → B'.Nonempty →
      (A' + B').card + A'.card < (A + B).card + A.card → KneserIneq A' B')
    (hK : addStab (A + B) = {0}) (hAB : (A ∩ B).Nonempty)
    (hC : IsConv A B C) (hmin : ∀ C', IsConv A B C' → (addStab C).card ≤ (addStab C').card)
    (hH2 : 2 ≤ (addStab C).card) : False := by
  classical
  set H := addStab C with hH
  have hA : A.Nonempty := hAB.mono inter_subset_left
  have hB : B.Nonempty := hAB.mono inter_subset_right
  have hABne : (A ∪ B).Nonempty := hA.mono subset_union_left
  have hCne : C.Nonempty := by
    rcases C.eq_empty_or_nonempty with h0 | h0
    · exfalso
      have h1 := hC.2
      rw [h0, addStab_empty] at h1
      have h2 : (A ∪ B) + (univ : Finset G) = univ := by
        refine eq_univ_of_forall fun z => ?_
        obtain ⟨x, hx⟩ := hABne
        exact mem_add.2 ⟨x, hx, z - x, mem_univ _, by abel⟩
      rw [h2, card_empty] at h1
      have h3 := hAB.card_pos
      omega
    · exact h0
  obtain ⟨a, ha, b, hb, h₀, hh₀, hout⟩ : ∃ a ∈ A, ∃ b ∈ B, ∃ h ∈ H, a + b + h ∉ A + B := by
    by_contra hcon
    push Not at hcon
    have hsub : H ⊆ {0} := by
      intro g hg
      rw [← hK]
      refine mem_addStab.2 fun z hz => ?_
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hz
      have := hcon x hx y hy g hg
      rw [show g + (x + y) = x + y + g by abel]
      exact this
    have := card_le_card hsub
    rw [card_singleton] at this
    omega
  set c₀ := a + b with hc₀
  set Y := coset C c₀ with hY
  have hYC : ∀ y ∈ Y, y ∉ C := by
    intro y hy hyC
    apply hout
    have h1 : y - c₀ ∈ H := mem_coset.1 hy
    have h2 : h₀ - (y - c₀) ∈ H := sub_mem_addStab hh₀ h1
    have h3 := mem_addStab.1 h2 y hyC
    rw [show h₀ - (y - c₀) + y = c₀ + h₀ by abel] at h3
    exact hC.1 h3
  have hYAB : ¬ Y ⊆ A + B := fun h => hout (h (mem_coset.2 (by simpa using hh₀)))
  have key : ∀ P Q : Finset G, P ⊆ A → Q ⊆ B → P.Nonempty → Q.Nonempty → P + Q ⊆ Y →
      ((A ∪ B) + H).card + (P + addStab (P + Q)).card + (Q + addStab (P + Q)).card <
        H.card + ((A ∪ B) + addStab (P + Q)).card ∧
      addStab (P + Q) ⊆ H ∧ KneserIneq P Q ∧ C.card + (P + Q).card ≤ (A + B).card := by
    intro P Q hPA hQB hP hQ hPQY
    set X := P + Q with hX
    have hXAB : X ⊆ A + B := add_subset_add hPA hQB
    have hXne : X.Nonempty := hP.add hQ
    have hdisj : Disjoint C X := by
      rw [disjoint_left]
      intro z hzC hzX
      exact hYC z (hPQY hzX) hzC
    have hSXH : addStab X ⊆ H := by
      intro g hg
      obtain ⟨x, hx⟩ := hXne
      have h1 : g + x ∈ X := mem_addStab.1 hg x hx
      have h2 : g + x - c₀ ∈ H := mem_coset.1 (hPQY h1)
      have h3 : x - c₀ ∈ H := mem_coset.1 (hPQY hx)
      have h4 := sub_mem_addStab h2 h3
      rw [show g + x - c₀ - (x - c₀) = g by abel] at h4
      exact h4
    have hSXlt : (addStab X).card < H.card := by
      refine card_lt_card ⟨hSXH, fun hHX => hYAB fun y hy => ?_⟩
      obtain ⟨x, hx⟩ := hXne
      have h1 : y - x ∈ H := by
        have h2 : y - c₀ ∈ H := mem_coset.1 hy
        have h3 : x - c₀ ∈ H := mem_coset.1 (hPQY hx)
        have h4 := sub_mem_addStab h2 h3
        rwa [show y - c₀ - (x - c₀) = y - x by abel] at h4
      have h5 := mem_addStab.1 (hHX h1) x hx
      rw [show y - x + x = y by abel] at h5
      exact hXAB h5
    have hSCX : addStab (C ∪ X) = addStab X := by
      ext g
      constructor
      · intro hg
        refine mem_addStab.2 fun x hx => ?_
        have h1 := mem_addStab.1 hg x (mem_union_right _ hx)
        rcases mem_union.1 h1 with h2 | h2
        · exfalso
          apply hYAB
          intro y hy
          have h3 : y - x ∈ H := by
            have h4 : y - c₀ ∈ H := mem_coset.1 hy
            have h5 : x - c₀ ∈ H := mem_coset.1 (hPQY hx)
            have h6 := sub_mem_addStab h4 h5
            rwa [show y - c₀ - (x - c₀) = y - x by abel] at h6
          have h7 : y - x + (g + x) ∈ C := mem_addStab.1 h3 _ h2
          have h8 := mem_addStab.1 (neg_mem_addStab hg) _ (mem_union_left _ h7)
          rw [show -g + (y - x + (g + x)) = y by abel] at h8
          rcases mem_union.1 h8 with h9 | h9
          · exact absurd h9 (hYC y hy)
          · exact hXAB h9
        · exact h2
      · intro hg
        refine mem_addStab.2 fun z hz => ?_
        rcases mem_union.1 hz with h1 | h1
        · exact mem_union_left _ (mem_addStab.1 (hSXH hg) z h1)
        · exact mem_union_right _ (mem_addStab.1 hg z h1)
    have hnot : ¬ IsConv A B (C ∪ X) := by
      intro hconv
      have := hmin _ hconv
      rw [hSCX] at this
      omega
    have hCX : C ∪ X ⊆ A + B := union_subset hC.1 hXAB
    have hnot' : (C ∪ X).card + (addStab X).card < (A ∩ B).card + ((A ∪ B) + addStab X).card := by
      by_contra h
      push Not at h
      exact hnot ⟨hCX, by rw [hSCX]; exact h⟩
    rw [card_union_of_disjoint hdisj] at hnot'
    have hCX' : C.card + X.card ≤ (A + B).card := by
      rw [← card_union_of_disjoint hdisj]
      exact card_le_card hCX
    have hPcard : P.card ≤ A.card := card_le_card hPA
    have hCpos := hCne.card_pos
    have hXPQ : (P + Q).card = X.card := rfl
    have hIH : KneserIneq P Q := IH P Q hP hQ (by omega)
    have hconvC := hC.2
    rw [← hH] at hconvC
    unfold KneserIneq at hIH
    rw [← hX] at hIH
    refine ⟨by omega, hSXH, ?_, hCX'⟩
    unfold KneserIneq
    exact hIH
  set A₁ := A.filter (· ∈ coset C a) with hA₁
  set A₂ := A.filter (· ∈ coset C b) with hA₂
  set B₁ := B.filter (· ∈ coset C b) with hB₁
  set B₂ := B.filter (· ∈ coset C a) with hB₂
  have hsumY : ∀ u v : G, u + v = c₀ → ∀ x y : G, x ∈ coset C u → y ∈ coset C v → x + y ∈ Y := by
    intro u v huv x y hx hy
    refine mem_coset.2 ?_
    have := add_mem_addStab (mem_coset.1 hx) (mem_coset.1 hy)
    rwa [show x - u + (y - v) = x + y - c₀ by rw [← huv]; abel] at this
  have hPQY : ∀ (P Q : Finset G) (u v : G), u + v = c₀ → (∀ x ∈ P, x ∈ coset C u) →
      (∀ y ∈ Q, y ∈ coset C v) → P + Q ⊆ Y := by
    intro P Q u v huv hP hQ z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hz
    exact hsumY u v huv x y (hP x hx) (hQ y hy)
  have hA₁ne : A₁.Nonempty := ⟨a, mem_filter.2 ⟨ha, self_mem_coset C a⟩⟩
  have hB₁ne : B₁.Nonempty := ⟨b, mem_filter.2 ⟨hb, self_mem_coset C b⟩⟩
  obtain ⟨k1, hS1H, hIH1, hC1⟩ := key A₁ B₁ (filter_subset _ _) (filter_subset _ _) hA₁ne hB₁ne
    (hPQY A₁ B₁ a b rfl (fun x hx => (mem_filter.1 hx).2) (fun y hy => (mem_filter.1 hy).2))
  set H₁ := addStab (A₁ + B₁) with hH₁
  have cov : ∀ (H' : Finset G), H' ⊆ H → ∀ w ∈ A ∪ B, ∀ P Q : Finset G,
      ((A ∪ B).filter (· ∈ coset C w) ⊆ P ∪ Q) →
      ((A ∪ B) + H').card + H.card ≤ ((A ∪ B) + H).card + (P + H').card + (Q + H').card := by
    intro H' hH'H w hw P Q hPQ
    set U := (A ∪ B) + H' with hU
    set V := coset C w with hV
    have hUsub : U ⊆ (A ∪ B) + H := add_subset_add_left hH'H
    have hVsub : V ⊆ (A ∪ B) + H := by
      intro v hv
      exact mem_add.2 ⟨w, hw, v - w, mem_coset.1 hv, by abel⟩
    have hUV : U ∩ V ⊆ (P + H') ∪ (Q + H') := by
      intro z hz
      obtain ⟨hzU, hzV⟩ := mem_inter.1 hz
      obtain ⟨x, hx, h', hh', rfl⟩ := mem_add.1 hzU
      have hxw : x ∈ coset C w := by
        refine mem_coset.2 ?_
        have h1 := sub_mem_addStab (mem_coset.1 hzV) (hH'H hh')
        rwa [show x + h' - w - h' = x - w by abel] at h1
      have hxPQ := hPQ (mem_filter.2 ⟨hx, hxw⟩)
      rcases mem_union.1 hxPQ with h2 | h2
      · exact mem_union_left _ (mem_add.2 ⟨x, h2, h', hh', rfl⟩)
      · exact mem_union_right _ (mem_add.2 ⟨x, h2, h', hh', rfl⟩)
    have h1 := card_union_add_card_inter U V
    have h2 := card_le_card (union_subset hUsub hVsub)
    have h3 := (card_le_card hUV).trans (card_union_le _ _)
    have h4 : V.card = H.card := card_coset C w
    omega
  have hAB1 : (A ∪ B).filter (· ∈ coset C a) ⊆ A₁ ∪ B₂ := by
    intro x hx
    obtain ⟨hxAB, hxa⟩ := mem_filter.1 hx
    rcases mem_union.1 hxAB with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨h, hxa⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨h, hxa⟩)
  have hAB2 : (A ∪ B).filter (· ∈ coset C b) ⊆ A₂ ∪ B₁ := by
    intro x hx
    obtain ⟨hxAB, hxb⟩ := mem_filter.1 hx
    rcases mem_union.1 hxAB with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨h, hxb⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨h, hxb⟩)
  have hA₁pos := (hA₁ne.add (addStab_nonempty (A₁ + B₁))).card_pos
  have hB₁pos := (hB₁ne.add (addStab_nonempty (A₁ + B₁))).card_pos
  have hB₂ne : B₂.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h0
    have h1 := cov H₁ hS1H a (mem_union_left _ ha) A₁ B₂ hAB1
    rw [h0, empty_add, card_empty] at h1
    omega
  have hA₂ne : A₂.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h0
    have h1 := cov H₁ hS1H b (mem_union_right _ hb) A₂ B₁ hAB2
    rw [h0, empty_add, card_empty] at h1
    omega
  have hab : b - a ∉ H := by
    intro hba
    have hB₂B₁ : B₂ ⊆ B₁ := by
      intro x hx
      obtain ⟨hxB, hxa⟩ := mem_filter.1 hx
      refine mem_filter.2 ⟨hxB, mem_coset.2 ?_⟩
      have h1 := sub_mem_addStab (mem_coset.1 hxa) hba
      rwa [show x - a - (b - a) = x - b by abel] at h1
    have h1 := cov H₁ hS1H a (mem_union_left _ ha) A₁ B₁ (hAB1.trans (union_subset_union subset_rfl hB₂B₁))
    omega
  obtain ⟨k2, hS2H, hIH2, hC2⟩ := key A₂ B₂ (filter_subset _ _) (filter_subset _ _) hA₂ne hB₂ne
    (hPQY A₂ B₂ b a (by rw [hc₀, add_comm]) (fun x hx => (mem_filter.1 hx).2) (fun y hy => (mem_filter.1 hy).2))
  set H₂ := addStab (A₂ + B₂) with hH₂
  have step2 : ∀ (P Q : Finset G), P.Nonempty → Q.Nonempty → addStab (P + Q) ⊆ H →
      ((A ∪ B) + H).card + (P + addStab (P + Q)).card + (Q + addStab (P + Q)).card <
        H.card + ((A ∪ B) + addStab (P + Q)).card →
      P.card + Q.card + (addStab (P + Q)).card ≤ H.card := by
    intro P Q hP hQ hSH hk
    have h1 : ((A ∪ B) + addStab (P + Q)).card ≤ ((A ∪ B) + H).card := card_le_card (add_subset_add_left hSH)
    have hlt : (P + addStab (P + Q)).card + (Q + addStab (P + Q)).card < H.card := by omega
    have hd1 : (addStab (P + Q)).card ∣ (P + addStab (P + Q)).card :=
      card_dvd_card_of_subset (addStab_subset_addStab_add P (P + Q))
    have hd2 : (addStab (P + Q)).card ∣ (Q + addStab (P + Q)).card :=
      card_dvd_card_of_subset (addStab_subset_addStab_add Q (P + Q))
    have hd3 : (addStab (P + Q)).card ∣ H.card := by
      refine card_dvd_card_of_subset fun g hg => mem_addStab.2 fun h hh => add_mem_addStab (hSH hg) hh
    have hd : (addStab (P + Q)).card ∣ H.card - ((P + addStab (P + Q)).card + (Q + addStab (P + Q)).card) :=
      Nat.dvd_sub hd3 (dvd_add hd1 hd2)
    have hpos : 0 < H.card - ((P + addStab (P + Q)).card + (Q + addStab (P + Q)).card) := by omega
    have h2 := Nat.le_of_dvd hpos hd
    have h3 : P.card ≤ (P + addStab (P + Q)).card := card_le_card_add_right (addStab_nonempty _)
    have h4 : Q.card ≤ (Q + addStab (P + Q)).card := card_le_card_add_right (addStab_nonempty _)
    omega
  have e1 := step2 A₁ B₁ hA₁ne hB₁ne hS1H k1
  have e2 := step2 A₂ B₂ hA₂ne hB₂ne hS2H k2
  rw [← hH₁] at e1
  rw [← hH₂] at e2
  set S := (coset C a).filter (· ∉ A ∪ B) with hSdef
  set T := (coset C b).filter (· ∉ A ∪ B) with hTdef
  have hdisjST : Disjoint S T := by
    rw [disjoint_left]
    intro z hzS hzT
    apply hab
    have h1 := sub_mem_addStab (mem_coset.1 (mem_filter.1 hzS).1) (mem_coset.1 (mem_filter.1 hzT).1)
    rwa [show z - a - (z - b) = b - a by abel] at h1
  have hdisjAS : Disjoint (A ∪ B) (S ∪ T) := by
    rw [disjoint_left]
    intro z hz hzST
    rcases mem_union.1 hzST with h | h
    · exact (mem_filter.1 h).2 hz
    · exact (mem_filter.1 h).2 hz
  have hcover : (A ∪ B) ∪ (S ∪ T) ⊆ (A ∪ B) + H := by
    intro z hz
    rcases mem_union.1 hz with h | h
    · exact mem_add.2 ⟨z, h, 0, zero_mem_addStab C, add_zero z⟩
    · rcases mem_union.1 h with h' | h'
      · exact mem_add.2 ⟨a, mem_union_left _ ha, z - a, mem_coset.1 (mem_filter.1 h').1, by abel⟩
      · exact mem_add.2 ⟨b, mem_union_right _ hb, z - b, mem_coset.1 (mem_filter.1 h').1, by abel⟩
  have hcardST : (A ∪ B).card + S.card + T.card ≤ ((A ∪ B) + H).card := by
    have h1 := card_le_card hcover
    rw [card_union_of_disjoint hdisjAS, card_union_of_disjoint hdisjST] at h1
    omega
  have hnotAB : (A + B).card + 1 < (A ∩ B).card + (A ∪ B).card := by
    by_contra h
    push Not at h
    have hconv : IsConv A B (A + B) := by
      refine ⟨subset_rfl, ?_⟩
      rw [hK, card_singleton, add_singleton_zero']
      omega
    have := hmin _ hconv
    rw [hK, card_singleton] at this
    omega
  have hconvC := hC.2
  rw [← hH] at hconvC
  unfold KneserIneq at hIH1 hIH2
  rw [← hH₁] at hIH1
  rw [← hH₂] at hIH2
  have hA₁' : A₁.card ≤ (A₁ + H₁).card := card_le_card_add_right (addStab_nonempty _)
  have hB₁' : B₁.card ≤ (B₁ + H₁).card := card_le_card_add_right (addStab_nonempty _)
  have hA₂' : A₂.card ≤ (A₂ + H₂).card := card_le_card_add_right (addStab_nonempty _)
  have hB₂' : B₂.card ≤ (B₂ + H₂).card := card_le_card_add_right (addStab_nonempty _)
  have hcovA : H.card ≤ S.card + A₁.card + B₂.card := by
    have h1 : coset C a ⊆ S ∪ A₁ ∪ B₂ := by
      intro z hz
      by_cases hzAB : z ∈ A ∪ B
      · rcases mem_union.1 hzAB with h | h
        · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨h, hz⟩))
        · exact mem_union_right _ (mem_filter.2 ⟨h, hz⟩)
      · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hz, hzAB⟩))
    have h2 := card_le_card h1
    have h3 := card_union_le (S ∪ A₁) B₂
    have h4 := card_union_le S A₁
    have h5 : (coset C a).card = H.card := card_coset C a
    omega
  have hcovB : H.card ≤ T.card + A₂.card + B₁.card := by
    have h1 : coset C b ⊆ T ∪ A₂ ∪ B₁ := by
      intro z hz
      by_cases hzAB : z ∈ A ∪ B
      · rcases mem_union.1 hzAB with h | h
        · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨h, hz⟩))
        · exact mem_union_right _ (mem_filter.2 ⟨h, hz⟩)
      · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hz, hzAB⟩))
    have h2 := card_le_card h1
    have h3 := card_union_le (T ∪ A₂) B₁
    have h4 := card_union_le T A₂
    have h5 : (coset C b).card = H.card := card_coset C b
    omega
  omega

theorem kneser_core {A B : Finset G}
    (IH : ∀ A' B' : Finset G, A'.Nonempty → B'.Nonempty →
      (A' + B').card + A'.card < (A + B).card + A.card → KneserIneq A' B')
    (hK : addStab (A + B) = {0}) (hAB : (A ∩ B).Nonempty) (hABA : (A ∩ B).card < A.card) :
    A.card + B.card ≤ (A + B).card + 1 := by
  classical
  have hA : A.Nonempty := hAB.mono inter_subset_left
  have hsub : (A ∩ B) + (A ∪ B) ⊆ A + B := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hz
    rw [mem_inter] at hx
    rcases mem_union.1 hy with hyA | hyB
    · exact mem_add.2 ⟨y, hyA, x, hx.2, add_comm _ _⟩
    · exact mem_add.2 ⟨x, hx.1, y, hyB, rfl⟩
  have hC₀ : IsConv A B ((A ∩ B) + (A ∪ B)) := by
    refine ⟨hsub, ?_⟩
    have h1 := IH (A ∩ B) (A ∪ B) hAB (hA.mono subset_union_left) (by
      have := card_le_card hsub
      omega)
    unfold KneserIneq at h1
    have h2 : (A ∩ B).card ≤ ((A ∩ B) + addStab ((A ∩ B) + (A ∪ B))).card :=
      card_le_card_add_right (addStab_nonempty _)
    omega
  obtain ⟨C, hCmem, hCmin⟩ := exists_min_image ((A + B).powerset.filter (IsConv A B))
    (fun C => (addStab C).card) ⟨_, mem_filter.2 ⟨mem_powerset.2 hC₀.1, hC₀⟩⟩
  have hC : IsConv A B C := (mem_filter.1 hCmem).2
  have hmin : ∀ C', IsConv A B C' → (addStab C).card ≤ (addStab C').card := fun C' h =>
    hCmin C' (mem_filter.2 ⟨mem_powerset.2 h.1, h⟩)
  by_cases hH1 : (addStab C).card ≤ 1
  · have hH0 := eq_singleton_zero_of_card_le_one hH1
    have h1 := hC.2
    rw [hH0, card_singleton, add_singleton_zero'] at h1
    have h2 := card_union_add_card_inter A B
    have h3 := card_le_card hC.1
    omega
  · exact (kneser_contra IH hK hAB hC hmin (by omega)).elim

theorem kneser_quotient {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G] {A B : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (IH : ∀ (Q : Type u) [AddCommGroup Q] [Fintype Q] [DecidableEq Q] (A' B' : Finset Q),
      A'.Nonempty → B'.Nonempty → (A' + B').card + A'.card < (A + B).card + A.card → KneserIneq A' B')
    (hK : 2 ≤ (addStab (A + B)).card) : KneserIneq A B := by
  classical
  set K := addStab (A + B) with hKdef
  let : Fintype (G ⧸ stabSub (A + B)) := Fintype.ofFinite _
  set π : G →+ G ⧸ stabSub (A + B) := QuotientAddGroup.mk' (stabSub (A + B)) with hπ
  set A' := A.image π with hA'
  set B' := B.image π with hB'
  have hsum : A' + B' = (A + B).image π := (image_add π).symm
  have hπK : ∀ z ∈ A + B, ∀ z', π z' = π z → z' ∈ A + B := by
    intro z hz z' hzz
    have h1 : -z + z' ∈ stabSub (A + B) := (QuotientAddGroup.eq).1 hzz.symm
    have h2 := mem_addStab.1 h1 z hz
    rwa [show -z + z' + z = z' by abel] at h2
  have hstab : addStab (A' + B') = {0} := by
    ext c
    rw [mem_singleton]
    constructor
    · intro hc
      obtain ⟨g, rfl⟩ := QuotientAddGroup.mk'_surjective (stabSub (A + B)) c
      have hg : g ∈ K := by
        refine mem_addStab.2 fun z hz => ?_
        have h1 := mem_addStab.1 hc (π z) (by rw [hsum]; exact mem_image_of_mem _ hz)
        rw [hsum, ← map_add] at h1
        obtain ⟨z', hz', hzz⟩ := mem_image.1 h1
        exact hπK z' hz' (g + z) hzz.symm
      exact (QuotientAddGroup.eq_zero_iff g).2 hg
    · rintro rfl
      exact zero_mem_addStab _
  have himA : (A + K).image π = A' := by
    ext c
    simp only [hA', mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, k, hk, rfl⟩ := mem_add.1 hz
      refine ⟨x, hx, ?_⟩
      have hk0 : π k = 0 := (QuotientAddGroup.eq_zero_iff k).2 (mem_stabSub.2 hk)
      simp only [map_add, hk0, add_zero]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, mem_add.2 ⟨x, hx, 0, zero_mem_addStab _, add_zero x⟩, rfl⟩
  have himB : (B + K).image π = B' := by
    ext c
    simp only [hB', mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, k, hk, rfl⟩ := mem_add.1 hz
      refine ⟨x, hx, ?_⟩
      have hk0 : π k = 0 := (QuotientAddGroup.eq_zero_iff k).2 (mem_stabSub.2 hk)
      simp only [map_add, hk0, add_zero]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, mem_add.2 ⟨x, hx, 0, zero_mem_addStab _, add_zero x⟩, rfl⟩
  have hcA : (A + K).card = A'.card * K.card := by
    rw [card_eq_card_image_mul (addStab_subset_addStab_add A (A + B))]
    congr 1
    exact congrArg card himA
  have hcB : (B + K).card = B'.card * K.card := by
    rw [card_eq_card_image_mul (addStab_subset_addStab_add B (A + B))]
    congr 1
    exact congrArg card himB
  have hcAB : (A + B).card = (A' + B').card * K.card := by
    rw [card_eq_card_image_mul (subset_refl (addStab (A + B))), hsum]
  have hABpos := (hA.add hB).card_pos
  have hlt : (A' + B').card + A'.card < (A + B).card + A.card := by
    have h1 : A'.card ≤ A.card := card_image_le
    have h2 : (A' + B').card < (A + B).card := by
      rw [hcAB]
      have h3 : 0 < (A' + B').card := by
        rw [hcAB] at hABpos
        exact Nat.pos_of_mul_pos_right hABpos
      nlinarith
    omega
  have hIH := IH (G ⧸ stabSub (A + B)) A' B' (hA.image _) (hB.image _) hlt
  unfold KneserIneq at hIH
  rw [hstab, card_singleton, add_singleton_zero', add_singleton_zero'] at hIH
  unfold KneserIneq
  rw [hcA, hcB, hcAB]
  nlinarith

theorem kneser_aux (n : ℕ) : ∀ (G : Type u) [AddCommGroup G] [Fintype G] [DecidableEq G] (A B : Finset G),
    A.Nonempty → B.Nonempty → (A + B).card + A.card = n → KneserIneq A B := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro G _ _ _ A B hA hB hn
  by_cases hK : 2 ≤ (addStab (A + B)).card
  · exact kneser_quotient hA hB
      (fun Q _ _ _ A' B' hA' hB' hlt => IH _ (hn ▸ hlt) Q A' B' hA' hB' rfl) hK
  · have hK0 : addStab (A + B) = {0} := eq_singleton_zero_of_card_le_one (by omega)
    unfold KneserIneq
    rw [hK0, card_singleton, add_singleton_zero', add_singleton_zero']
    by_cases hA1 : A.card = 1
    · obtain ⟨a, rfl⟩ := card_eq_one.1 hA1
      rw [card_singleton_add, card_singleton]
      omega
    · obtain ⟨a, ha, a', ha', hne⟩ := one_lt_card.1 (show 1 < A.card by
        have := hA.card_pos
        omega)
      have hnot : a' - a ∉ addStab B := fun h => by
        have h1 := addStab_subset_addStab_add_right A B h
        rw [hK0, mem_singleton, sub_eq_zero] at h1
        exact hne h1.symm
      rw [mem_addStab] at hnot
      push Not at hnot
      obtain ⟨b, hb, hb'⟩ := hnot
      set t := a - b with ht
      set B' := B.image (· + t) with hB'
      have hB'card : B'.card = B.card := card_image_of_injective _ (add_left_injective t)
      have hsum' : A + B' = (A + B).image (· + t) := add_image_add_right A B t
      have hsumcard : (A + B').card = (A + B).card := by
        rw [hsum', card_image_of_injective _ (add_left_injective t)]
      have hK' : addStab (A + B') = {0} := by rw [hsum', addStab_image_add_right, hK0]
      have haB' : a ∈ A ∩ B' := mem_inter.2 ⟨ha, mem_image.2 ⟨b, hb, by rw [ht]; abel⟩⟩
      have ha'B' : a' ∉ B' := by
        intro h
        obtain ⟨y, hy, hyt⟩ := mem_image.1 h
        apply hb'
        have hy' : y = a' - a + b := by
          rw [← hyt, ht]
          abel
        rw [← hy']
        exact hy
      have hcore := kneser_core (A := A) (B := B')
        (fun A' B'' hA' hB'' hlt => IH _ (by rw [hsumcard] at hlt; omega) G A' B'' hA' hB'' rfl)
        hK' ⟨a, haB'⟩ (card_lt_card ⟨inter_subset_left, fun h => ha'B' (mem_inter.1 (h ha')).2⟩)
      rw [hB'card, hsumcard] at hcore
      exact hcore

end Kneser

open scoped Pointwise in
theorem ext_kneser {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {X Y : Finset G}
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    (X + addStab (X + Y)).card + (Y + addStab (X + Y)).card ≤
      (X + Y).card + (addStab (X + Y)).card :=
  kneser_aux _ G X Y hX hY rfl

end DGS
