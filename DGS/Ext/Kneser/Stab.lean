module

public import DGS.ExtDefs
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Coset.Card

@[expose] public section

open Finset
open scoped Pointwise

namespace DGS

section Stab

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem image_add_left_eq_self_iff {X : Finset G} {g : G} :
    X.image (g + ·) = X ↔ ∀ x ∈ X, g + x ∈ X := by
  constructor
  · intro h x hx
    rw [← h]
    exact mem_image_of_mem _ hx
  · intro h
    refine eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
      exact h x hx
    · rw [card_image_of_injective _ (add_right_injective g)]

theorem mem_addStab {X : Finset G} {g : G} : g ∈ addStab X ↔ ∀ x ∈ X, g + x ∈ X := by
  unfold addStab
  rw [mem_filter, image_add_left_eq_self_iff]
  simp

theorem zero_mem_addStab (X : Finset G) : (0 : G) ∈ addStab X :=
  mem_addStab.2 fun x hx => by simpa using hx

theorem addStab_nonempty (X : Finset G) : (addStab X).Nonempty := ⟨0, zero_mem_addStab X⟩

theorem add_mem_addStab {X : Finset G} {g h : G} (hg : g ∈ addStab X) (hh : h ∈ addStab X) :
    g + h ∈ addStab X :=
  mem_addStab.2 fun x hx => by
    rw [add_assoc]
    exact mem_addStab.1 hg _ (mem_addStab.1 hh x hx)

theorem neg_mem_addStab {X : Finset G} {g : G} (hg : g ∈ addStab X) : -g ∈ addStab X := by
  have himg : X.image (g + ·) = X := image_add_left_eq_self_iff.2 (mem_addStab.1 hg)
  refine mem_addStab.2 fun x hx => ?_
  rw [← himg] at hx
  obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
  simpa using hy

theorem sub_mem_addStab {X : Finset G} {g h : G} (hg : g ∈ addStab X) (hh : h ∈ addStab X) :
    g - h ∈ addStab X := by
  rw [sub_eq_add_neg]
  exact add_mem_addStab hg (neg_mem_addStab hh)

def stabSub (X : Finset G) : AddSubgroup G where
  carrier := {g | g ∈ addStab X}
  zero_mem' := zero_mem_addStab X
  add_mem' := add_mem_addStab
  neg_mem' := neg_mem_addStab

theorem mem_stabSub {X : Finset G} {g : G} : g ∈ stabSub X ↔ g ∈ addStab X := Iff.rfl

theorem add_addStab (X : Finset G) : X + addStab X = X := by
  ext z
  rw [mem_add]
  constructor
  · rintro ⟨x, hx, g, hg, rfl⟩
    rw [add_comm]
    exact mem_addStab.1 hg x hx
  · intro hz
    exact ⟨z, hz, 0, zero_mem_addStab X, add_zero z⟩

theorem add_addStab_of_subset {X Y : Finset G} (h : addStab Y ⊆ addStab X) : X + addStab Y = X := by
  refine Subset.antisymm ?_ ?_
  · intro z hz
    obtain ⟨x, hx, g, hg, rfl⟩ := mem_add.1 hz
    rw [add_comm]
    exact mem_addStab.1 (h hg) x hx
  · intro z hz
    exact mem_add.2 ⟨z, hz, 0, zero_mem_addStab Y, add_zero z⟩

theorem addStab_subset_addStab_add (X Y : Finset G) : addStab Y ⊆ addStab (X + addStab Y) := by
  intro g hg
  refine mem_addStab.2 fun z hz => ?_
  obtain ⟨x, hx, k, hk, rfl⟩ := mem_add.1 hz
  refine mem_add.2 ⟨x, hx, g + k, add_mem_addStab hg hk, ?_⟩
  abel

theorem addStab_subset_addStab_add_right (A B : Finset G) : addStab B ⊆ addStab (A + B) := by
  intro g hg
  refine mem_addStab.2 fun z hz => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hz
  refine mem_add.2 ⟨a, ha, g + b, mem_addStab.1 hg b hb, ?_⟩
  abel

theorem addStab_empty : addStab (∅ : Finset G) = univ := by
  ext g
  simp [mem_addStab]

theorem addStab_image_add_right (X : Finset G) (t : G) : addStab (X.image (· + t)) = addStab X := by
  ext g
  rw [mem_addStab, mem_addStab]
  constructor
  · intro h x hx
    have h1 := h (x + t) (mem_image_of_mem _ hx)
    obtain ⟨y, hy, hyx⟩ := mem_image.1 h1
    have : y = g + x := by
      rw [← add_assoc] at hyx
      exact add_right_cancel hyx
    rw [← this]
    exact hy
  · intro h z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
    exact mem_image.2 ⟨g + x, h x hx, by abel⟩

omit [Fintype G] in
theorem add_image_add_right (A B : Finset G) (t : G) :
    A + B.image (· + t) = (A + B).image (· + t) := by
  ext z
  simp only [mem_add, mem_image]
  constructor
  · rintro ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by abel⟩
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨a, ha, b + t, ⟨b, hb, rfl⟩, by abel⟩

omit [Fintype G] in
theorem add_singleton_zero' (X : Finset G) : X + {0} = X := by
  ext z
  simp [mem_add]

def coset (Y : Finset G) (x : G) : Finset G := (addStab Y).image (x + ·)

theorem card_coset (Y : Finset G) (x : G) : (coset Y x).card = (addStab Y).card :=
  card_image_of_injective _ (add_right_injective x)

theorem mem_coset {Y : Finset G} {x z : G} : z ∈ coset Y x ↔ z - x ∈ addStab Y := by
  unfold coset
  rw [mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa using hk
  · intro h
    exact ⟨z - x, h, by abel⟩

theorem self_mem_coset (Y : Finset G) (x : G) : x ∈ coset Y x := by
  rw [mem_coset, sub_self]
  exact zero_mem_addStab Y

theorem card_eq_card_image_mul {X Y : Finset G} [DecidableEq (G ⧸ stabSub Y)]
    (h : addStab Y ⊆ addStab X) :
    X.card = (X.image (QuotientAddGroup.mk' (stabSub Y))).card * (addStab Y).card := by
  rw [card_eq_sum_card_image (QuotientAddGroup.mk' (stabSub Y)) X]
  refine sum_const_nat fun c hc => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := mem_image.1 hc
  have hfib : X.filter (fun x => QuotientAddGroup.mk' (stabSub Y) x = QuotientAddGroup.mk' (stabSub Y) x₀) =
      (addStab Y).image (x₀ + ·) := by
    ext x
    rw [mem_filter, mem_image]
    simp only [QuotientAddGroup.mk'_apply]
    constructor
    · rintro ⟨-, hxc⟩
      refine ⟨-x₀ + x, ?_, by abel⟩
      exact (QuotientAddGroup.eq).1 hxc.symm
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [add_comm]
        exact mem_addStab.1 (h hk) x₀ hx₀
      · refine ((QuotientAddGroup.eq).2 ?_).symm
        rw [mem_stabSub]
        simpa using hk
  rw [hfib, card_image_of_injective _ (add_right_injective x₀)]

theorem card_dvd_card_of_subset {X Y : Finset G} [DecidableEq (G ⧸ stabSub Y)]
    (h : addStab Y ⊆ addStab X) : (addStab Y).card ∣ X.card :=
  ⟨_, (card_eq_card_image_mul h).trans (mul_comm _ _)⟩

end Stab

end DGS
