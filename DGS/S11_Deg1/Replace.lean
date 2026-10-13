module

public import DGS.S03_Prelim.SuppD

@[expose] public section

open Finset Matrix

namespace DGS

variable {m : ℕ} {B : Type*} [Fintype B]

open Classical in
noncomputable def replace (β : B → Pairs m) (hβ : Function.Injective β) (ω : Pairs m → Bool)
    (x : B → Bool) : Pairs m → Bool := fun q =>
  if h : q ∈ Set.range β then x ((Equiv.ofInjective β hβ).symm ⟨q, h⟩) else ω q

variable (β : B → Pairs m) (hβ : Function.Injective β)

theorem replace_apply_mem (ω : Pairs m → Bool) (x : B → Bool) (b : B) :
    replace β hβ ω x (β b) = x b := by
  unfold replace
  rw [dite_eq_left ⟨b, rfl⟩]
  congr 1
  apply (Equiv.ofInjective β hβ).injective
  rw [Equiv.apply_symm_apply]
  rfl

theorem replace_apply_not_mem (ω : Pairs m → Bool) (x : B → Bool) {q : Pairs m}
    (hq : q ∉ Set.range β) : replace β hβ ω x q = ω q := by
  unfold replace
  rw [dite_eq_right hq]

theorem comp_replace (ω : Pairs m → Bool) (x : B → Bool) : replace β hβ ω x ∘ β = x := by
  funext b
  exact replace_apply_mem β hβ ω x b

theorem replace_replace (ω : Pairs m → Bool) (x : B → Bool) :
    replace β hβ (replace β hβ ω x) (ω ∘ β) = ω := by
  funext q
  by_cases hq : q ∈ Set.range β
  · obtain ⟨b, rfl⟩ := hq
    rw [replace_apply_mem]
    rfl
  · rw [replace_apply_not_mem β hβ _ _ hq, replace_apply_not_mem β hβ _ _ hq]

noncomputable def replaceSwap : (Pairs m → Bool) × (B → Bool) ≃ (Pairs m → Bool) × (B → Bool) :=
  Function.Involutive.toPerm (fun y => (replace β hβ y.1 y.2, y.1 ∘ β)) fun y => by
    obtain ⟨ω, x⟩ := y
    simp only [replace_replace, comp_replace]

theorem prob_eq_prob_replace (P : (Pairs m → Bool) → Prop) :
    prob P = prob (fun y : (Pairs m → Bool) × (B → Bool) => P (replace β hβ y.1 y.2)) := by
  rw [← prob_fst (Ω' := B → Bool) P]
  exact (prob_equiv (replaceSwap β hβ) (fun y => P y.1)).symm

theorem prob_and_le_of_replace {E G : (Pairs m → Bool) → Prop} {c : ℝ} (hc : 0 ≤ c)
    (hG : ∀ ω x, G (replace β hβ ω x) ↔ G ω)
    (h : ∀ ω, G ω → prob (fun x : B → Bool => E (replace β hβ ω x)) ≤ c) :
    prob (fun ω => E ω ∧ G ω) ≤ c := by
  rw [prob_eq_prob_replace β hβ]
  refine prob_le_of_forall_fst (fun ω => ?_) hc
  by_cases hω : G ω
  · refine le_trans (prob_mono fun x hx => hx.1) (h ω hω)
  · rw [prob_congr (Q := fun _ => False) fun x => ⟨fun hx => hω ((hG ω x).1 hx.2), False.elim⟩,
      prob_false]
    exact hc

include hβ in
theorem prob_comp_injective (P : (B → Bool) → Prop) :
    prob (fun ω : Pairs m → Bool => P (ω ∘ β)) = prob P := by
  rw [prob_eq_prob_replace β hβ]
  simp only [comp_replace]
  exact prob_snd (Ω := Pairs m → Bool) P

theorem seidelOf_replace_of_not_mem (ω : Pairs m → Bool) (x : B → Bool) {u v : Fin m} (huv : u ≠ v)
    (hq : sortPair u v huv ∉ Set.range β) :
    seidelOf (replace β hβ ω x) u v = seidelOf ω u v := by
  unfold seidelOf
  rw [symOf_sortPair _ _ _ huv, symOf_sortPair _ _ _ huv, replace_apply_not_mem β hβ _ _ hq]

theorem seidelOf_replace_diag (ω : Pairs m → Bool) (x : B → Bool) (u : Fin m) :
    seidelOf (replace β hβ ω x) u u = seidelOf ω u u := by
  unfold seidelOf symOf
  simp

theorem seidelOf_replace_mem (ω : Pairs m → Bool) (x : B → Bool) {u v : Fin m} (huv : u ≠ v) (b : B)
    (hb : β b = sortPair u v huv) :
    seidelOf (replace β hβ ω x) u v = if x b then 1 else -1 := by
  unfold seidelOf
  rw [symOf_sortPair _ _ _ huv, ← hb, replace_apply_mem]

end DGS
