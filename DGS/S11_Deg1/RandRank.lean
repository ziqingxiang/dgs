module

public import DGS.S11_Deg1.Replace
public import DGS.S03_Prelim.SignVectors

@[expose] public section

open Finset Module

namespace DGS

section Independence

theorem prob_pi_forall {ι Y : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y] (A : ι → Y → Prop) :
    prob (fun y : ι → Y => ∀ i, A i (y i)) = ∏ i, prob (A i) := by
  classical
  unfold prob
  have h1 : Nat.card {y : ι → Y // ∀ i, A i (y i)} = ∏ i, Nat.card {b : Y // A i b} := by
    rw [Nat.card_congr (Equiv.subtypePiEquivPi), Nat.card_pi]
  have h2 : Nat.card (ι → Y) = ∏ _i : ι, Nat.card Y := Nat.card_pi
  rw [h1, h2]
  push_cast
  rw [Finset.prod_div_distrib]

theorem prob_forall_not_mem_le {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (I : Finset X) (A : (X → Y) → X → Y → Prop)
    (hA : ∀ x x' : X → Y, (∀ i ∈ I, x i = x' i) → ∀ j v, A x j v ↔ A x' j v)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ x j, prob (A x j) ≤ ε) :
    prob (fun x : X → Y => ∀ j ∉ I, A x j (x j)) ≤ ε ^ (Fintype.card X - I.card) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun j : X => j ∈ I) (fun _ : X => Y)
  rw [← prob_equiv e.symm]
  refine prob_le_of_forall_fst (fun xI => ?_) (pow_nonneg hε0 _)
  set x0 : X → Y := e.symm (xI, fun _ => Classical.arbitrary Y) with hx0
  have hagree : ∀ xc : {j // j ∉ I} → Y, ∀ i ∈ I, e.symm (xI, xc) i = x0 i := by
    intro xc i hi
    simp [hx0, e, Equiv.piEquivPiSubtypeProd, hi]
  have hcongr : ∀ xc : {j // j ∉ I} → Y,
      (∀ j ∉ I, A (e.symm (xI, xc)) j (e.symm (xI, xc) j)) ↔ ∀ j : {j // j ∉ I}, A x0 j (xc j) := by
    intro xc
    constructor
    · intro h j
      have h1 := h j.1 j.2
      have h2 : e.symm (xI, xc) j.1 = xc j := by simp [e, Equiv.piEquivPiSubtypeProd, j.2]
      rw [h2] at h1
      exact (hA _ _ (hagree xc) j.1 (xc j)).1 h1
    · intro h j hj
      have h2 : e.symm (xI, xc) j = xc ⟨j, hj⟩ := by simp [e, Equiv.piEquivPiSubtypeProd, hj]
      rw [h2]
      exact (hA _ _ (hagree xc) j (xc ⟨j, hj⟩)).2 (h ⟨j, hj⟩)
  rw [prob_congr hcongr, prob_pi_forall]
  calc ∏ j : {j // j ∉ I}, prob (A x0 j) ≤ ∏ _j : {j // j ∉ I}, ε :=
        Finset.prod_le_prod₀ (fun j _ => prob_nonneg _) (fun j _ => hε _ _)
    _ = ε ^ (Fintype.card X - I.card) := by
        rw [prod_const, card_univ, Fintype.card_subtype_compl, Fintype.card_coe]

end Independence

theorem prob_curry_eq {k n : ℕ} (P : (Fin k → Fin n → Bool) → Prop) :
    prob (fun x : Fin k × Fin n → Bool => P (fun a c => x (a, c))) = prob P :=
  prob_equiv (Equiv.curry (Fin k) (Fin n) Bool) P

section LinAlg

variable {F : Type*} [Field F]

theorem finrank_comap_le_add {V W : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] (f : V →ₗ[F] W) (S : Submodule F W) :
    finrank F (S.comap f) ≤ finrank F S + finrank F (LinearMap.ker f) := by
  have hmaps : ∀ x ∈ S.comap f, f x ∈ S := fun x hx => hx
  let g := f.restrict hmaps
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 : finrank F (LinearMap.range g) ≤ finrank F S := Submodule.finrank_le _
  let ι : LinearMap.ker g →ₗ[F] V := (S.comap f).subtype ∘ₗ (LinearMap.ker g).subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hrange : LinearMap.range ι ≤ LinearMap.ker f := by
    rintro _ ⟨x, rfl⟩
    have hx : g x = 0 := x.2
    exact congrArg Subtype.val hx
  have h3 : finrank F (LinearMap.ker g) ≤ finrank F (LinearMap.ker f) := by
    rw [← LinearMap.finrank_range_of_inj hι]
    exact Submodule.finrank_mono hrange
  omega

theorem exists_finset_span_eq {M ι : Type*} [AddCommGroup M] [Module F M] [Fintype ι] [DecidableEq ι]
    (v : ι → M) : ∃ I : Finset ι, I.card = finrank F (Submodule.span F (Set.range v)) ∧
      ∀ j, v j ∈ Submodule.span F (v '' (I : Set ι)) := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' F v
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  classical
  have himg : v '' ((Finset.univ.image a : Finset ι) : Set ι) = Set.range (v ∘ a) := by
    ext y
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image, Set.mem_range,
      Function.comp_apply]
    constructor
    · rintro ⟨i, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨a b, ⟨b, rfl⟩, rfl⟩
  refine ⟨Finset.univ.image a, ?_, fun j => ?_⟩
  · rw [Finset.card_image_of_injective _ ha, Finset.card_univ, ← hspan, finrank_span_eq_card hli]
  · rw [himg, hspan]
    exact Submodule.subset_span ⟨j, rfl⟩

end LinAlg

section Affine

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]

theorem prob_affine_mem_le {N : ℕ} (hF : (1 : F) ≠ -1) (Ψ : (Fin N → F) →ₗ[F] M) (c : M)
    (S : Submodule F M) :
    prob (fun s : Fin N → Bool => Ψ (twoValued (1 : F) (-1) s) + c ∈ S) ≤
      (2 : ℝ) ^ finrank F S / 2 ^ finrank F (LinearMap.range Ψ) := by
  classical
  by_cases hex : ∃ s0 : Fin N → Bool, Ψ (twoValued (1 : F) (-1) s0) + c ∈ S
  · obtain ⟨s0, hs0⟩ := hex
    set v0 := twoValued (1 : F) (-1) s0 with hv0
    set V := S.comap Ψ with hV
    have hiff : ∀ s : Fin N → Bool,
        Ψ (twoValued (1 : F) (-1) s) + c ∈ S ↔ twoValued (1 : F) (-1) s - v0 ∈ V := by
      intro s
      rw [hV, Submodule.mem_comap, map_sub]
      constructor
      · intro h
        have := S.sub_mem h hs0
        rwa [add_sub_add_right_eq_sub] at this
      · intro h
        have := S.add_mem h hs0
        rwa [show Ψ (twoValued (1 : F) (-1) s) - Ψ v0 + (Ψ v0 + c) = Ψ (twoValued (1 : F) (-1) s) + c by
          abel] at this
    have hcount := lem_odlyzko (1 : F) (-1) hF V v0
    have hdim : finrank F V + finrank F (LinearMap.range Ψ) ≤ finrank F S + N := by
      have h1 : finrank F V ≤ finrank F S + finrank F (LinearMap.ker Ψ) := finrank_comap_le_add Ψ S
      have h2 := LinearMap.finrank_range_add_finrank_ker Ψ
      rw [Module.finrank_fin_fun] at h2
      omega
    rw [prob_congr hiff]
    unfold prob
    have hN : Nat.card (Fin N → Bool) = 2 ^ N := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [hN, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (Nat.card {s : Fin N → Bool // twoValued (1 : F) (-1) s - v0 ∈ V} : ℝ) ≤
        (2 : ℝ) ^ finrank F V := by exact_mod_cast hcount
    have h2 : (2 : ℝ) ^ finrank F V * 2 ^ finrank F (LinearMap.range Ψ) ≤ 2 ^ finrank F S * 2 ^ N := by
      rw [← pow_add, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) hdim
    push_cast
    calc (Nat.card {s : Fin N → Bool // twoValued (1 : F) (-1) s - v0 ∈ V} : ℝ) *
          2 ^ finrank F (LinearMap.range Ψ) ≤ 2 ^ finrank F V * 2 ^ finrank F (LinearMap.range Ψ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 2 ^ finrank F S * 2 ^ N := h2
  · push Not at hex
    rw [prob_congr (Q := fun _ => False) fun s => ⟨fun h => hex s h, False.elim⟩, prob_false]
    positivity

theorem prob_finrank_span_le {N k r : ℕ} (hF : (1 : F) ≠ -1) (Ψ : (Fin N → F) →ₗ[F] M) (c : Fin k → M)
    (hr : r ≤ finrank F (LinearMap.range Ψ)) :
    prob (fun x : Fin k → Fin N → Bool =>
        finrank F (Submodule.span F (Set.range fun i => Ψ (twoValued (1 : F) (-1) (x i)) + c i)) ≤ r) ≤
      2 ^ k * ((2 : ℝ) ^ r / 2 ^ finrank F (LinearMap.range Ψ)) ^ (k - r) := by
  classical
  set ρ := finrank F (LinearMap.range Ψ) with hρ
  set ε : ℝ := (2 : ℝ) ^ r / 2 ^ ρ with hε
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) hr
  set z : (Fin k → Fin N → Bool) → Fin k → M := fun x i => Ψ (twoValued (1 : F) (-1) (x i)) + c i
    with hz
  have hsub : ∀ x : Fin k → Fin N → Bool,
      finrank F (Submodule.span F (Set.range (z x))) ≤ r →
      ∃ I ∈ (univ : Finset (Fin k)).powerset, I.card ≤ r ∧
        ∀ j ∉ I, z x j ∈ Submodule.span F (z x '' (I : Set (Fin k))) := by
    intro x hx
    obtain ⟨I, hIcard, hI⟩ := exists_finset_span_eq (F := F) (z x)
    exact ⟨I, mem_powerset.2 (subset_univ _), hIcard ▸ hx, fun j _ => hI j⟩
  have hone : ∀ I : Finset (Fin k), prob (fun x : Fin k → Fin N → Bool => I.card ≤ r ∧
      ∀ j ∉ I, z x j ∈ Submodule.span F (z x '' (I : Set (Fin k)))) ≤ ε ^ (k - r) := by
    intro I
    by_cases hI : I.card ≤ r
    · have h1 : prob (fun x : Fin k → Fin N → Bool =>
          ∀ j ∉ I, z x j ∈ Submodule.span F (z x '' (I : Set (Fin k)))) ≤ ε ^ (k - I.card) := by
        have := prob_forall_not_mem_le (X := Fin k) (Y := Fin N → Bool) I
          (fun x j v => Ψ (twoValued (1 : F) (-1) v) + c j ∈ Submodule.span F (z x '' (I : Set (Fin k))))
          (fun x x' hxx' j v => by
            have himg : z x '' (I : Set (Fin k)) = z x' '' (I : Set (Fin k)) := by
              refine Set.image_congr fun i hi => ?_
              simp only [hz]
              rw [hxx' i hi]
            rw [himg])
          hε0 (fun x j => by
            refine (prob_affine_mem_le hF Ψ (c j) _).trans ?_
            rw [hε]
            refine div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) ?_) (by positivity)
            have h2 : (Finset.image (z x) I : Set M) = z x '' (I : Set (Fin k)) := Finset.coe_image
            have h3 := finrank_span_finset_le_card (R := F) (Finset.image (z x) I)
            rw [h2] at h3
            exact h3.trans (Finset.card_image_le.trans hI))
        rwa [Fintype.card_fin] at this
      refine (prob_mono fun x hx => hx.2).trans (h1.trans ?_)
      exact pow_le_pow_of_le_one hε0 hε1 (by omega)
    · rw [prob_congr (Q := fun _ => False) fun x => ⟨fun h => hI h.1, False.elim⟩, prob_false]
      positivity
  calc prob (fun x : Fin k → Fin N → Bool =>
        finrank F (Submodule.span F (Set.range fun i => Ψ (twoValued (1 : F) (-1) (x i)) + c i)) ≤ r)
      ≤ prob (fun x : Fin k → Fin N → Bool => ∃ I ∈ (univ : Finset (Fin k)).powerset, I.card ≤ r ∧
          ∀ j ∉ I, z x j ∈ Submodule.span F (z x '' (I : Set (Fin k)))) := prob_mono hsub
    _ ≤ ∑ I ∈ (univ : Finset (Fin k)).powerset, prob (fun x : Fin k → Fin N → Bool => I.card ≤ r ∧
          ∀ j ∉ I, z x j ∈ Submodule.span F (z x '' (I : Set (Fin k)))) := prob_exists_le_sum _ _
    _ ≤ ∑ _I ∈ (univ : Finset (Fin k)).powerset, ε ^ (k - r) := sum_le_sum fun I _ => hone I
    _ = 2 ^ k * ε ^ (k - r) := by
        rw [sum_const, card_powerset, card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

theorem prob_setFinrank_le {N k r : ℕ} (hF : (1 : F) ≠ -1) (Ψ : (Fin N → F) →ₗ[F] M) (c : Fin k → M)
    (hr : r ≤ finrank F (LinearMap.range Ψ)) :
    prob (fun x : Fin k → Fin N → Bool =>
        (Set.range fun i => Ψ (twoValued (1 : F) (-1) (x i)) + c i).finrank F ≤ r) ≤
      2 ^ k * ((2 : ℝ) ^ r / 2 ^ finrank F (LinearMap.range Ψ)) ^ (k - r) :=
  prob_finrank_span_le hF Ψ c hr

theorem prob_setFinrank_le' {N k r ρ : ℕ} (hF : (1 : F) ≠ -1) (Ψ : (Fin N → F) →ₗ[F] M) (c : Fin k → M)
    (hρ : ρ ≤ finrank F (LinearMap.range Ψ)) (hr : r ≤ ρ) :
    prob (fun x : Fin k → Fin N → Bool =>
        (Set.range fun i => Ψ (twoValued (1 : F) (-1) (x i)) + c i).finrank F ≤ r) ≤
      2 ^ k * ((2 : ℝ) ^ r / 2 ^ ρ) ^ (k - r) := by
  refine (prob_setFinrank_le hF Ψ c (hr.trans hρ)).trans ?_
  gcongr
  norm_num

theorem prob_setFinrank_sign_le {N k r : ℕ} (hF : (1 : F) ≠ -1) (hr : r ≤ N) :
    prob (fun x : Fin k → Fin N → Bool => (Set.range fun i => twoValued (1 : F) (-1) (x i)).finrank F ≤ r) ≤
      2 ^ k * ((2 : ℝ) ^ r / 2 ^ N) ^ (k - r) := by
  have hrid : finrank F (LinearMap.range (LinearMap.id : (Fin N → F) →ₗ[F] _)) = N := by
    rw [LinearMap.range_id, finrank_top, Module.finrank_fin_fun]
  have h := prob_setFinrank_le (k := k) (r := r) hF (LinearMap.id : (Fin N → F) →ₗ[F] _) (fun _ => 0)
    (by rw [hrid]; exact hr)
  rw [hrid] at h
  simpa using h

end Affine

end DGS
