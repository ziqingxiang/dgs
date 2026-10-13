module

public import DGS.S11_Deg1.PencilLin
public import DGS.S11_Deg1.Replace
public import DGS.S03_Prelim.Apriori

@[expose] public section

open Finset Matrix Module

namespace DGS

theorem sortPair_eq_imp {m : ℕ} {u v u' v' : Fin m} (h : u ≠ v) (h' : u' ≠ v') :
    sortPair u v h = sortPair u' v' h' → (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
  intro he
  unfold sortPair at he
  split_ifs at he with h1 h2 h2 <;> simp only [Subtype.mk.injEq, Prod.mk.injEq] at he <;> tauto

variable {m : ℕ}

noncomputable def eRcOf (R : Finset (Fin m)) : Fin Rᶜ.card → Fin m := Rᶜ.orderEmbOfFin rfl

noncomputable def eUOf (U : Finset (Fin m)) : Fin U.card → Fin m := U.orderEmbOfFin rfl

noncomputable def e1Of (R : Finset (Fin m)) (a : Fin (R.card / 2)) : Fin m :=
  R.orderEmbOfFin rfl ⟨a.1, by have := a.2; omega⟩

noncomputable def e2Of (R : Finset (Fin m)) (c : Fin (R.card / 2)) : Fin m :=
  R.orderEmbOfFin rfl ⟨R.card / 2 + c.1, by have := c.2; omega⟩

section Enum

variable (R U : Finset (Fin m))

theorem eRcOf_injective : Function.Injective (eRcOf R) := (Rᶜ.orderEmbOfFin rfl).injective

theorem eUOf_injective : Function.Injective (eUOf U) := (U.orderEmbOfFin rfl).injective

theorem not_mem_iff_eRcOf (j : Fin m) : j ∉ R ↔ j ∈ Set.range (eRcOf R) := by
  rw [eRcOf, Finset.range_orderEmbOfFin, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe]

theorem mem_iff_eUOf (j : Fin m) : j ∈ U ↔ j ∈ Set.range (eUOf U) := by
  rw [eUOf, Finset.range_orderEmbOfFin, Finset.mem_coe]

theorem eRcOf_not_mem (a : Fin Rᶜ.card) : eRcOf R a ∉ R :=
  (not_mem_iff_eRcOf R _).2 ⟨a, rfl⟩

theorem eUOf_mem (b : Fin U.card) : eUOf U b ∈ U := (mem_iff_eUOf U _).2 ⟨b, rfl⟩

theorem e1Of_mem (a : Fin (R.card / 2)) : e1Of R a ∈ R := Finset.orderEmbOfFin_mem _ _ _

theorem e2Of_mem (c : Fin (R.card / 2)) : e2Of R c ∈ R := Finset.orderEmbOfFin_mem _ _ _

theorem e1Of_injective : Function.Injective (e1Of R) := by
  intro a a' h
  have := (R.orderEmbOfFin rfl).injective h
  simp only [Fin.mk.injEq] at this
  exact Fin.ext this

theorem e2Of_injective : Function.Injective (e2Of R) := by
  intro c c' h
  have := (R.orderEmbOfFin rfl).injective h
  simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at this
  exact Fin.ext this

theorem e1Of_ne_e2Of (a c : Fin (R.card / 2)) : e1Of R a ≠ e2Of R c := by
  intro h
  have := (R.orderEmbOfFin rfl).injective h
  simp only [Fin.mk.injEq] at this
  have := a.2
  omega

theorem e2Of_ne_eRcOf (c : Fin (R.card / 2)) (a : Fin Rᶜ.card) : e2Of R c ≠ eRcOf R a := by
  intro h
  exact eRcOf_not_mem R a (h ▸ e2Of_mem R c)

end Enum

section Blocks

variable (R U : Finset (Fin m))

noncomputable def blk1 (ac : Fin (R.card / 2) × Fin (R.card / 2)) : Pairs m :=
  sortPair (e1Of R ac.1) (e2Of R ac.2) (e1Of_ne_e2Of R ac.1 ac.2)

noncomputable def blk2 (ca : Fin (R.card / 2) × Fin Rᶜ.card) : Pairs m :=
  sortPair (e2Of R ca.1) (eRcOf R ca.2) (e2Of_ne_eRcOf R ca.1 ca.2)

noncomputable def blkU (q : Pairs U.card) : Pairs m :=
  sortPair (eUOf U q.1.1) (eUOf U q.1.2) ((eUOf_injective U).ne (ne_of_lt q.2))

theorem blk1_injective : Function.Injective (blk1 R) := by
  rintro ⟨a, c⟩ ⟨a', c'⟩ h
  rcases sortPair_eq_imp _ _ h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2
    rw [e1Of_injective R h1, e2Of_injective R h2]
  · exact absurd h1 (e1Of_ne_e2Of R a c')

theorem blk2_injective : Function.Injective (blk2 R) := by
  rintro ⟨c, a⟩ ⟨c', a'⟩ h
  rcases sortPair_eq_imp _ _ h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2
    rw [e2Of_injective R h1, eRcOf_injective R h2]
  · exact absurd h1 (e2Of_ne_eRcOf R c a')

theorem blkU_injective : Function.Injective (blkU U) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨i', j'⟩, hij'⟩ h
  rcases sortPair_eq_imp _ _ h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 := eUOf_injective U h1
    have e2 := eUOf_injective U h2
    simp only at e1 e2
    subst e1 e2
    rfl
  · have e1 := eUOf_injective U h1
    have e2 := eUOf_injective U h2
    simp only at e1 e2 hij hij'
    subst e1 e2
    exact absurd (hij.trans hij') (lt_irrefl _)

end Blocks

section Entries

variable (R U : Finset (Fin m))

def IsBlk1 (u v : Fin m) : Prop :=
  ∃ a c : Fin (R.card / 2), (u = e1Of R a ∧ v = e2Of R c) ∨ (u = e2Of R c ∧ v = e1Of R a)

theorem seidelOf_replace1_of (ω : Pairs m → Bool) (x : Fin (R.card / 2) × Fin (R.card / 2) → Bool)
    {u v : Fin m} (huv : ¬ IsBlk1 R u v) :
    seidelOf (replace (blk1 R) (blk1_injective R) ω x) u v = seidelOf ω u v := by
  by_cases h : u = v
  · subst h
    exact seidelOf_replace_diag _ _ _ _ _
  · refine seidelOf_replace_of_not_mem _ _ _ _ h ?_
    rintro ⟨⟨a, c⟩, hac⟩
    apply huv
    rcases sortPair_eq_imp _ _ hac with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a, c, Or.inl ⟨h1.symm, h2.symm⟩⟩
    · exact ⟨a, c, Or.inr ⟨h2.symm, h1.symm⟩⟩

theorem seidelOf_replace1_blk (ω : Pairs m → Bool) (x : Fin (R.card / 2) × Fin (R.card / 2) → Bool)
    (a c : Fin (R.card / 2)) :
    seidelOf (replace (blk1 R) (blk1_injective R) ω x) (e1Of R a) (e2Of R c) = if x (a, c) then 1 else -1 :=
  seidelOf_replace_mem _ _ _ _ (e1Of_ne_e2Of R a c) (a, c) rfl

theorem not_isBlk1_of_not_mem_left {u : Fin m} (hu : u ∉ R) (v : Fin m) : ¬ IsBlk1 R u v := by
  rintro ⟨a, c, ⟨h1, -⟩ | ⟨h1, -⟩⟩
  · exact hu (h1 ▸ e1Of_mem R a)
  · exact hu (h1 ▸ e2Of_mem R c)

theorem not_isBlk1_of_not_mem_right (u : Fin m) {v : Fin m} (hv : v ∉ R) : ¬ IsBlk1 R u v := by
  rintro ⟨a, c, ⟨-, h2⟩ | ⟨-, h2⟩⟩
  · exact hv (h2 ▸ e2Of_mem R c)
  · exact hv (h2 ▸ e1Of_mem R a)

theorem not_isBlk1_e2Of (c c' : Fin (R.card / 2)) : ¬ IsBlk1 R (e2Of R c) (e2Of R c') := by
  rintro ⟨a, c'', ⟨h1, -⟩ | ⟨-, h2⟩⟩
  · exact e1Of_ne_e2Of R a c h1.symm
  · exact e1Of_ne_e2Of R a c' h2.symm

theorem not_isBlk1_e1Of_of (a : Fin (R.card / 2)) {l : Fin m} (hl : ∀ c, l ≠ e2Of R c) :
    ¬ IsBlk1 R (e1Of R a) l := by
  rintro ⟨a', c, ⟨-, h2⟩ | ⟨h1, -⟩⟩
  · exact hl c h2
  · exact e1Of_ne_e2Of R a c h1

theorem seidelOf_replace2 (ω : Pairs m → Bool) (x : Fin (R.card / 2) × Fin Rᶜ.card → Bool)
    (c : Fin (R.card / 2)) (a : Fin Rᶜ.card) :
    seidelOf (replace (blk2 R) (blk2_injective R) ω x) (e2Of R c) (eRcOf R a) = if x (c, a) then 1 else -1 :=
  seidelOf_replace_mem _ _ _ _ (e2Of_ne_eRcOf R c a) (c, a) rfl

theorem seidelOf_eUOf (ω : Pairs m → Bool) (b b' : Fin U.card) :
    seidelOf ω (eUOf U b) (eUOf U b') = seidelOf (ω ∘ blkU U) b b' := by
  by_cases h : b = b'
  · subst h
    unfold seidelOf symOf
    simp
  · unfold seidelOf
    rw [symOf_sortPair _ _ _ ((eUOf_injective U).ne h), symOf_sortPair _ _ _ h]
    simp only [Function.comp_apply]
    congr 2
    unfold blkU
    rcases lt_or_gt_of_ne h with h' | h'
    · rw [sortPair_of_lt h']
    · rw [sortPair_comm h, sortPair_of_lt h', sortPair_comm]

end Entries

section KofSec

variable {p : ℕ} [Fact p.Prime]

def QAm {F : Type*} [Field F] (b0 b1 : F) (A : Matrix (Fin m) (Fin m) F) : Matrix (Fin m) (Fin m) F :=
  A * A + b1 • A + b0 • (1 : Matrix (Fin m) (Fin m) F)

def PAm {F : Type*} [Field F] (a0 a1 : F) (A : Matrix (Fin m) (Fin m) F) : Matrix (Fin m) (Fin m) F :=
  a1 • A + a0 • (1 : Matrix (Fin m) (Fin m) F)

variable (p) (b0 b1 a0 a1 : ZMod p) (U R : Finset (Fin m))

noncomputable def Kof (ω : Pairs m → Bool) : Matrix (Fin m) (Fin Rᶜ.card ⊕ Fin U.card) (ZMod p) :=
  Kmat (QAm b0 b1 (modP p (seidelOf ω))) (PAm a0 a1 (modP p (seidelOf ω))) (eRcOf R) (eUOf U)

noncomputable def Wrow (ω : Pairs m → Bool) (c : Fin (R.card / 2)) : Fin Rᶜ.card → ZMod p :=
  fun a => modP p (seidelOf ω) (e2Of R c) (eRcOf R a)

noncomputable def Wvec (ω : Pairs m → Bool) (c : Fin (R.card / 2)) : Fin Rᶜ.card ⊕ Fin U.card → ZMod p :=
  Sum.elim (Wrow p R ω c) 0

omit [Fact (Nat.Prime p)] in
theorem modP_replace1_of (ω : Pairs m → Bool) (x : Fin (R.card / 2) × Fin (R.card / 2) → Bool)
    {u v : Fin m} (huv : ¬ IsBlk1 R u v) :
    modP p (seidelOf (replace (blk1 R) (blk1_injective R) ω x)) u v = modP p (seidelOf ω) u v := by
  simp only [modP, map_apply, seidelOf_replace1_of R ω x huv]

theorem Kof_replace_row (hRU : Disjoint R U) (ω : Pairs m → Bool)
    (x : Fin (R.card / 2) × Fin (R.card / 2) → Bool) (a : Fin (R.card / 2)) :
    Kof p b0 b1 a0 a1 U R (replace (blk1 R) (blk1_injective R) ω x) (e1Of R a) =
      Fintype.linearCombination (ZMod p) (Wvec p U R ω) (twoValued (1 : ZMod p) (-1) fun c => x (a, c)) +
        (Kof p b0 b1 a0 a1 U R ω (e1Of R a) - Fintype.linearCombination (ZMod p) (Wvec p U R ω)
          (fun c => modP p (seidelOf ω) (e1Of R a) (e2Of R c))) := by
  set A := modP p (seidelOf ω) with hA
  set A' := modP p (seidelOf (replace (blk1 R) (blk1_injective R) ω x)) with hA'
  have hU : ∀ b, eUOf U b ∉ R := fun b h => Finset.disjoint_left.1 hRU h (eUOf_mem U b)
  have hrow : ∀ l, A' (e1Of R a) l = A (e1Of R a) l +
      ∑ c, if l = e2Of R c then A' (e1Of R a) (e2Of R c) - A (e1Of R a) (e2Of R c) else 0 := by
    intro l
    by_cases hl : ∃ c, l = e2Of R c
    · obtain ⟨c0, rfl⟩ := hl
      rw [Finset.sum_eq_single c0]
      · rw [ite_eq_left rfl]
        ring
      · intro c _ hc
        rw [ite_eq_right (fun h => hc ((e2Of_injective R h).symm))]
      · intro h
        exact absurd (Finset.mem_univ c0) h
    · push Not at hl
      rw [Finset.sum_eq_zero fun c _ => ite_eq_right (hl c), add_zero]
      exact modP_replace1_of p R ω x (not_isBlk1_e1Of_of R a hl)
  have hcolRc : ∀ l (a' : Fin Rᶜ.card), A' l (eRcOf R a') = A l (eRcOf R a') := fun l a' =>
    modP_replace1_of p R ω x (not_isBlk1_of_not_mem_right R l (eRcOf_not_mem R a'))
  funext s
  rcases s with a' | b
  ·
    simp only [Kof, Kmat, QAm, Matrix.of_apply, Sum.elim_inl, Pi.add_apply, Pi.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fintype.linearCombination_apply,
      Finset.sum_apply, Pi.smul_apply, Wvec, Wrow]
    rw [← hA', ← hA]
    have hsq : (A' * A') (e1Of R a) (eRcOf R a') = (A * A) (e1Of R a) (eRcOf R a') +
        ∑ c, (A' (e1Of R a) (e2Of R c) - A (e1Of R a) (e2Of R c)) * A (e2Of R c) (eRcOf R a') := by
      have hterm : ∀ l, A' (e1Of R a) l * A' l (eRcOf R a') = A (e1Of R a) l * A l (eRcOf R a') +
          ∑ c, (if l = e2Of R c then
            (A' (e1Of R a) (e2Of R c) - A (e1Of R a) (e2Of R c)) * A l (eRcOf R a') else 0) := by
        intro l
        rw [hcolRc l a', hrow l, add_mul, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> simp
      simp only [Matrix.mul_apply]
      rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_ite_eq']
      simp
    rw [hsq, hcolRc]
    have hx : ∀ c, A' (e1Of R a) (e2Of R c) = twoValued (1 : ZMod p) (-1) (fun c => x (a, c)) c := by
      intro c
      simp only [hA', modP, map_apply, seidelOf_replace1_blk R ω x a c, twoValued]
      split_ifs <;> simp
    simp only [hx, sub_mul, Finset.sum_sub_distrib]
    ring
  ·
    simp only [Kof, Kmat, PAm, Matrix.of_apply, Sum.elim_inr, Pi.add_apply, Pi.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fintype.linearCombination_apply,
      Finset.sum_apply, Pi.smul_apply, Wvec, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      sub_zero, zero_add]
    rw [modP_replace1_of p R ω x (not_isBlk1_of_not_mem_right R _ (hU b))]

theorem Kof_replace_U (hRU : Disjoint R U) (ω : Pairs m → Bool)
    (x : Fin (R.card / 2) × Fin (R.card / 2) → Bool) (b : Fin U.card) :
    Kof p b0 b1 a0 a1 U R (replace (blk1 R) (blk1_injective R) ω x) (eUOf U b) =
      Kof p b0 b1 a0 a1 U R ω (eUOf U b) := by
  have hU : ∀ b, eUOf U b ∉ R := fun b h => Finset.disjoint_left.1 hRU h (eUOf_mem U b)
  have hrow : ∀ l, modP p (seidelOf (replace (blk1 R) (blk1_injective R) ω x)) (eUOf U b) l =
      modP p (seidelOf ω) (eUOf U b) l := fun l =>
    modP_replace1_of p R ω x (not_isBlk1_of_not_mem_left R (hU b) l)
  have hcol : ∀ l (a' : Fin Rᶜ.card), modP p (seidelOf (replace (blk1 R) (blk1_injective R) ω x)) l
      (eRcOf R a') = modP p (seidelOf ω) l (eRcOf R a') := fun l a' =>
    modP_replace1_of p R ω x (not_isBlk1_of_not_mem_right R l (eRcOf_not_mem R a'))
  funext s
  rcases s with a' | b'
  · simp only [Kof, Kmat, QAm, Matrix.of_apply, Sum.elim_inl, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_apply, hrow, hcol]
  · simp only [Kof, Kmat, PAm, Matrix.of_apply, Sum.elim_inr, Matrix.add_apply, Matrix.smul_apply, hrow]

omit [Fact (Nat.Prime p)] in
theorem Wrow_replace1 (ω : Pairs m → Bool) (x : Fin (R.card / 2) × Fin (R.card / 2) → Bool) :
    Wrow p R (replace (blk1 R) (blk1_injective R) ω x) = Wrow p R ω := by
  funext c a
  exact modP_replace1_of p R ω x (not_isBlk1_of_not_mem_right R _ (eRcOf_not_mem R a))

theorem PUmat_replace1 (hRU : Disjoint R U) (ω : Pairs m → Bool)
    (x : Fin (R.card / 2) × Fin (R.card / 2) → Bool) :
    PUmat (PAm a0 a1 (modP p (seidelOf (replace (blk1 R) (blk1_injective R) ω x)))) (eUOf U) =
      PUmat (PAm a0 a1 (modP p (seidelOf ω))) (eUOf U) := by
  have hU : ∀ b, eUOf U b ∉ R := fun b h => Finset.disjoint_left.1 hRU h (eUOf_mem U b)
  ext b b'
  simp only [PUmat, PAm, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    modP_replace1_of p R ω x (not_isBlk1_of_not_mem_left R (hU b) _)]

theorem Wrow_replace2 (ω : Pairs m → Bool) (x : Fin (R.card / 2) × Fin Rᶜ.card → Bool) :
    Wrow p R (replace (blk2 R) (blk2_injective R) ω x) = fun c => twoValued (1 : ZMod p) (-1) fun a => x (c, a) := by
  funext c a
  simp only [Wrow, modP, map_apply, seidelOf_replace2 R ω x c a, twoValued]
  split_ifs <;> simp

theorem PUmat_eq (ω : Pairs m → Bool) :
    PUmat (PAm a0 a1 (modP p (seidelOf ω))) (eUOf U) = a1 • modP p (seidelOf (ω ∘ blkU U)) + a0 • 1 := by
  ext b b'
  simp only [PUmat, PAm, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, modP, map_apply,
    seidelOf_eUOf U ω b b', Matrix.one_apply, (eUOf_injective U).eq_iff]

end KofSec

end DGS
