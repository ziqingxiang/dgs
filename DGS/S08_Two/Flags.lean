module

public import DGS.S08_Two.SeqCount

@[expose] public section

open Matrix Polynomial Module

namespace DGS

variable {n : ℕ}

local notation "V" => Fin n → ZMod 2

def coordSub (S : Finset (Fin n)) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {y | ∀ i, i ∉ S → y i = 0}
  add_mem' := by
    intro y z hy hz i hi
    simp [hy i hi, hz i hi]
  zero_mem' := fun i _ => rfl
  smul_mem' := by
    intro c y hy i hi
    simp [hy i hi]

theorem mem_coordSub {S : Finset (Fin n)} {y : V} : y ∈ coordSub S ↔ ∀ i, i ∉ S → y i = 0 := Iff.rfl

def indS (S : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ S then 1 else 0

theorem indS_mem (S : Finset (Fin n)) : indS S ∈ coordSub S := fun i hi => by simp [indS, hi]

theorem indS_univ : indS (Finset.univ : Finset (Fin n)) = ones n (ZMod 2) := by
  funext i; simp [indS, ones]

theorem coordSub_univ : coordSub (Finset.univ : Finset (Fin n)) = ⊤ := by
  ext y; simp [mem_coordSub]

theorem dot_self_eq_indS_dot {S : Finset (Fin n)} {y : V} (hy : y ∈ coordSub S) :
    y ⬝ᵥ y = indS S ⬝ᵥ y := by
  simp only [dotProduct, indS]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi, one_mul]
    have := ZMod.pow_card (y i)
    rwa [sq] at this
  · rw [ite_eq_right hi, zero_mul, hy i hi, zero_mul]

theorem indS_dot_indS (S : Finset (Fin n)) : indS S ⬝ᵥ indS S = (S.card : ZMod 2) := by
  have h : ∀ i, indS S i * indS S i = if i ∈ S then 1 else 0 := by
    intro i; simp only [indS]; split_ifs <;> simp
  simp only [dotProduct, h]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem indS_ne_zero {S : Finset (Fin n)} (hS : S.Nonempty) : indS S ≠ 0 := by
  obtain ⟨i, hi⟩ := hS
  intro h
  have := congrFun h i
  simp [indS, hi] at this

def projS (S : Finset (Fin n)) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun y := fun i => if i ∈ S then y i else 0
  map_add' y z := by funext i; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c y := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

theorem projS_apply (S : Finset (Fin n)) (y : V) (i : Fin n) :
    projS S y i = if i ∈ S then y i else 0 := rfl

theorem projS_mem (S : Finset (Fin n)) (y : V) : projS S y ∈ coordSub S :=
  fun i hi => by simp [projS_apply, hi]

theorem projS_add_projS_compl (S : Finset (Fin n)) (y : V) : projS S y + projS Sᶜ y = y := by
  funext i
  simp only [Pi.add_apply, projS_apply, Finset.mem_compl]
  by_cases hi : i ∈ S <;> simp [hi]

theorem projS_of_mem {S : Finset (Fin n)} {y : V} (hy : y ∈ coordSub S) : projS S y = y := by
  funext i
  rw [projS_apply]
  split_ifs with hi
  · rfl
  · exact (hy i hi).symm

theorem range_projS (S : Finset (Fin n)) : LinearMap.range (projS S) = coordSub S := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩; exact projS_mem S y
  · intro y hy; exact ⟨y, projS_of_mem hy⟩

theorem ker_projS (S : Finset (Fin n)) : LinearMap.ker (projS S) = coordSub Sᶜ := by
  ext y
  rw [LinearMap.mem_ker, mem_coordSub]
  constructor
  · intro h i hi
    have := congrFun h i
    rw [Finset.mem_compl, not_not] at hi
    simpa [projS_apply, hi] using this
  · intro h
    funext i
    rw [projS_apply]
    split_ifs with hi
    · exact h i (by rw [Finset.mem_compl, not_not]; exact hi)
    · rfl

theorem finrank_coordSub (S : Finset (Fin n)) : finrank (ZMod 2) (coordSub S) = S.card := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (projS S)
  have h2 := LinearMap.finrank_range_add_finrank_ker (projS Sᶜ)
  rw [range_projS, ker_projS, Module.finrank_fin_fun] at h1
  rw [range_projS, ker_projS, compl_compl, Module.finrank_fin_fun] at h2
  have h3 : finrank (ZMod 2) (coordSub S) ≤ S.card := by
    let f : coordSub S →ₗ[ZMod 2] (S → ZMod 2) :=
      { toFun := fun y i => y.1 i
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro y z h
      apply Subtype.ext
      funext i
      by_cases hi : i ∈ S
      · exact congrFun h ⟨i, hi⟩
      · rw [y.2 i hi, z.2 i hi]
    have := LinearMap.finrank_le_finrank_of_injective hf
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  have h4 : finrank (ZMod 2) (coordSub Sᶜ) ≤ Sᶜ.card := by
    let f : coordSub Sᶜ →ₗ[ZMod 2] (↥Sᶜ → ZMod 2) :=
      { toFun := fun y i => y.1 i
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro y z h
      apply Subtype.ext
      funext i
      by_cases hi : i ∈ Sᶜ
      · exact congrFun h ⟨i, hi⟩
      · rw [y.2 i hi, z.2 i hi]
    have := LinearMap.finrank_le_finrank_of_injective hf
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  have h5 : S.card + Sᶜ.card = n := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ S
    rw [Fintype.card_fin] at this
    omega
  omega

theorem dot_eq_zero_of_coordSub {S : Finset (Fin n)} {y z : V} (hy : y ∈ coordSub S)
    (hz : z ∈ coordSub Sᶜ) : y ⬝ᵥ z = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i ∈ S
  · rw [hz i (by rw [Finset.mem_compl, not_not]; exact hi), mul_zero]
  · rw [hy i hi, zero_mul]

theorem finrank_orthC_inf_coordSub {S : Finset (Fin n)} {U : Submodule (ZMod 2) V}
    (hU : U ≤ coordSub S) :
    finrank (ZMod 2) (orthC U ⊓ coordSub S : Submodule (ZMod 2) V) = S.card - finrank (ZMod 2) U := by
  have hsup : (orthC U ⊓ coordSub S) ⊔ coordSub Sᶜ = orthC U := by
    apply le_antisymm
    · refine sup_le inf_le_left fun z hz w hw => ?_
      exact dot_eq_zero_of_coordSub (hU hw) hz
    · intro y hy
      rw [← projS_add_projS_compl S y]
      refine Submodule.add_mem_sup ⟨?_, projS_mem S y⟩ (projS_mem Sᶜ y)
      have h1 : projS Sᶜ y ∈ orthC U := fun w hw => dot_eq_zero_of_coordSub (hU hw) (projS_mem _ _)
      have h2 : projS S y = y - projS Sᶜ y := eq_sub_of_add_eq (projS_add_projS_compl S y)
      rw [h2]
      exact sub_mem hy h1
  have hinf : (orthC U ⊓ coordSub S) ⊓ coordSub Sᶜ = ⊥ := by
    rw [eq_bot_iff]
    intro y ⟨⟨_, hy1⟩, hy2⟩
    rw [Submodule.mem_bot]
    funext i
    by_cases hi : i ∈ S
    · exact hy2 i (by rw [Finset.mem_compl, not_not]; exact hi)
    · exact hy1 i hi
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (orthC U ⊓ coordSub S) (coordSub Sᶜ)
  rw [hsup, hinf, finrank_bot, add_zero, finrank_coordSub] at h1
  have h2 := finrank_orthC_add U
  have h3 : S.card + Sᶜ.card = n := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ S
    rw [Fintype.card_fin] at this
    omega
  omega

def flagCh (S : Finset (Fin n)) : (i : ℕ) → (Fin i → (Fin n → ZMod 2)) → Set (Fin n → ZMod 2)
  | 0, _ => {indS S}
  | _ + 1, p => {y | y ∈ coordSub S ∧ y ∈ orthC (Submodule.span (ZMod 2) (Set.range p)) ∧
      y ∉ Submodule.span (ZMod 2) (Set.range p)}

abbrev IsFlag (S : Finset (Fin n)) (m : ℕ) (u : Fin m → V) : Prop := SeqValid (flagCh S) m u

theorem isFlag_one_iff {S : Finset (Fin n)} {u : Fin 1 → V} : IsFlag S 1 u ↔ u 0 = indS S := by
  show SeqValid (flagCh S) 0 (Fin.init u) ∧ u (Fin.last 0) ∈ flagCh S 0 (Fin.init u) ↔ _
  simp [SeqValid, flagCh]

theorem isFlag_succ_iff {S : Finset (Fin n)} {m : ℕ} {u : Fin (m + 1 + 1) → V} :
    IsFlag S (m + 1 + 1) u ↔ IsFlag S (m + 1) (Fin.init u) ∧
      u (Fin.last (m + 1)) ∈ coordSub S ∧
      u (Fin.last (m + 1)) ∈ orthC (Submodule.span (ZMod 2) (Set.range (Fin.init u))) ∧
      u (Fin.last (m + 1)) ∉ Submodule.span (ZMod 2) (Set.range (Fin.init u)) := Iff.rfl

theorem IsFlag.prop {S : Finset (Fin n)} (hS : S.Nonempty) :
    ∀ {m : ℕ} {u : Fin (m + 1) → V}, IsFlag S (m + 1) u →
      u 0 = indS S ∧ (∀ i, u i ∈ coordSub S) ∧ LinearIndependent (ZMod 2) u ∧
        ∀ i j : Fin (m + 1), ((i : ℕ) ≠ 0 ∨ (j : ℕ) ≠ 0) → u i ⬝ᵥ u j = 0 := by
  intro m
  induction m with
  | zero =>
    intro u hu
    rw [isFlag_one_iff] at hu
    refine ⟨hu, fun i => ?_, ?_, fun i j h => ?_⟩
    · have : i = 0 := Fin.ext (by have := i.2; omega)
      rw [this, hu]; exact indS_mem S
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hi : i = 0 := Fin.ext (by have := i.2; omega)
      subst hi
      rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, hu] at hg
      exact (smul_eq_zero.1 hg).resolve_right (indS_ne_zero hS)
    · exfalso
      have hi := i.2
      have hj := j.2
      omega
  | succ m ih =>
    intro u hu
    rw [isFlag_succ_iff] at hu
    obtain ⟨hinit, hx1, hx2, hx3⟩ := hu
    obtain ⟨h0, hmem, hind, horth⟩ := ih hinit
    refine ⟨?_, fun i => ?_, ?_, fun i j h => ?_⟩
    · have := h0
      simp only [Fin.init] at this
      exact this
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact hmem j
      · exact hx1
    · rw [linearIndependent_finSucc']
      exact ⟨hind, hx3⟩
    · have hlast : ∀ j : Fin (m + 1 + 1), u (Fin.last (m + 1)) ⬝ᵥ u j = 0 := by
        intro j
        rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
        · rw [dotProduct_comm]
          exact hx2 _ (Submodule.subset_span ⟨k, rfl⟩)
        ·
          rw [dot_self_eq_indS_dot hx1, ← h0]
          exact hx2 _ (Submodule.subset_span ⟨0, rfl⟩)
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · exact horth i' j' (by simpa using h)
        · rw [dotProduct_comm]; exact hlast _
      · exact hlast j

theorem finrank_radical_flag {S : Finset (Fin n)} (hS : S.Nonempty) {m : ℕ} {u : Fin (m + 1) → V}
    (hu : IsFlag S (m + 1) u) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range u) ⊓
      orthC (Submodule.span (ZMod 2) (Set.range u)) : Submodule (ZMod 2) V) = m + 1 - S.card % 2 := by
  obtain ⟨h0, -, hind, horth⟩ := hu.prop hS
  set K := Submodule.span (ZMod 2) (Set.range u) with hK
  have hKdim : finrank (ZMod 2) K = m + 1 := by rw [hK, finrank_span_eq_card hind, Fintype.card_fin]
  let f : V →ₗ[ZMod 2] ZMod 2 := (dotProductEquiv (ZMod 2) (Fin n)) (indS S)
  have hf : ∀ y, f y = indS S ⬝ᵥ y := fun y => rfl
  have heq : K ⊓ orthC K = K ⊓ LinearMap.ker f := by
    ext y
    simp only [Submodule.mem_inf, LinearMap.mem_ker, hf]
    constructor
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      rw [← h0]
      exact hy' _ (Submodule.subset_span ⟨0, rfl⟩)
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      rw [hK, mem_orthC_span_iff]
      intro i
      by_cases hi : (i : ℕ) = 0
      · have : i = 0 := Fin.ext hi
        rw [this, h0]
        exact hy'
      ·
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hy
        rw [dotProduct_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [dotProduct_smul, horth i j (Or.inl hi), smul_zero]
  rw [heq]
  have h1 := finrank_map_add_finrank_inf_ker' f K
  rw [hKdim] at h1
  have hmap : finrank (ZMod 2) (K.map f) = S.card % 2 := by
    rcases Nat.mod_two_eq_zero_or_one S.card with h | h
    · rw [h]
      rw [Submodule.finrank_eq_zero, eq_bot_iff]
      rintro _ ⟨y, hy, rfl⟩
      rw [Submodule.mem_bot, hf]
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hy
      rw [dotProduct_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [dotProduct_smul, ← h0]
      by_cases hj : (j : ℕ) = 0
      · have : j = 0 := Fin.ext hj
        subst this
        rw [h0, indS_dot_indS, ← ZMod.natCast_mod, h, Nat.cast_zero, smul_zero]
      · rw [horth 0 j (Or.inr hj), smul_zero]
    · rw [h]
      have htop : K.map f = ⊤ := by
        rw [eq_top_iff]
        intro x _
        refine ⟨x • u 0, K.smul_mem x (Submodule.subset_span ⟨0, rfl⟩), ?_⟩
        rw [map_smul, hf, h0, indS_dot_indS, ← ZMod.natCast_mod, h, Nat.cast_one, smul_eq_mul,
          mul_one]
      rw [htop, finrank_top, Module.finrank_self]
  omega

theorem card_flagCh {S : Finset (Fin n)} (hS : S.Nonempty) {m : ℕ} {u : Fin (m + 1) → V}
    (hu : IsFlag S (m + 1) u) :
    Nat.card (flagCh S (m + 1) u) = 2 ^ (S.card - (m + 1)) - 2 ^ (m + 1 - S.card % 2) := by
  set K := Submodule.span (ZMod 2) (Set.range u) with hK
  obtain ⟨-, hmem, hind, -⟩ := hu.prop hS
  have hKS : K ≤ coordSub S := by
    rw [hK, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  have hKdim : finrank (ZMod 2) K = m + 1 := by rw [hK, finrank_span_eq_card hind, Fintype.card_fin]
  have hset : flagCh S (m + 1) u =
      ((orthC K ⊓ coordSub S : Submodule (ZMod 2) V) : Set V) \
        ((K ⊓ orthC K : Submodule (ZMod 2) V) : Set V) := by
    ext y
    simp only [flagCh, Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Submodule.mem_inf]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h2, h1⟩, fun h => h3 h.1⟩
    · rintro ⟨⟨h2, h1⟩, h3⟩
      exact ⟨h1, h2, fun h => h3 ⟨h, h2⟩⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_sdiff]
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    change Nat.card (orthC K ⊓ coordSub S : Submodule (ZMod 2) V) -
      Nat.card (K ⊓ orthC K : Submodule (ZMod 2) V) = _
    have e1 : Nat.card (orthC K ⊓ coordSub S : Submodule (ZMod 2) V) = 2 ^ (S.card - (m + 1)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        finrank_orthC_inf_coordSub hKS, hKdim]
    have e2 : Nat.card (K ⊓ orthC K : Submodule (ZMod 2) V) = 2 ^ (m + 1 - S.card % 2) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_radical_flag hS hu]
    rw [e1, e2]
  · intro y hy
    exact ⟨hy.2, hKS hy.1⟩

end DGS
