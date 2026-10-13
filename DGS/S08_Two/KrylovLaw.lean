module

public import DGS.S08_Two.Krylov

@[expose] public section

open Matrix Polynomial Module

namespace DGS

section CosetFiber

variable {F X Y : Type*} [Field F] [Finite F] [AddCommGroup X] [Module F X] [Finite X]
  [AddCommGroup Y] [Module F Y]

theorem finrank_map_add_finrank_inf_ker' (L : X →ₗ[F] Y) (U : Submodule F X) :
    finrank F (U.map L) + finrank F (U ⊓ LinearMap.ker L : Submodule F X) = finrank F U := by
  have h := LinearMap.finrank_range_add_finrank_ker (L.domRestrict U)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have h2 : finrank F ((LinearMap.ker L).comap U.subtype) =
      finrank F (U ⊓ LinearMap.ker L : Submodule F X) := by
    rw [(Submodule.equivSubtypeMap U ((LinearMap.ker L).comap U.subtype)).finrank_eq,
      Submodule.map_comap_subtype]
  rw [h2] at h
  exact h

theorem finrank_map_le' (L : X →ₗ[F] Y) (U : Submodule F X) : finrank F (U.map L) ≤ finrank F U := by
  have := finrank_map_add_finrank_inf_ker' L U
  omega

open Classical in
theorem natCard_coset_fiber (L : X →ₗ[F] Y) (U : Submodule F X) (x₀ : X) (y : Y) :
    Nat.card {x : X // x - x₀ ∈ U ∧ L x = y} =
      if y - L x₀ ∈ U.map L then Nat.card F ^ (finrank F U - finrank F (U.map L)) else 0 := by
  have hrank := finrank_map_add_finrank_inf_ker' L U
  split_ifs with h
  · obtain ⟨u₁, hu₁, hLu⟩ := h
    rw [show finrank F U - finrank F (U.map L) = finrank F (U ⊓ LinearMap.ker L : Submodule F X) by
      omega, ← Module.natCard_eq_pow_finrank]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1 - x₀ - u₁, sub_mem x.2.1 hu₁, ?_⟩
        invFun := fun t => ⟨t.1 + x₀ + u₁, ?_, ?_⟩
        left_inv := fun x => Subtype.ext (by dsimp only; abel)
        right_inv := fun t => Subtype.ext (by dsimp only; abel) }
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_sub, x.2.2, hLu, sub_sub,
        add_sub_cancel, sub_self]
    · have := add_mem (Submodule.mem_inf.1 t.2).1 hu₁
      convert this using 1
      abel
    · have ht := (Submodule.mem_inf.1 t.2).2
      rw [LinearMap.mem_ker] at ht
      rw [map_add, map_add, ht, hLu, zero_add, add_sub_cancel]
  · have : IsEmpty {x : X // x - x₀ ∈ U ∧ L x = y} :=
      ⟨fun x => h ⟨x.1 - x₀, x.2.1, by rw [map_sub, x.2.2]⟩⟩
    exact Nat.card_of_isEmpty

theorem natCard_coset (U : Submodule F X) (x₀ : X) :
    Nat.card {x : X // x - x₀ ∈ U} = Nat.card F ^ finrank F U := by
  rw [← Module.natCard_eq_pow_finrank]
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1 - x₀, x.2⟩
      invFun := fun t => ⟨t.1 + x₀, by simp⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun t => Subtype.ext (by simp) }

end CosetFiber

section Alt

variable {n : ℕ}

local notation "V" => Fin n → ZMod 2
local notation "Mat" => Matrix (Fin n) (Fin n) (ZMod 2)

def IsAlt (M : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop := Mᵀ = M ∧ ∀ i, M i i = 0

def altKill (U : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)) where
  carrier := {B | Bᵀ = B ∧ (∀ i, B i i = 0) ∧ ∀ y ∈ U, B *ᵥ y = 0}
  add_mem' := by
    rintro B B' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨by rw [transpose_add, h1, h1'], fun i => by simp [h2, h2'], fun y hy => ?_⟩
    rw [add_mulVec, h3 y hy, h3' y hy, add_zero]
  zero_mem' := ⟨transpose_zero, fun i => rfl, fun y _ => zero_mulVec y⟩
  smul_mem' := by
    rintro c B ⟨h1, h2, h3⟩
    refine ⟨by rw [transpose_smul, h1], fun i => by simp [h2], fun y hy => ?_⟩
    rw [smul_mulVec, h3 y hy, smul_zero]

theorem mem_altKill {U : Submodule (ZMod 2) (Fin n → ZMod 2)} {B : Mat} :
    B ∈ altKill U ↔ Bᵀ = B ∧ (∀ i, B i i = 0) ∧ ∀ y ∈ U, B *ᵥ y = 0 := Iff.rfl

theorem IsAlt.sub {M M' : Mat} (hM : IsAlt M) (hM' : IsAlt M') : IsAlt (M - M') :=
  ⟨by rw [transpose_sub, hM.1, hM'.1], fun i => by simp [hM.2, hM'.2]⟩

theorem IsAlt.add {M M' : Mat} (hM : IsAlt M) (hM' : IsAlt M') : IsAlt (M + M') :=
  ⟨by rw [transpose_add, hM.1, hM'.1], fun i => by simp [hM.2, hM'.2]⟩

def mulVecAt (v : Fin n → ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun B := B *ᵥ v
  map_add' B B' := add_mulVec B B' v
  map_smul' c B := by rw [smul_mulVec, RingHom.id_apply]

theorem mulVecAt_apply (v : V) (B : Mat) : mulVecAt v B = B *ᵥ v := rfl

theorem mem_orthC_span_iff {k : ℕ} {w : Fin k → V} {y : V} :
    y ∈ orthC (Submodule.span (ZMod 2) (Set.range w)) ↔ ∀ i, w i ⬝ᵥ y = 0 := by
  constructor
  · intro h i
    exact h (w i) (Submodule.subset_span ⟨i, rfl⟩)
  · intro h x hx
    refine Submodule.span_induction (p := fun x _ => x ⬝ᵥ y = 0) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩; exact h i
    · exact zero_dotProduct y
    · intro a b _ _ ha hb; rw [add_dotProduct, ha, hb, add_zero]
    · intro c a _ ha; rw [smul_dotProduct, ha, smul_zero]

theorem finrank_orthC_span {k : ℕ} {w : Fin k → V} (hw : LinearIndependent (ZMod 2) w) :
    finrank (ZMod 2) (orthC (Submodule.span (ZMod 2) (Set.range w))) = n - k := by
  have h1 := finrank_orthC_add (Submodule.span (ZMod 2) (Set.range w))
  rw [finrank_span_eq_card hw, Fintype.card_fin] at h1
  omega

theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

theorem map_altKill_eq {k : ℕ} {w : Fin (k + 1) → V} (hw : LinearIndependent (ZMod 2) w) :
    (altKill (Submodule.span (ZMod 2) (Set.range (Fin.init w)))).map (mulVecAt (w (Fin.last k))) =
      orthC (Submodule.span (ZMod 2) (Set.range w)) := by
  apply le_antisymm
  · rintro _ ⟨B, ⟨hB1, hB2, hB3⟩, rfl⟩
    rw [mem_orthC_span_iff]
    intro i
    rw [mulVecAt_apply]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h := hB3 (w j.castSucc) (Submodule.subset_span ⟨j, rfl⟩)
      rw [dotProduct_mulVec, ← mulVec_transpose, hB1, h, zero_dotProduct]
    · exact dotProduct_mulVec_self_eq_zero (by decide) hB1 hB2 _
  · intro z hz
    have hinit : LinearIndependent (ZMod 2) (Fin.init w) := (linearIndependent_finSucc'.1 hw).1
    have hlt : finrank (ZMod 2) (orthC (Submodule.span (ZMod 2) (Set.range w))) <
        finrank (ZMod 2) (orthC (Submodule.span (ZMod 2) (Set.range (Fin.init w)))) := by
      rw [finrank_orthC_span hw, finrank_orthC_span hinit]
      have := (finrank_span_eq_card hw).symm.trans_le (Submodule.finrank_le _)
      rw [Fintype.card_fin, Module.finrank_fin_fun] at this
      omega
    obtain ⟨y, hy1, hy2⟩ : ∃ y ∈ orthC (Submodule.span (ZMod 2) (Set.range (Fin.init w))),
        y ∉ orthC (Submodule.span (ZMod 2) (Set.range w)) := by
      by_contra hcon
      push Not at hcon
      exact absurd (Submodule.finrank_mono hcon) (not_le.2 hlt)
    rw [mem_orthC_span_iff] at hy1 hy2
    push Not at hy2
    obtain ⟨i, hi⟩ := hy2
    have hyk : w (Fin.last k) ⬝ᵥ y = 1 := by
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact absurd (hy1 j) hi
      · exact zmod2_eq_one_of_ne_zero hi
    rw [mem_orthC_span_iff] at hz
    refine ⟨vecMulVec z y + vecMulVec y z, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_comm]
    · intro i
      simp only [Matrix.add_apply, vecMulVec_apply]
      rw [mul_comm (y i), ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
    · intro x hx
      refine Submodule.span_induction (p := fun x _ => (vecMulVec z y + vecMulVec y z) *ᵥ x = 0)
        ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨j, rfl⟩
        rw [add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, dotProduct_comm y, hy1 j,
          dotProduct_comm z]
        have : Fin.init w j ⬝ᵥ z = 0 := hz j.castSucc
        rw [this]
        simp
      · exact mulVec_zero _
      · intro a b _ _ ha hb; rw [mulVec_add, ha, hb, add_zero]
      · intro c a _ ha; rw [mulVec_smul, ha, smul_zero]
    · rw [mulVecAt_apply, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, dotProduct_comm y, hyk,
        dotProduct_comm z, hz (Fin.last k)]
      simp

def kseq (k : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2)) : Fin k → (Fin n → ZMod 2) :=
  fun i => M ^ (i : ℕ) *ᵥ ones n (ZMod 2)

noncomputable def kcount (k : ℕ) (w : Fin k → (Fin n → ZMod 2)) : ℕ :=
  Nat.card {M : Matrix (Fin n) (Fin n) (ZMod 2) // IsAlt M ∧ kseq k M = w}

theorem kseq_succ_eq_snoc (k : ℕ) (M : Mat) :
    kseq (k + 1) M = Fin.snoc (kseq k M) (M ^ k *ᵥ ones n (ZMod 2)) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp only [kseq, Fin.snoc_castSucc, Fin.val_castSucc]
  · simp only [kseq, Fin.snoc_last, Fin.val_last]

theorem kseq_succ_eq_iff {k : ℕ} {M : Mat} {w : Fin k → V} {z : V} :
    kseq (k + 1) M = Fin.snoc w z ↔ kseq k M = w ∧ M ^ k *ᵥ ones n (ZMod 2) = z := by
  rw [kseq_succ_eq_snoc]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := congrArg Fin.init h
      rwa [Fin.init_snoc, Fin.init_snoc] at this
    · have := congrFun h (Fin.last k)
      rwa [Fin.snoc_last, Fin.snoc_last] at this
  · rintro ⟨rfl, rfl⟩
    rfl

theorem kseq_apply (k : ℕ) (M : Mat) (i : Fin k) : kseq k M i = M ^ (i : ℕ) *ᵥ ones n (ZMod 2) :=
  rfl

theorem kseq_dot {k : ℕ} {M : Mat} (hM : IsAlt M) (i j : Fin k) (h : (i : ℕ) ≠ 0 ∨ (j : ℕ) ≠ 0) :
    kseq k M i ⬝ᵥ kseq k M j = 0 :=
  dot_pow_ones_eq_zero hM.1 hM.2 h

theorem fiber_eq_coset {k : ℕ} {w : Fin (k + 1) → V} {M₀ : Mat} (hM₀ : IsAlt M₀)
    (hw₀ : kseq (k + 1) M₀ = w) (M : Mat) :
    (IsAlt M ∧ kseq (k + 1) M = w) ↔
      M - M₀ ∈ altKill (Submodule.span (ZMod 2) (Set.range (Fin.init w))) := by
  constructor
  · rintro ⟨hM, hMw⟩
    have hsub := hM.sub hM₀
    refine ⟨hsub.1, hsub.2, fun y hy => ?_⟩
    refine Submodule.span_induction (p := fun y _ => (M - M₀) *ᵥ y = 0) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨j, rfl⟩
      have h1 : Fin.init w j = M ^ (j : ℕ) *ᵥ ones n (ZMod 2) := by
        rw [← hMw]; rfl
      have h2 : Fin.init w j = M₀ ^ (j : ℕ) *ᵥ ones n (ZMod 2) := by
        rw [← hw₀]; rfl
      have h3 : M ^ ((j : ℕ) + 1) *ᵥ ones n (ZMod 2) = M₀ ^ ((j : ℕ) + 1) *ᵥ ones n (ZMod 2) := by
        have e1 := congrFun hMw j.succ
        have e2 := congrFun hw₀ j.succ
        simp only [kseq, Fin.val_succ] at e1 e2
        rw [e1, e2]
      rw [sub_mulVec]
      nth_rewrite 1 [h1]
      rw [h2, mulVec_mulVec, mulVec_mulVec, ← pow_succ', ← pow_succ', h3, sub_self]
    · exact mulVec_zero _
    · intro a b _ _ ha hb; rw [mulVec_add, ha, hb, add_zero]
    · intro c a _ ha; rw [mulVec_smul, ha, smul_zero]
  · intro hB
    obtain ⟨hB1, hB2, hB3⟩ := hB
    have hM : IsAlt M := by
      have := hM₀.add ⟨hB1, hB2⟩
      rwa [add_sub_cancel] at this
    refine ⟨hM, ?_⟩
    rw [← hw₀]
    have key : ∀ i, i ≤ k → M ^ i *ᵥ ones n (ZMod 2) = M₀ ^ i *ᵥ ones n (ZMod 2) := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        have hwi : M₀ ^ i *ᵥ ones n (ZMod 2) ∈ Submodule.span (ZMod 2) (Set.range (Fin.init w)) := by
          refine Submodule.subset_span ⟨⟨i, by omega⟩, ?_⟩
          rw [← hw₀]; rfl
        have hB := hB3 _ hwi
        rw [pow_succ', ← mulVec_mulVec, ih (by omega), pow_succ', ← mulVec_mulVec]
        have : M = M₀ + (M - M₀) := by abel
        rw [this, add_mulVec, hB, add_zero]
    funext i
    exact key i (by omega)

open Classical in
theorem lem_krylov {k : ℕ} {w : Fin (k + 1) → V} (hw : LinearIndependent (ZMod 2) w) (z : V) :
    kcount (k + 1 + 1) (Fin.snoc w z) * 2 ^ (n - (k + 1)) =
      if z ∈ orthC (Submodule.span (ZMod 2) (Set.range w)) then kcount (k + 1) w else 0 := by
  by_cases hne : kcount (k + 1) w = 0
  · have hle : kcount (k + 1 + 1) (Fin.snoc w z) ≤ kcount (k + 1) w := by
      refine Nat.card_le_card_of_injective
        (fun M => ⟨M.1, M.2.1, (kseq_succ_eq_iff.1 M.2.2).1⟩) ?_
      intro M M' h
      apply Subtype.ext
      have := congrArg Subtype.val h
      exact this
    rw [hne] at hle ⊢
    rw [Nat.le_zero.1 hle, zero_mul]
    split_ifs <;> rfl
  obtain ⟨⟨M₀, hM₀, hw₀⟩⟩ : Nonempty {M : Mat // IsAlt M ∧ kseq (k + 1) M = w} := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hne Nat.card_of_isEmpty
  set K' := Submodule.span (ZMod 2) (Set.range (Fin.init w)) with hK'
  set Kp := orthC (Submodule.span (ZMod 2) (Set.range w)) with hKp
  set U := altKill K' with hU
  set L := mulVecAt (w (Fin.last k)) with hL
  have hA : kcount (k + 1) w = 2 ^ finrank (ZMod 2) U := by
    rw [kcount, Nat.card_congr (Equiv.subtypeEquivRight (fiber_eq_coset hM₀ hw₀)), natCard_coset,
      Nat.card_zmod]
  have hB : kcount (k + 1 + 1) (Fin.snoc w z) =
      Nat.card {M : Mat // M - M₀ ∈ U ∧ L M = z} := by
    rw [kcount]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun M => ?_)
    rw [kseq_succ_eq_iff]
    constructor
    · rintro ⟨hM, hMw, hMz⟩
      refine ⟨(fiber_eq_coset hM₀ hw₀ M).1 ⟨hM, hMw⟩, ?_⟩
      rw [hL, mulVecAt_apply, ← hMz]
      have : w (Fin.last k) = M ^ k *ᵥ ones n (ZMod 2) := by rw [← hMw]; rfl
      rw [this, mulVec_mulVec, ← pow_succ']
    · rintro ⟨hMU, hMz⟩
      obtain ⟨hM, hMw⟩ := (fiber_eq_coset hM₀ hw₀ M).2 hMU
      refine ⟨hM, hMw, ?_⟩
      rw [hL, mulVecAt_apply] at hMz
      have : w (Fin.last k) = M ^ k *ᵥ ones n (ZMod 2) := by rw [← hMw]; rfl
      rw [this, mulVec_mulVec, ← pow_succ'] at hMz
      exact hMz
  have hmap : U.map L = Kp := map_altKill_eq hw
  have hLM₀ : L M₀ ∈ Kp := by
    rw [hKp, mem_orthC_span_iff]
    intro i
    have h1 : w i = M₀ ^ (i : ℕ) *ᵥ ones n (ZMod 2) := by rw [← hw₀]; rfl
    have h2 : w (Fin.last k) = M₀ ^ k *ᵥ ones n (ZMod 2) := by rw [← hw₀]; rfl
    rw [hL, mulVecAt_apply, h1, h2, mulVec_mulVec, ← pow_succ']
    exact dot_pow_ones_eq_zero hM₀.1 hM₀.2 (Or.inr (by omega))
  have hdimKp : finrank (ZMod 2) Kp = n - (k + 1) := by
    rw [hKp, finrank_orthC_span hw]
  have hle := finrank_map_le' L U
  rw [hB, natCard_coset_fiber, hmap, Nat.card_zmod, hA]
  have hiff : z - L M₀ ∈ Kp ↔ z ∈ Kp := by
    constructor
    · intro h; have := add_mem h hLM₀; rwa [sub_add_cancel] at this
    · intro h; exact sub_mem h hLM₀
  by_cases hz : z ∈ Kp
  · rw [ite_eq_left (hiff.2 hz), ite_eq_left hz, hdimKp, ← pow_add]
    rw [hmap, hdimKp] at hle
    congr 1
    omega
  · rw [ite_eq_right (fun h => hz (hiff.1 h)), ite_eq_right hz, zero_mul]

end Alt

theorem natCard_subtype_eq_sum {α β : Type*} [Finite α] [Fintype β] (P : α → Prop) (f : α → β) :
    Nat.card {a // P a} = ∑ b, Nat.card {a // P a ∧ f a = b} := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr
    { toFun := fun a => ⟨f a.1, a.1, a.2, rfl⟩
      invFun := fun x => ⟨x.2.1, x.2.2.1⟩
      left_inv := fun a => rfl
      right_inv := fun ⟨b, a, hP, hf⟩ => by subst hf; rfl }

theorem natCard_mono {α : Type*} [Finite α] {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    Nat.card {a // P a} ≤ Nat.card {a // Q a} :=
  Nat.card_le_card_of_injective (fun a => ⟨a.1, h a.1 a.2⟩)
    (fun a b hab => Subtype.ext (by have := congrArg Subtype.val hab; exact this))

section PolyOfFin

variable {R : Type*} [CommRing R]

noncomputable def polyOfFin {k : ℕ} (c : Fin k → R) : R[X] := ∑ i, C (c i) * X ^ (i : ℕ)

theorem coeff_polyOfFin {k : ℕ} (c : Fin k → R) (j : ℕ) :
    (polyOfFin c).coeff j = if h : j < k then c ⟨j, h⟩ else 0 := by
  rw [polyOfFin, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      rw [ite_eq_right]
      intro hj
      exact hb (Fin.ext hj.symm)
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right]
    intro hj
    exact h (hj ▸ i.2)

theorem degree_polyOfFin_lt [Nontrivial R] {k : ℕ} (c : Fin k → R) : (polyOfFin c).degree < k := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_polyOfFin, dite_eq_right (by omega)]

theorem aeval_polyOfFin_mulVec {n k : ℕ} (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R)
    (c : Fin k → R) : aeval M (polyOfFin c) *ᵥ v = ∑ i, c i • (M ^ (i : ℕ) *ᵥ v) := by
  rw [polyOfFin, map_sum, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    Matrix.one_mul, smul_mulVec]

theorem polyOfFin_coeff_eq {k : ℕ} {p : R[X]} (hp : p.natDegree < k) :
    polyOfFin (fun i : Fin k => p.coeff i) = p := by
  ext j
  rw [coeff_polyOfFin]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]

end PolyOfFin

section KZero

variable {n : ℕ}

theorem linearIndependent_kseq_iff (M : Matrix (Fin n) (Fin n) (ZMod 2)) (k : ℕ) :
    LinearIndependent (ZMod 2) (kseq k M) ↔ k ≤ (muVec M (ones n (ZMod 2))).natDegree := by
  set μ := muVec M (ones n (ZMod 2)) with hμ
  have hμm : μ.Monic := muVec_monic _ _
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hrel : ∑ i : Fin k, μ.coeff i • kseq k M i = 0 := by
      have := aeval_polyOfFin_mulVec M (ones n (ZMod 2)) (fun i : Fin k => μ.coeff i)
      rw [polyOfFin_coeff_eq hlt, aeval_muVec] at this
      exact this.symm
    have := h _ hrel ⟨μ.natDegree, hlt⟩
    simp only at this
    rw [hμm.coeff_natDegree] at this
    exact one_ne_zero this
  · intro hk g hg i
    have h1 : aeval M (polyOfFin g) *ᵥ ones n (ZMod 2) = 0 := by
      rw [aeval_polyOfFin_mulVec]; exact hg
    have h2 := (muVec_dvd_iff M _).2 h1
    have h3 : polyOfFin g = 0 := by
      apply eq_zero_of_dvd_of_degree_lt h2
      calc (polyOfFin g).degree < k := degree_polyOfFin_lt g
        _ ≤ μ.natDegree := by exact_mod_cast hk
        _ = μ.degree := (degree_eq_natDegree hμm.ne_zero).symm
    have := congrArg (coeff · (i : ℕ)) h3
    simp only [coeff_polyOfFin, dite_eq_left i.2, coeff_zero] at this
    exact this

theorem natDegree_muVec_eq_iff (M : Matrix (Fin n) (Fin n) (ZMod 2)) (k : ℕ) :
    (muVec M (ones n (ZMod 2))).natDegree = k ↔
      LinearIndependent (ZMod 2) (kseq k M) ∧
        M ^ k *ᵥ ones n (ZMod 2) ∈ Submodule.span (ZMod 2) (Set.range (kseq k M)) := by
  have h1 := linearIndependent_kseq_iff M k
  have h2 := linearIndependent_kseq_iff M (k + 1)
  rw [kseq_succ_eq_snoc, linearIndependent_finSnoc] at h2
  constructor
  · intro h
    refine ⟨h1.2 h.ge, ?_⟩
    by_contra hnot
    have := h2.1 ⟨h1.2 h.ge, hnot⟩
    omega
  · rintro ⟨hind, hmem⟩
    have hk := h1.1 hind
    by_contra hne
    have : k + 1 ≤ (muVec M (ones n (ZMod 2))).natDegree := by omega
    exact (h2.2 this).2 hmem

theorem one_le_natDegree_muVec (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    1 ≤ (muVec M (ones n (ZMod 2))).natDegree := by
  rw [← linearIndependent_kseq_iff]
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hi : i = 0 := Fin.ext (by omega)
  subst hi
  rw [Fin.sum_univ_one] at hg
  have := congrFun hg ⟨0, hn⟩
  simp [kseq, ones] at this
  exact this

end KZero

section AltEquiv

variable {n : ℕ}

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

def altEquiv : (Pairs n → Bool) ≃ {M : Matrix (Fin n) (Fin n) (ZMod 2) // IsAlt M} where
  toFun ω := ⟨modP 2 (symOf 1 0 ω), modP_symOf_transpose ω, modP_symOf_diag ω⟩
  invFun M := fun q => decide (M.1 q.1.1 q.1.2 = 1)
  left_inv ω := by
    funext q
    have h : modP 2 (symOf 1 0 ω) q.1.1 q.1.2 = if ω q then 1 else 0 := by
      simp only [modP, Matrix.map_apply]
      rw [symOf_apply_lt _ _ _ q.2]
      split_ifs <;> simp
    simp only [h]
    cases ω q <;> decide
  right_inv M := by
    apply Subtype.ext
    ext i j
    simp only [modP, Matrix.map_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [symOf_apply_lt _ _ _ h]
      rcases zmod2_cases (M.1 i j) with h0 | h1
      · simp [h0]
      · simp [h1]
    · rw [symOf_apply_self, M.2.2]; simp
    · rw [symOf_apply_gt _ _ _ h]
      have hs : M.1 i j = M.1 j i := by
        have := congrFun (congrFun M.2.1 j) i
        rw [transpose_apply] at this
        exact this
      rw [hs]
      rcases zmod2_cases (M.1 j i) with h0 | h1
      · simp [h0]
      · simp [h1]

theorem prob_eq_alt (P : Matrix (Fin n) (Fin n) (ZMod 2) → Prop) :
    prob (fun ω : Pairs n → Bool => P (modP 2 (symOf 1 0 ω))) =
      (Nat.card {M // IsAlt M ∧ P M} : ℝ) / Nat.card {M : Matrix (Fin n) (Fin n) (ZMod 2) // IsAlt M} := by
  unfold prob
  rw [Nat.card_congr altEquiv]
  congr 2
  exact Nat.card_congr ((Equiv.subtypeEquiv altEquiv (fun ω => Iff.rfl)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun M => IsAlt M) P))

end AltEquiv

section LawB

variable {n : ℕ}

local notation "V" => Fin n → ZMod 2
local notation "Mat" => Matrix (Fin n) (Fin n) (ZMod 2)

theorem symOf_isSymm (ω : Pairs n → Bool) : (symOf 1 0 ω).IsSymm :=
  Matrix.IsSymm.ext fun i j => symOf_comm _ _ _ j i

theorem card_span_inf_orthC_le {k : ℕ} {w : Fin (k + 1) → V} (hw : LinearIndependent (ZMod 2) w)
    (hw0 : w 0 = ones n (ZMod 2)) :
    Nat.card (Submodule.span (ZMod 2) (Set.range w) ⊓ orthC (Submodule.span (ZMod 2) (Set.range w)) :
      Submodule (ZMod 2) V) ≤ 2 ^ (k + 1 - n % 2) := by
  set S := Submodule.span (ZMod 2) (Set.range w)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  apply Nat.pow_le_pow_right (by norm_num)
  have hS : finrank (ZMod 2) S = k + 1 := by rw [finrank_span_eq_card hw, Fintype.card_fin]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h, Nat.sub_zero, ← hS]
    exact Submodule.finrank_mono inf_le_left
  · rw [h]
    have hlt : S ⊓ orthC S < S := by
      refine lt_of_le_of_ne inf_le_left fun heq => ?_
      have h0 : w 0 ∈ S ⊓ orthC S := by rw [heq]; exact Submodule.subset_span ⟨0, rfl⟩
      have := h0.2 (w 0) (Submodule.subset_span ⟨0, rfl⟩)
      rw [hw0] at this
      have h1 : ones n (ZMod 2) ⬝ᵥ ones n (ZMod 2) = (n : ZMod 2) := by simp [ones, dotProduct]
      rw [h1, ← ZMod.natCast_mod, h, Nat.cast_one] at this
      exact one_ne_zero this
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega

open Classical in
theorem card_k0_eq_le {k : ℕ} :
    Nat.card {M : Mat // IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1} * 2 ^ (n - (k + 1)) ≤
      2 ^ (k + 1 - n % 2) * Nat.card {M : Mat // IsAlt M} := by
  rw [natCard_subtype_eq_sum _ (kseq (k + 1)), natCard_subtype_eq_sum (fun M : Mat => IsAlt M)
    (kseq (k + 1)), Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  by_cases hw : LinearIndependent (ZMod 2) w
  · rw [natCard_subtype_eq_sum _ (fun M : Mat => M ^ (k + 1) *ᵥ ones n (ZMod 2)), Finset.sum_mul]
    have hz : ∀ z, Nat.card {M : Mat // ((IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧ kseq (k + 1) M = w) ∧
        M ^ (k + 1) *ᵥ ones n (ZMod 2) = z} =
        if z ∈ Submodule.span (ZMod 2) (Set.range w) then kcount (k + 1 + 1) (Fin.snoc w z) else 0 := by
      intro z
      split_ifs with hzs
      · refine Nat.card_congr (Equiv.subtypeEquivRight fun M => ?_)
        rw [kseq_succ_eq_iff, natDegree_muVec_eq_iff]
        constructor
        · rintro ⟨⟨⟨hM, -⟩, hMw⟩, hMz⟩
          exact ⟨hM, hMw, hMz⟩
        · rintro ⟨hM, hMw, hMz⟩
          refine ⟨⟨⟨hM, ?_, ?_⟩, hMw⟩, hMz⟩
          · rw [hMw]; exact hw
          · rw [hMw, hMz]; exact hzs
      · have : IsEmpty {M : Mat // ((IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧ kseq (k + 1) M = w) ∧
            M ^ (k + 1) *ᵥ ones n (ZMod 2) = z} := by
          refine ⟨fun M => hzs ?_⟩
          obtain ⟨⟨⟨-, hk⟩, hMw⟩, hMz⟩ := M.2
          have := ((natDegree_muVec_eq_iff M.1 (k + 1)).1 hk).2
          rwa [hMw, hMz] at this
        exact Nat.card_of_isEmpty
    simp_rw [hz]
    have h84 : ∀ z, (if z ∈ Submodule.span (ZMod 2) (Set.range w) then
        kcount (k + 1 + 1) (Fin.snoc w z) else 0) * 2 ^ (n - (k + 1)) =
        if z ∈ Submodule.span (ZMod 2) (Set.range w) ⊓ orthC (Submodule.span (ZMod 2) (Set.range w))
        then kcount (k + 1) w else 0 := by
      intro z
      split_ifs with h1 h2 h2
      · rw [lem_krylov hw z, ite_eq_left (Submodule.mem_inf.1 h2).2]
      · rw [lem_krylov hw z, ite_eq_right (fun h => h2 (Submodule.mem_inf.2 ⟨h1, h⟩))]
      · exact absurd h2.1 h1
      · rw [zero_mul]
    simp_rw [h84]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    by_cases hc : kcount (k + 1) w = 0
    · rw [hc, mul_zero]; exact Nat.zero_le _
    ·
      obtain ⟨⟨M₀, -, hw₀⟩⟩ : Nonempty {M : Mat // IsAlt M ∧ kseq (k + 1) M = w} := by
        by_contra h
        rw [not_nonempty_iff] at h
        exact hc Nat.card_of_isEmpty
      have hw0 : w 0 = ones n (ZMod 2) := by rw [← hw₀]; simp [kseq]
      have hcard := card_span_inf_orthC_le hw hw0
      have h1 : (Finset.univ.filter fun z => z ∈ Submodule.span (ZMod 2) (Set.range w) ⊓
          orthC (Submodule.span (ZMod 2) (Set.range w))).card =
          Nat.card (Submodule.span (ZMod 2) (Set.range w) ⊓
            orthC (Submodule.span (ZMod 2) (Set.range w)) : Submodule (ZMod 2) V) := by
        rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
      rw [h1]
      exact Nat.mul_le_mul_right _ hcard
  · have : Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧ kseq (k + 1) M = w} = 0 := by
      have : IsEmpty {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧ kseq (k + 1) M = w} := by
        refine ⟨fun M => hw ?_⟩
        obtain ⟨⟨-, hk⟩, hMw⟩ := M.2
        rw [← hMw]
        exact ((natDegree_muVec_eq_iff M.1 (k + 1)).1 hk).1
      exact Nat.card_of_isEmpty
    rw [this, zero_mul]
    exact Nat.zero_le _

theorem prob_k0_eq_le {k : ℕ} (hk : 1 ≤ k) :
    prob (fun ω : Pairs n → Bool => (muVec (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))).natDegree = k) ≤
      (1 / 4 : ℝ) ^ ((n + 1) / 2 - k) := by
  by_cases hkκ : k ≤ (n + 1) / 2
  · rw [prob_eq_alt (fun M => (muVec M (ones n (ZMod 2))).natDegree = k)]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hc := card_k0_eq_le (n := n) (k := k')
    have hpos : (0 : ℝ) < Nat.card {M : Mat // IsAlt M} := by
      have : Nonempty {M : Mat // IsAlt M} := ⟨⟨0, transpose_zero, fun i => rfl⟩⟩
      exact_mod_cast Nat.card_pos
    rw [div_le_iff₀ hpos]
    have hc' : (Nat.card {M : Mat // IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k' + 1} : ℝ) * 2 ^ (n - (k' + 1)) ≤
        2 ^ (k' + 1 - n % 2) * Nat.card {M : Mat // IsAlt M} := by exact_mod_cast hc
    have hexp : n - (k' + 1) = (k' + 1 - n % 2) + 2 * ((n + 1) / 2 - (k' + 1)) := by omega
    rw [hexp, pow_add, pow_mul] at hc'
    have h4 : ((2 : ℝ) ^ 2) ^ ((n + 1) / 2 - (k' + 1)) * (1 / 4) ^ ((n + 1) / 2 - (k' + 1)) = 1 := by
      rw [← mul_pow]; norm_num
    have h2 : (0 : ℝ) < 2 ^ (k' + 1 - n % 2) := by positivity
    have h5 : (Nat.card {M : Mat // IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k' + 1} : ℝ) *
        ((2 : ℝ) ^ 2) ^ ((n + 1) / 2 - (k' + 1)) ≤ Nat.card {M : Mat // IsAlt M} := by
      have := hc'
      rw [mul_comm (2 ^ (k' + 1 - n % 2) : ℝ), ← mul_assoc] at this
      nlinarith
    calc (Nat.card {M : Mat // IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k' + 1} : ℝ)
        = (Nat.card {M : Mat // IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k' + 1} : ℝ) *
            ((2 : ℝ) ^ 2) ^ ((n + 1) / 2 - (k' + 1)) * (1 / 4) ^ ((n + 1) / 2 - (k' + 1)) := by
          rw [mul_assoc, h4, mul_one]
      _ ≤ Nat.card {M : Mat // IsAlt M} * (1 / 4) ^ ((n + 1) / 2 - (k' + 1)) := by
          gcongr
      _ = (1 / 4) ^ ((n + 1) / 2 - (k' + 1)) * Nat.card {M : Mat // IsAlt M} := by ring
  · rw [show (n + 1) / 2 - k = 0 by omega, pow_zero]
    exact prob_le_one _

theorem lem_krylovlaw_b (hn : 1 ≤ n) (r : ℕ) :
    prob (fun ω : Pairs n → Bool => r ≤ (n + 1) / 2 - (muVec (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))).natDegree) ≤
      4 / 3 * (1 / 4 : ℝ) ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [pow_zero, mul_one]
    exact (prob_le_one _).trans (by norm_num)
  have hsub : ∀ ω : Pairs n → Bool, r ≤ (n + 1) / 2 - (muVec (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))).natDegree →
      ∃ i ∈ Finset.Ico r ((n + 1) / 2), (muVec (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))).natDegree = (n + 1) / 2 - i := by
    intro ω h
    have h1 := one_le_natDegree_muVec hn (modP 2 (symOf 1 0 ω))
    refine ⟨(n + 1) / 2 - (muVec (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))).natDegree, Finset.mem_Ico.2 ⟨h, by omega⟩, ?_⟩
    have h2 := (lem_krylovlaw_a (symOf_isSymm ω) (fun i => symOf_apply_self 1 0 ω i)).1
    omega
  calc prob (fun ω : Pairs n → Bool => r ≤ (n + 1) / 2 - (muVec (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))).natDegree)
      ≤ prob (fun ω : Pairs n → Bool => ∃ i ∈ Finset.Ico r ((n + 1) / 2),
          (muVec (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))).natDegree = (n + 1) / 2 - i) := prob_mono hsub
    _ ≤ ∑ i ∈ Finset.Ico r ((n + 1) / 2),
          prob (fun ω : Pairs n → Bool => (muVec (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))).natDegree = (n + 1) / 2 - i) :=
        prob_exists_le_sum _ _
    _ ≤ ∑ i ∈ Finset.Ico r ((n + 1) / 2), (1 / 4 : ℝ) ^ i := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_Ico.1 hi
        have := prob_k0_eq_le (n := n) (k := (n + 1) / 2 - i) (by omega)
        rwa [show (n + 1) / 2 - ((n + 1) / 2 - i) = i by omega] at this
    _ = (1 / 4 : ℝ) ^ r * ∑ j ∈ Finset.range ((n + 1) / 2 - r), (1 / 4 : ℝ) ^ j := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_add]
    _ ≤ (1 / 4 : ℝ) ^ r * (4 / 3) := by
        gcongr
        rw [geom_sum_eq (by norm_num)]
        have : (0 : ℝ) ≤ (1 / 4) ^ ((n + 1) / 2 - r) := by positivity
        rw [div_le_iff_of_neg (by norm_num)]
        nlinarith
    _ = 4 / 3 * (1 / 4 : ℝ) ^ r := by ring

end LawB

end DGS
