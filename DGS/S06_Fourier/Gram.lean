module

public import DGS.S06_Fourier.ShortVec

@[expose] public section

open Matrix Complex
open scoped Real

namespace DGS

section Coords

abbrev UT (r : ℕ) := {x : Fin r × Fin r // x.1 ≤ x.2}

abbrev GI (r : ℕ) := UT r ⊕ Fin r

def diagUT {r : ℕ} (i : Fin r) : UT r := ⟨(i, i), le_rfl⟩

variable {r : ℕ} {R : Type*} [CommRing R]

def coordsG (Θ : Matrix (Fin r) (Fin r) R) (u : Fin r → R) : GI r → R
  | Sum.inl x => Θ x.1.1 x.1.2
  | Sum.inr i => u i

def gramVec {n : ℕ} (W : Fin n → Fin r → R) : GI r → R :=
  coordsG (fun i j => ∑ k, W k i * W k j) (fun i => ∑ k, W k i)

def Fxi (ξ : GI r → R) (y : Fin r → R) : R :=
  ∑ x : UT r, ξ (Sum.inl x) * (y x.1.1 * y x.1.2) + ∑ i, ξ (Sum.inr i) * y i

def dotG (ξ x : GI r → R) : R := ∑ a, ξ a * x a

theorem dotG_gramVec {n : ℕ} (ξ : GI r → R) (W : Fin n → Fin r → R) :
    dotG ξ (gramVec W) = ∑ k, Fxi ξ (W k) := by
  simp only [dotG, gramVec, coordsG, Fxi, Fintype.sum_sum_type, Finset.mul_sum,
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
  · rw [Finset.sum_comm]

end Coords

section Fourier

variable {r : ℕ} {q : ℕ} [NeZero q]

noncomputable def Sxi (ξ : GI r → ZMod q) : ℂ := ∑ y : Fin r → ZMod q, ZMod.stdAddChar (Fxi ξ y)

theorem sum_W_char {n : ℕ} (ξ : GI r → ZMod q) :
    ∑ W : Fin n → Fin r → ZMod q, ZMod.stdAddChar (dotG ξ (gramVec W)) = Sxi ξ ^ n := by
  classical
  simp_rw [dotG_gramVec, addChar_map_sum]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (y : Fin r → ZMod q) => ZMod.stdAddChar (Fxi ξ y))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Sxi]

theorem card_gram_eq {n : ℕ} (x : GI r → ZMod q) :
    ((Finset.univ.filter fun W : Fin n → Fin r → ZMod q => gramVec W = x).card : ℂ) =
      ((q : ℂ) ^ Fintype.card (GI r))⁻¹ *
        ∑ ξ : GI r → ZMod q, ZMod.stdAddChar (-dotG ξ x) * Sxi ξ ^ n := by
  classical
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have h1 : ∀ W : Fin n → Fin r → ZMod q, (if gramVec W = x then (1 : ℂ) else 0) =
      ((q : ℂ) ^ Fintype.card (GI r))⁻¹ * ∑ ξ : GI r → ZMod q,
        ZMod.stdAddChar (dotG ξ (gramVec W)) * ZMod.stdAddChar (-dotG ξ x) := by
    intro W
    have h2 := sum_stdAddChar_dot (q := q) (gramVec W - x)
    have h3 : ∀ ξ : GI r → ZMod q, ZMod.stdAddChar (∑ a, ξ a * (gramVec W - x) a) =
        ZMod.stdAddChar (dotG ξ (gramVec W)) * ZMod.stdAddChar (-dotG ξ x) := by
      intro ξ
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [dotG, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    simp_rw [h3] at h2
    rw [h2]
    by_cases hW : gramVec W = x
    · rw [ite_eq_left hW, ite_eq_left (sub_eq_zero.2 hW), inv_mul_cancel₀ (pow_ne_zero _ hq)]
    · rw [ite_eq_right hW, ite_eq_right (fun h => hW (sub_eq_zero.1 h)), mul_zero]
  rw [Finset.card_filter]
  push_cast
  simp_rw [h1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [← Finset.sum_mul, sum_W_char, mul_comm]

end Fourier

section Step1

variable {r : ℕ} {R : Type*} [CommRing R]

theorem Fxi_single (ξ : GI r → R) (i : Fin r) (c : R) :
    Fxi ξ (Pi.single i c) = ξ (Sum.inl (diagUT i)) * (c * c) + ξ (Sum.inr i) * c := by
  classical
  unfold Fxi
  congr 1
  · rw [Fintype.sum_eq_single (diagUT i)]
    · simp [diagUT]
    · intro x hx
      have : ¬ (x.1.1 = i ∧ x.1.2 = i) := by
        rintro ⟨h1, h2⟩
        apply hx
        apply Subtype.ext
        simp [diagUT, Prod.ext_iff, h1, h2]
      by_cases h1 : x.1.1 = i
      · have h2 : x.1.2 ≠ i := fun h2 => this ⟨h1, h2⟩
        simp [Pi.single_apply, h2]
      · simp [Pi.single_apply, h1]
  · rw [Fintype.sum_eq_single i]
    · simp
    · intro j hj; simp [hj]

theorem diagUT_injective {r : ℕ} : Function.Injective (diagUT (r := r)) := by
  intro i j h
  have := congrArg (fun x : UT r => x.1.1) h
  simpa [diagUT] using this

theorem Fxi_single_add_single (ξ : GI r → R) {i j : Fin r} (hij : i < j) :
    Fxi ξ (Pi.single i 1 + Pi.single j 1) =
      Fxi ξ (Pi.single i 1) + Fxi ξ (Pi.single j 1) + ξ (Sum.inl ⟨(i, j), hij.le⟩) := by
  classical
  have hcross : ∑ x : UT r, ξ (Sum.inl x) * ((Pi.single i (1 : R) : Fin r → R) x.1.1 *
      (Pi.single j (1 : R) : Fin r → R) x.1.2 + (Pi.single j (1 : R) : Fin r → R) x.1.1 *
      (Pi.single i (1 : R) : Fin r → R) x.1.2) = ξ (Sum.inl ⟨(i, j), hij.le⟩) := by
    rw [Fintype.sum_eq_single ⟨(i, j), hij.le⟩]
    · have hji : j ≠ i := ne_of_gt hij
      simp [hji, hij.ne]
    · intro x hx
      have h1 : ¬ (x.1.1 = i ∧ x.1.2 = j) := by
        rintro ⟨h1, h2⟩
        exact hx (Subtype.ext (Prod.ext h1 h2))
      have h2 : ¬ (x.1.1 = j ∧ x.1.2 = i) := by
        rintro ⟨h1, h2⟩
        have := x.2
        rw [h1, h2] at this
        exact absurd hij (not_lt.2 this)
      by_cases ha : x.1.1 = i
      · have hb : x.1.2 ≠ j := fun hb => h1 ⟨ha, hb⟩
        have hc : x.1.1 ≠ j := by rw [ha]; exact hij.ne
        simp [Pi.single_apply, hb, hc]
      · by_cases hb : x.1.1 = j
        · have hc : x.1.2 ≠ i := fun hc => h2 ⟨hb, hc⟩
          simp [Pi.single_apply, ha, hc]
        · simp [Pi.single_apply, ha, hb]
  unfold Fxi
  rw [← hcross]
  simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

variable {q : ℕ} [NeZero q]

theorem exists_sq_sub_eq_two_mul (y : ZMod q) : ∃ w : ZMod q, y * y - y = 2 * w := by
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self (y.val : ℤ)
  refine ⟨(k : ZMod q), ?_⟩
  have := congrArg (Int.cast : ℤ → ZMod q) hk
  push_cast at this
  rw [ZMod.natCast_zmod_val] at this
  linear_combination this

theorem Fxi_eq_zero_iff (ξ : GI r → ZMod q) :
    (∀ y, Fxi ξ y = 0) ↔ (∀ x : UT r, x.1.1 ≠ x.1.2 → ξ (Sum.inl x) = 0) ∧
      ∀ i, ξ (Sum.inr i) = -ξ (Sum.inl (diagUT i)) ∧
        ξ (Sum.inl (diagUT i)) + ξ (Sum.inl (diagUT i)) = 0 := by
  classical
  constructor
  · intro hF
    have h1 : ∀ i, ξ (Sum.inl (diagUT i)) + ξ (Sum.inr i) = 0 := by
      intro i
      have := hF (Pi.single i 1)
      rw [Fxi_single] at this
      simpa using this
    have h2 : ∀ i, ξ (Sum.inl (diagUT i)) + ξ (Sum.inl (diagUT i)) = 0 := by
      intro i
      have h := hF (Pi.single i 2)
      rw [Fxi_single] at h
      linear_combination h - 2 * h1 i
    refine ⟨fun x hx => ?_, fun i => ⟨by linear_combination h1 i, h2 i⟩⟩
    have hlt : x.1.1 < x.1.2 := lt_of_le_of_ne x.2 hx
    have h := hF (Pi.single x.1.1 1 + Pi.single x.1.2 1)
    rw [Fxi_single_add_single ξ hlt, hF, hF, zero_add, zero_add] at h
    exact h
  · rintro ⟨hoff, hdiag⟩ y
    have hquad : ∑ x : UT r, ξ (Sum.inl x) * (y x.1.1 * y x.1.2) =
        ∑ i, ξ (Sum.inl (diagUT i)) * (y i * y i) := by
      refine (Fintype.sum_of_injective diagUT diagUT_injective _ _ ?_ ?_).symm
      · intro x hx
        have hne : x.1.1 ≠ x.1.2 := by
          intro h
          apply hx
          refine ⟨x.1.1, Subtype.ext ?_⟩
          simp [diagUT, Prod.ext_iff, h]
        rw [hoff x hne, zero_mul]
      · intro i; rfl
    unfold Fxi
    rw [hquad, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨w, hw⟩ := exists_sq_sub_eq_two_mul (y i)
    rw [(hdiag i).1]
    linear_combination ξ (Sum.inl (diagUT i)) * hw + w * (hdiag i).2

end Step1

section Main

variable {r : ℕ} {q : ℕ} [NeZero q]

abbrev Tor2 (q : ℕ) := {a : ZMod q // a + a = 0}

def xiOf (a : Fin r → Tor2 q) : GI r → ZMod q
  | Sum.inl x => if x.1.1 = x.1.2 then (a x.1.1).1 else 0
  | Sum.inr i => -(a i).1

omit [NeZero q] in
theorem xiOf_injective : Function.Injective (xiOf (r := r) (q := q)) := by
  intro a a' h
  funext i
  have := congrFun h (Sum.inl (diagUT i))
  simp only [xiOf, diagUT, ite_true] at this
  exact Subtype.ext this

def Zset (r q : ℕ) [NeZero q] : Finset (GI r → ZMod q) :=
  Finset.univ.filter fun ξ => ∀ y, Fxi ξ y = 0

theorem mem_Zset_iff (ξ : GI r → ZMod q) : ξ ∈ Zset r q ↔ ∃ a, xiOf a = ξ := by
  classical
  simp only [Zset, Finset.mem_filter, Finset.mem_univ, true_and, Fxi_eq_zero_iff]
  constructor
  · rintro ⟨hoff, hdiag⟩
    refine ⟨fun i => ⟨ξ (Sum.inl (diagUT i)), (hdiag i).2⟩, funext fun c => ?_⟩
    rcases c with x | i
    · simp only [xiOf]
      split_ifs with h
      · rw [show diagUT x.1.1 = x from Subtype.ext (by simp [diagUT, Prod.ext_iff, h])]
      · exact (hoff x h).symm
    · simp only [xiOf]
      rw [(hdiag i).1]
  · rintro ⟨a, rfl⟩
    refine ⟨fun x hx => by simp [xiOf, hx], fun i => ⟨by simp [xiOf, diagUT], ?_⟩⟩
    simp only [xiOf, diagUT, ite_true]
    exact (a i).2

theorem Zset_eq_map : Zset r q = Finset.univ.map ⟨xiOf, xiOf_injective⟩ := by
  ext ξ
  rw [mem_Zset_iff, Finset.mem_map]
  simp

omit [NeZero q] in
theorem dotG_xiOf (a : Fin r → Tor2 q) (x : GI r → ZMod q) :
    dotG (xiOf a) x = ∑ i, (a i).1 * (x (Sum.inl (diagUT i)) - x (Sum.inr i)) := by
  classical
  have h1 : ∑ u : UT r, xiOf a (Sum.inl u) * x (Sum.inl u) =
      ∑ i, (a i).1 * x (Sum.inl (diagUT i)) := by
    refine (Fintype.sum_of_injective diagUT diagUT_injective _ _ ?_ ?_).symm
    · intro u hu
      have hne : u.1.1 ≠ u.1.2 := by
        intro h
        apply hu
        refine ⟨u.1.1, Subtype.ext ?_⟩
        simp [diagUT, Prod.ext_iff, h]
      simp [xiOf, hne]
    · intro i; simp [xiOf, diagUT]
  rw [dotG, Fintype.sum_sum_type, h1]
  simp only [xiOf, mul_sub, Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib]
  ring

theorem sum_tor2_char (w : ZMod q) :
    ∑ b : Tor2 q, ZMod.stdAddChar (-(b.1 * w)) =
      if ∀ b : Tor2 q, b.1 * w = 0 then (Fintype.card (Tor2 q) : ℂ) else 0 := by
  classical
  split_ifs with h
  · simp [h, AddChar.map_zero_eq_one]
  · push Not at h
    obtain ⟨b0, hb0⟩ := h
    set S := ∑ b : Tor2 q, ZMod.stdAddChar (-(b.1 * w)) with hS
    let e : Tor2 q ≃ Tor2 q :=
      { toFun := fun b => ⟨b.1 + b0.1, by linear_combination b.2 + b0.2⟩
        invFun := fun b => ⟨b.1 - b0.1, by linear_combination b.2 - b0.2⟩
        left_inv := fun b => Subtype.ext (by simp)
        right_inv := fun b => Subtype.ext (by simp) }
    have h1 : S = ZMod.stdAddChar (-(b0.1 * w)) * S := by
      have h2 := Fintype.sum_equiv e (fun b => ZMod.stdAddChar (-((b.1 + b0.1) * w)))
        (fun b => ZMod.stdAddChar (-(b.1 * w))) (fun b => rfl)
      rw [← hS] at h2
      calc S = ∑ b : Tor2 q, ZMod.stdAddChar (-((b.1 + b0.1) * w)) := h2.symm
        _ = ∑ b : Tor2 q, ZMod.stdAddChar (-(b0.1 * w)) * ZMod.stdAddChar (-(b.1 * w)) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [← AddChar.map_add_eq_mul]
            congr 1; ring
        _ = ZMod.stdAddChar (-(b0.1 * w)) * S := by rw [hS, Finset.mul_sum]
    have h3 : ZMod.stdAddChar (-(b0.1 * w)) ≠ 1 := by
      intro h4
      rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := q))] at h4
      have := ZMod.injective_stdAddChar h4
      exact hb0 (neg_eq_zero.1 this)
    have h5 : (1 - ZMod.stdAddChar (-(b0.1 * w))) * S = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact absurd (sub_eq_zero.1 h6).symm h3
    · exact h6

def GramCoord (r q : ℕ) [NeZero q] : Finset (GI r → ZMod q) :=
  Finset.univ.filter fun x => ∀ i, ∀ b : Tor2 q, b.1 * (x (Sum.inl (diagUT i)) - x (Sum.inr i)) = 0

noncomputable def Mmain (x : GI r → ZMod q) : ℂ :=
  ((q : ℂ) ^ Fintype.card (GI r))⁻¹ * ∑ ξ ∈ Zset r q, ZMod.stdAddChar (-dotG ξ x)

theorem Mmain_eq (x : GI r → ZMod q) :
    Mmain x = if x ∈ GramCoord r q then
      ((q : ℂ) ^ Fintype.card (GI r))⁻¹ * (Fintype.card (Tor2 q) : ℂ) ^ r else 0 := by
  classical
  rw [Mmain, Zset_eq_map, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, dotG_xiOf]
  have h1 : ∀ a : Fin r → Tor2 q, ZMod.stdAddChar
      (-∑ i, (a i).1 * (x (Sum.inl (diagUT i)) - x (Sum.inr i))) =
      ∏ i, ZMod.stdAddChar (-((a i).1 * (x (Sum.inl (diagUT i)) - x (Sum.inr i)))) := by
    intro a
    rw [← Finset.sum_neg_distrib, addChar_map_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i (b : Tor2 q) =>
    ZMod.stdAddChar (-(b.1 * (x (Sum.inl (diagUT i)) - x (Sum.inr i)))))]
  simp_rw [sum_tor2_char]
  rw [Fintype.prod_ite_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [GramCoord, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> simp

theorem sum_Mmain : ∑ x : GI r → ZMod q, Mmain x = 1 := by
  classical
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [Mmain]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h1 : ∀ ξ : GI r → ZMod q, ∑ x : GI r → ZMod q, ZMod.stdAddChar (-dotG ξ x) =
      if -ξ = 0 then (q : ℂ) ^ Fintype.card (GI r) else 0 := by
    intro ξ
    rw [← sum_stdAddChar_dot (-ξ)]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    simp only [dotG, Pi.neg_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  simp_rw [h1, neg_eq_zero]
  rw [Finset.sum_ite_eq' (Zset r q) 0 (fun _ => (q : ℂ) ^ Fintype.card (GI r))]
  have h0 : (0 : GI r → ZMod q) ∈ Zset r q := by
    simp only [Zset, Finset.mem_filter, Finset.mem_univ, true_and]
    intro y; simp [Fxi]
  rw [ite_eq_left h0, inv_mul_cancel₀ (pow_ne_zero _ hq)]

theorem card_GramCoord :
    ((GramCoord r q).card : ℂ) * (Fintype.card (Tor2 q) : ℂ) ^ r = (q : ℂ) ^ Fintype.card (GI r) := by
  classical
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have h := sum_Mmain (r := r) (q := q)
  simp_rw [Mmain_eq] at h
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul] at h
  have h2 : (Finset.univ.filter fun x : GI r → ZMod q => x ∈ GramCoord r q) = GramCoord r q := by
    ext x; simp
  rw [h2] at h
  field_simp at h
  linear_combination h

end Main

section Deviation

variable {r : ℕ} {q : ℕ} [NeZero q]

theorem Sxi_of_mem_Zset {ξ : GI r → ZMod q} (hξ : ξ ∈ Zset r q) : Sxi ξ = (q : ℂ) ^ r := by
  simp only [Zset, Finset.mem_filter, Finset.mem_univ, true_and] at hξ
  simp only [Sxi, hξ, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast; ring

theorem norm_prob_gram_sub_le {n : ℕ} (x : GI r → ZMod q) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ ξ, ξ ∉ Zset r q → ‖Sxi ξ‖ ≤ c * (q : ℝ) ^ r) :
    ‖((Finset.univ.filter fun W : Fin n → Fin r → ZMod q => gramVec W = x).card : ℂ) /
        (q : ℂ) ^ (n * r) - Mmain x‖ ≤ c ^ n := by
  classical
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set A : ℂ := ((q : ℂ) ^ Fintype.card (GI r))⁻¹ with hA
  set Q : ℂ := (q : ℂ) ^ (n * r) with hQ
  have hQ0 : Q ≠ 0 := pow_ne_zero _ hq
  set R : ℂ := ∑ ξ ∈ (Zset r q)ᶜ, ZMod.stdAddChar (-dotG ξ x) * Sxi ξ ^ n with hR
  have hcard : ((Finset.univ.filter fun W : Fin n → Fin r → ZMod q => gramVec W = x).card : ℂ) =
      Q * Mmain x + A * R := by
    rw [card_gram_eq, ← Finset.sum_add_sum_compl (Zset r q), Mmain, ← hA, ← hR]
    have h1 : ∑ ξ ∈ Zset r q, ZMod.stdAddChar (-dotG ξ x) * Sxi ξ ^ n =
        Q * ∑ ξ ∈ Zset r q, ZMod.stdAddChar (-dotG ξ x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξ hξ => ?_
      rw [Sxi_of_mem_Zset hξ, hQ, ← pow_mul, mul_comm r n, mul_comm]
    rw [h1]; ring
  have hdiff : ((Finset.univ.filter fun W : Fin n → Fin r → ZMod q => gramVec W = x).card : ℂ) / Q -
      Mmain x = A * R / Q := by
    rw [hcard]; field_simp; ring
  rw [hdiff, norm_div, norm_mul]
  have hRle : ‖R‖ ≤ (q : ℝ) ^ Fintype.card (GI r) * (c ^ n * (q : ℝ) ^ (n * r)) := by
    calc ‖R‖ ≤ ∑ ξ ∈ (Zset r q)ᶜ, ‖ZMod.stdAddChar (-dotG ξ x) * Sxi ξ ^ n‖ := norm_sum_le _ _
      _ ≤ ∑ _ξ ∈ (Zset r q)ᶜ, c ^ n * (q : ℝ) ^ (n * r) := by
          refine Finset.sum_le_sum fun ξ hξ => ?_
          rw [norm_mul, AddChar.norm_apply, one_mul, norm_pow]
          calc ‖Sxi ξ‖ ^ n ≤ (c * (q : ℝ) ^ r) ^ n :=
                pow_le_pow_left₀ (norm_nonneg _) (hc ξ (Finset.mem_compl.1 hξ)) n
            _ = c ^ n * (q : ℝ) ^ (n * r) := by rw [mul_pow, ← pow_mul, mul_comm r n]
      _ = ((Zset r q)ᶜ.card : ℝ) * (c ^ n * (q : ℝ) ^ (n * r)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q : ℝ) ^ Fintype.card (GI r) * (c ^ n * (q : ℝ) ^ (n * r)) := by
          gcongr
          have h1 : (Zset r q)ᶜ.card ≤ Fintype.card (GI r → ZMod q) := Finset.card_le_univ _
          rw [Fintype.card_fun, ZMod.card] at h1
          exact_mod_cast h1
  have hAn : ‖A‖ = ((q : ℝ) ^ Fintype.card (GI r))⁻¹ := by
    rw [hA, norm_inv, norm_pow, Complex.norm_natCast]
  have hQn : ‖Q‖ = (q : ℝ) ^ (n * r) := by rw [hQ, norm_pow, Complex.norm_natCast]
  rw [hAn, hQn]
  have hqp : (0 : ℝ) < (q : ℝ) ^ Fintype.card (GI r) := by positivity
  have hqnr : (0 : ℝ) < (q : ℝ) ^ (n * r) := by positivity
  rw [div_le_iff₀ hqnr, inv_mul_le_iff₀ hqp]
  calc ‖R‖ ≤ (q : ℝ) ^ Fintype.card (GI r) * (c ^ n * (q : ℝ) ^ (n * r)) := hRle
    _ = (q : ℝ) ^ Fintype.card (GI r) * (c ^ n * (q : ℝ) ^ (n * r)) := rfl

theorem tauq_lt_one {q : ℕ} (hq : 2 ≤ q) : tauq q < 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  refine (tauq_le_exp hq).trans_lt ?_
  rw [Real.exp_lt_one_iff]
  have : (0 : ℝ) < 4 / (q : ℝ) ^ 2 := by positivity
  linarith [show -4 / (q : ℝ) ^ 2 = -(4 / (q : ℝ) ^ 2) by ring]

theorem norm_Sxi_le_of_not_mem (hq2 : 2 ≤ q) {ξ : GI r → ZMod q} (hξ : ξ ∉ Zset r q) :
    ‖Sxi ξ‖ ≤ (q : ℝ) ^ r - 2 + 2 * tauq q := by
  classical
  simp only [Zset, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hξ
  obtain ⟨y0, hy0⟩ := hξ
  have h0 : Fxi ξ 0 = 0 := by simp [Fxi]
  have hy00 : y0 ≠ 0 := by rintro rfl; exact hy0 h0
  have hmem : y0 ∈ (Finset.univ : Finset (Fin r → ZMod q)).erase 0 :=
    Finset.mem_erase.2 ⟨hy00, Finset.mem_univ _⟩
  set T := ((Finset.univ : Finset (Fin r → ZMod q)).erase 0).erase y0 with hT
  have hsum : Sxi ξ = (1 + ZMod.stdAddChar (Fxi ξ y0)) + ∑ y ∈ T, ZMod.stdAddChar (Fxi ξ y) := by
    rw [Sxi, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0), ← Finset.add_sum_erase _ _ hmem, h0,
      AddChar.map_zero_eq_one]
    ring
  have hTcard : (T.card : ℝ) = (q : ℝ) ^ r - 2 := by
    have h1 := Finset.card_erase_add_one hmem
    have h2 := Finset.card_erase_add_one (Finset.mem_univ (0 : Fin r → ZMod q))
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h2
    have h3 : T.card + 1 + 1 = q ^ r := by rw [hT, h1, h2]
    have h4 : ((T.card + 1 + 1 : ℕ) : ℝ) = ((q ^ r : ℕ) : ℝ) := by rw [h3]
    push_cast at h4
    linarith
  rw [hsum]
  calc ‖(1 + ZMod.stdAddChar (Fxi ξ y0)) + ∑ y ∈ T, ZMod.stdAddChar (Fxi ξ y)‖
      ≤ ‖1 + ZMod.stdAddChar (Fxi ξ y0)‖ + ‖∑ y ∈ T, ZMod.stdAddChar (Fxi ξ y)‖ := norm_add_le _ _
    _ ≤ 2 * tauq q + T.card := by
        gcongr
        · exact norm_one_add_stdAddChar_le hq2 hy0
        · calc ‖∑ y ∈ T, ZMod.stdAddChar (Fxi ξ y)‖ ≤ ∑ y ∈ T, ‖ZMod.stdAddChar (Fxi ξ y)‖ :=
                norm_sum_le _ _
            _ = T.card := by simp [AddChar.norm_apply]
    _ = (q : ℝ) ^ r - 2 + 2 * tauq q := by rw [hTcard]; ring

end Deviation

section Gauss

variable {r : ℕ} {p : ℕ} [hp : Fact p.Prime]

def Lvec (ξ : GI r → ZMod p) (h : Fin r → ZMod p) : Fin r → ZMod p := fun k =>
  ∑ x : UT r, ξ (Sum.inl x) *
    (h x.1.1 * (if x.1.2 = k then 1 else 0) + h x.1.2 * (if x.1.1 = k then 1 else 0))

theorem sum_mul_Lvec (ξ : GI r → ZMod p) (z h : Fin r → ZMod p) :
    ∑ k, z k * Lvec ξ h k = ∑ x : UT r, ξ (Sum.inl x) * (h x.1.1 * z x.1.2 + h x.1.2 * z x.1.1) := by
  classical
  simp only [Lvec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _),
    ite_eq_left (Finset.mem_univ _)]
  ring

theorem Fxi_add (ξ : GI r → ZMod p) (z h : Fin r → ZMod p) :
    Fxi ξ (z + h) = Fxi ξ z + Fxi ξ h + ∑ k, z k * Lvec ξ h k := by
  rw [sum_mul_Lvec]
  simp only [Fxi, Pi.add_apply]
  have h1 : ∀ x : UT r, ξ (Sum.inl x) * ((z x.1.1 + h x.1.1) * (z x.1.2 + h x.1.2)) =
      ξ (Sum.inl x) * (z x.1.1 * z x.1.2) + ξ (Sum.inl x) * (h x.1.1 * h x.1.2) +
        ξ (Sum.inl x) * (h x.1.1 * z x.1.2 + h x.1.2 * z x.1.1) := fun x => by ring
  simp_rw [h1, mul_add, Finset.sum_add_distrib]
  ring

noncomputable def LvecLin (ξ : GI r → ZMod p) : (Fin r → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p) where
  toFun := Lvec ξ
  map_add' h h' := by
    funext k
    simp only [Lvec, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  map_smul' c h := by
    funext k
    simp only [Lvec, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

theorem card_ker_Lvec_le (hp2 : p ≠ 2) {ξ : GI r → ZMod p} (x0 : UT r)
    (hx0 : ξ (Sum.inl x0) ≠ 0) :
    (Finset.univ.filter fun h : Fin r → ZMod p => Lvec ξ h = 0).card ≤ p ^ (r - 1) := by
  classical
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 this with h1 | h1
    · exact hp.out.one_lt.ne' h1
    · exact hp2 h1
  have hval : Lvec ξ (Pi.single x0.1.1 1) x0.1.2 =
      (if x0.1.1 = x0.1.2 then 2 else 1) * ξ (Sum.inl x0) := by
    unfold Lvec
    rw [Fintype.sum_eq_single x0]
    · have e1 : (Pi.single x0.1.1 (1 : ZMod p) : Fin r → ZMod p) x0.1.1 = 1 :=
        Pi.single_eq_same _ _
      by_cases h : x0.1.1 = x0.1.2
      · have e2 : (Pi.single x0.1.1 (1 : ZMod p) : Fin r → ZMod p) x0.1.2 = 1 := by
          rw [← h]; exact Pi.single_eq_same _ _
        rw [e1, e2, ite_eq_left (rfl : x0.1.2 = x0.1.2), ite_eq_left h, ite_eq_left h]
        ring
      · have e2 : (Pi.single x0.1.1 (1 : ZMod p) : Fin r → ZMod p) x0.1.2 = 0 :=
          Pi.single_eq_of_ne (Ne.symm h) _
        rw [e1, e2, ite_eq_left (rfl : x0.1.2 = x0.1.2), ite_eq_right h, ite_eq_right h]
        ring
    · intro x hx
      have hne : ¬ (x.1.1 = x0.1.1 ∧ x.1.2 = x0.1.2) := by
        rintro ⟨h1, h2⟩; exact hx (Subtype.ext (Prod.ext h1 h2))
      have hne' : ¬ (x.1.2 = x0.1.1 ∧ x.1.1 = x0.1.2) := by
        rintro ⟨h1, h2⟩
        have h3 := x.2
        have h4 := x0.2
        rw [h1, h2] at h3
        have h5 : x0.1.1 = x0.1.2 := le_antisymm h4 h3
        apply hx
        apply Subtype.ext
        rw [Prod.ext_iff]
        exact ⟨h2.trans h5.symm, h1.trans h5⟩
      by_cases ha : x.1.1 = x0.1.1
      · have hb : x.1.2 ≠ x0.1.2 := fun hb => hne ⟨ha, hb⟩
        by_cases hc : x.1.2 = x0.1.1
        · have hd : x.1.1 ≠ x0.1.2 := fun hd => hne' ⟨hc, hd⟩
          have he : x0.1.1 ≠ x0.1.2 := fun he => hb (hc.trans he)
          simp [ha, hc, he]
        · simp [ha, hb, hc]
      · by_cases hc : x.1.2 = x0.1.1
        · have hd : x.1.1 ≠ x0.1.2 := fun hd => hne' ⟨hc, hd⟩
          simp [ha, hc, hd]
        · simp [ha, hc]
  have hne : LinearMap.ker (LvecLin ξ) ≠ ⊤ := by
    intro htop
    have h1 : Pi.single x0.1.1 (1 : ZMod p) ∈ LinearMap.ker (LvecLin ξ) := htop ▸ Submodule.mem_top
    have h2 : Lvec ξ (Pi.single x0.1.1 1) = 0 := h1
    have h3 := congrFun h2 x0.1.2
    rw [hval, Pi.zero_apply] at h3
    split_ifs at h3
    · exact hx0 ((mul_eq_zero.1 h3).resolve_left h2ne)
    · exact hx0 (by simpa using h3)
  have h3 := Submodule.finrank_lt hne
  rw [Module.finrank_fin_fun] at h3
  have h4 : Fintype.card (LinearMap.ker (LvecLin ξ)) =
      p ^ Module.finrank (ZMod p) (LinearMap.ker (LvecLin ξ)) := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := LinearMap.ker (LvecLin ξ)), ZMod.card]
  calc (Finset.univ.filter fun h : Fin r → ZMod p => Lvec ξ h = 0).card
      = Fintype.card (LinearMap.ker (LvecLin ξ)) := by
        rw [Fintype.card_subtype]
        congr 1
        ext h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.mem_ker]
        rfl
    _ = p ^ Module.finrank (ZMod p) (LinearMap.ker (LvecLin ξ)) := h4
    _ ≤ p ^ (r - 1) := Nat.pow_le_pow_right hp.out.pos (by omega)

theorem norm_Sxi_sq_le (ξ : GI r → ZMod p) :
    ‖Sxi ξ‖ ^ 2 ≤ (p : ℝ) ^ r * (Finset.univ.filter fun h : Fin r → ZMod p => Lvec ξ h = 0).card := by
  classical
  have hconj : (starRingEnd ℂ) (Sxi ξ) = ∑ z : Fin r → ZMod p, ZMod.stdAddChar (-Fxi ξ z) := by
    rw [Sxi, map_sum]
    exact Finset.sum_congr rfl fun z _ => (AddChar.map_neg_eq_conj _ _).symm
  have hprod : Sxi ξ * (starRingEnd ℂ) (Sxi ξ) =
      (p : ℂ) ^ r * ∑ h ∈ Finset.univ.filter (fun h : Fin r → ZMod p => Lvec ξ h = 0),
        ZMod.stdAddChar (Fxi ξ h) := by
    rw [hconj, Sxi, Finset.sum_mul_sum, Finset.sum_comm]
    have h1 : ∀ z : Fin r → ZMod p, ∑ y : Fin r → ZMod p,
        ZMod.stdAddChar (Fxi ξ y) * ZMod.stdAddChar (-Fxi ξ z) =
        ∑ h : Fin r → ZMod p, ZMod.stdAddChar (Fxi ξ h) *
          ZMod.stdAddChar (∑ k, z k * Lvec ξ h k) := by
      intro z
      rw [← Fintype.sum_equiv (Equiv.addLeft z)
        (fun h => ZMod.stdAddChar (Fxi ξ (z + h)) * ZMod.stdAddChar (-Fxi ξ z))
        (fun y => ZMod.stdAddChar (Fxi ξ y) * ZMod.stdAddChar (-Fxi ξ z)) (fun h => rfl)]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, Fxi_add]
      congr 1; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_stdAddChar_dot, Fintype.card_fin]
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> ring
  have h2 : (‖Sxi ξ‖ ^ 2 : ℝ) = ‖Sxi ξ * (starRingEnd ℂ) (Sxi ξ)‖ := by
    rw [Complex.mul_conj, Complex.norm_real, Real.norm_eq_abs, Complex.normSq_eq_norm_sq,
      abs_of_nonneg (by positivity)]
  rw [h2, hprod, norm_mul, norm_pow, Complex.norm_natCast]
  gcongr
  calc ‖∑ h ∈ Finset.univ.filter (fun h : Fin r → ZMod p => Lvec ξ h = 0), ZMod.stdAddChar (Fxi ξ h)‖
      ≤ ∑ h ∈ Finset.univ.filter (fun h : Fin r → ZMod p => Lvec ξ h = 0),
          ‖ZMod.stdAddChar (Fxi ξ h)‖ := norm_sum_le _ _
    _ = _ := by simp [AddChar.norm_apply]

theorem norm_Sxi_le_gauss (hp2 : p ≠ 2) {ξ : GI r → ZMod p} (hξ : ξ ∉ Zset r p) :
    ‖Sxi ξ‖ ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ r := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  by_cases hquad : ∀ x : UT r, ξ (Sum.inl x) = 0
  ·
    have ht : (fun i => ξ (Sum.inr i)) ≠ 0 := by
      intro ht
      apply hξ
      have hξ0 : ξ = 0 := funext fun c => by
        rcases c with x | i
        · exact hquad x
        · exact congrFun ht i
      rw [hξ0]
      simp only [Zset, Finset.mem_filter, Finset.mem_univ, true_and]
      intro y; simp [Fxi]
    have hS : Sxi ξ = 0 := by
      have h1 := sum_stdAddChar_dot (q := p) (fun i => ξ (Sum.inr i))
      rw [ite_eq_right ht] at h1
      rw [Sxi, ← h1]
      refine Finset.sum_congr rfl fun y _ => ?_
      congr 1
      simp [Fxi, hquad, mul_comm]
    rw [hS, norm_zero]
    positivity
  · push Not at hquad
    obtain ⟨x0, hx0⟩ := hquad
    have hr : 1 ≤ r := by
      have := x0.1.1.2; omega
    have hker := card_ker_Lvec_le hp2 x0 hx0
    have hsq := norm_Sxi_sq_le ξ
    have hker' : ((Finset.univ.filter fun h : Fin r → ZMod p => Lvec ξ h = 0).card : ℝ) ≤
        (p : ℝ) ^ (r - 1) := by exact_mod_cast hker
    have h1 : ‖Sxi ξ‖ ^ 2 ≤ ((p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ r) ^ 2 := by
      have h2 : ((p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ r) ^ 2 = (p : ℝ) ^ r * (p : ℝ) ^ (r - 1) := by
        rw [mul_pow, ← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 : ℝ))), ← Real.rpow_mul hp0.le]
        have h3 : (p : ℝ) ^ r = (p : ℝ) * (p : ℝ) ^ (r - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [h3]
        norm_num
        rw [Real.rpow_neg_one]
        field_simp
      rw [h2]
      calc ‖Sxi ξ‖ ^ 2 ≤ (p : ℝ) ^ r *
            (Finset.univ.filter fun h : Fin r → ZMod p => Lvec ξ h = 0).card := hsq
        _ ≤ (p : ℝ) ^ r * (p : ℝ) ^ (r - 1) := by gcongr
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h1

end Gauss

section Final

variable {r : ℕ}

theorem card_UT : Fintype.card (UT r) = r * (r + 1) / 2 := by
  classical
  rw [Fintype.card_subtype]
  have h1 : (Finset.univ.filter fun x : Fin r × Fin r => x.1 ≤ x.2) =
      (Finset.univ.filter fun x : Fin r × Fin r => x.1 < x.2) ∪
        (Finset.univ : Finset (Fin r)).diag := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_diag]
    exact le_iff_lt_or_eq
  have h2 : Disjoint (Finset.univ.filter fun x : Fin r × Fin r => x.1 < x.2)
      (Finset.univ : Finset (Fin r)).diag := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_diag] at hx'
    exact absurd hx'.2 (ne_of_lt hx)
  have h3 : (Finset.univ.filter fun x : Fin r × Fin r => x.1 < x.2).card = r.choose 2 := by
    have := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin r)))
    rwa [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] at this
  rw [h1, Finset.card_union_of_disjoint h2, h3, Finset.diag_card, Finset.card_univ,
    Fintype.card_fin]
  have h4 : r.choose 2 + r = (r + 1).choose 2 := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
  rw [h4, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

theorem card_GI : Fintype.card (GI r) = r * (r + 3) / 2 := by
  rw [Fintype.card_sum, card_UT, Fintype.card_fin]
  have h : r * (r + 3) = r * (r + 1) + 2 * r := by ring
  rw [h, Nat.add_mul_div_left _ _ (by norm_num)]

variable {R : Type*} [CommRing R]

def fromCoords (y : GI r → R) : Matrix (Fin r) (Fin r) R × (Fin r → R) :=
  (Matrix.of fun i j => if h : i ≤ j then y (Sum.inl ⟨(i, j), h⟩)
    else y (Sum.inl ⟨(j, i), le_of_lt (not_le.1 h)⟩), fun i => y (Sum.inr i))

omit [CommRing R] in
theorem fromCoords_symm (y : GI r → R) : (fromCoords y).1ᵀ = (fromCoords y).1 := by
  ext i j
  simp only [fromCoords, transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h.le, not_le.2 h]
  · simp
  · simp [h.le, not_le.2 h]

omit [CommRing R] in
theorem coordsG_fromCoords (y : GI r → R) : coordsG (fromCoords y).1 (fromCoords y).2 = y := by
  funext c
  rcases c with x | i
  · simp [coordsG, fromCoords, x.2]
  · simp [coordsG, fromCoords]

omit [CommRing R] in
theorem fromCoords_coordsG {Θ : Matrix (Fin r) (Fin r) R} (hΘ : Θᵀ = Θ) (u : Fin r → R) :
    fromCoords (coordsG Θ u) = (Θ, u) := by
  refine Prod.ext ?_ rfl
  ext i j
  simp only [fromCoords, coordsG, Matrix.of_apply]
  split_ifs with h
  · rfl
  · have := congrFun (congrFun hΘ i) j
    simpa [transpose_apply] using this

theorem gram_iff {n : ℕ} (V : Matrix (Fin n) (Fin r) R) {Θ : Matrix (Fin r) (Fin r) R}
    (hΘ : Θᵀ = Θ) (u : Fin r → R) :
    (Vᵀ * V = Θ ∧ Vᵀ *ᵥ (fun _ => 1) = u) ↔ gramVec (fun k i => V k i) = coordsG Θ u := by
  constructor
  · rintro ⟨h1, h2⟩
    funext c
    rcases c with x | i
    · simp only [gramVec, coordsG]
      rw [← h1]
      simp [Matrix.mul_apply]
    · simp only [gramVec, coordsG]
      rw [← h2]
      simp [mulVec, dotProduct]
  · intro h
    have h' := congrArg fromCoords h
    rw [fromCoords_coordsG hΘ] at h'
    have hΘ' : (fromCoords (gramVec fun k i => V k i)).1 = Θ := congrArg Prod.fst h'
    have hu' : (fromCoords (gramVec fun k i => V k i)).2 = u := congrArg Prod.snd h'
    constructor
    · rw [← hΘ']
      ext i j
      simp only [fromCoords, gramVec, coordsG, Matrix.of_apply, Matrix.mul_apply, transpose_apply]
      split_ifs
      · rfl
      · exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · rw [← hu']
      funext i
      simp [fromCoords, gramVec, coordsG, mulVec, dotProduct]

variable {p : ℕ} [hp : Fact p.Prime]

open Classical in
noncomputable def GramSet (p q r : ℕ) [NeZero q] :
    Finset (Matrix (Fin r) (Fin r) (ZMod q) × (Fin r → ZMod q)) :=
  Finset.univ.filter fun x => x.1ᵀ = x.1 ∧ (p = 2 → ∀ i, ∃ y : ZMod q, x.1 i i - x.2 i = 2 * y)

noncomputable def muGram (p q r : ℕ) [NeZero q]
    (x : Matrix (Fin r) (Fin r) (ZMod q) × (Fin r → ZMod q)) : ℝ :=
  if x ∈ GramSet p q r then ((GramSet p q r).card : ℝ)⁻¹ else 0

theorem tor2_mul_eq_zero_iff {E : ℕ} (hE : 1 ≤ E) (w : ZMod (p ^ E)) :
    (∀ b : Tor2 (p ^ E), b.1 * w = 0) ↔ (p = 2 → ∃ y : ZMod (p ^ E), w = 2 * y) := by
  constructor
  · intro h hp2
    subst hp2
    have hT : (2 : ZMod (2 ^ E)) ^ (E - 1) + 2 ^ (E - 1) = 0 := by
      rw [← two_mul, ← pow_succ', show E - 1 + 1 = E by omega]
      exact_mod_cast ZMod.natCast_self (2 ^ E)
    have h1 := h ⟨_, hT⟩
    have h2 : ((2 ^ (E - 1) * w.val : ℕ) : ZMod (2 ^ E)) = 0 := by
      push_cast; rw [ZMod.natCast_zmod_val]; exact h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hQ : 2 ^ (E - 1) * 2 ∣ 2 ^ E := by
      rw [← pow_succ, show E - 1 + 1 = E by omega]
    have h3 : 2 ∣ w.val := (Nat.mul_dvd_mul_iff_left (by positivity)).1 (hQ.trans h2)
    obtain ⟨k, hk⟩ := h3
    refine ⟨(k : ZMod (2 ^ E)), ?_⟩
    rw [← ZMod.natCast_zmod_val w, hk]
    push_cast; ring
  · intro h b
    by_cases hp2 : p = 2
    · obtain ⟨y, hy⟩ := h hp2
      rw [hy]
      linear_combination y * b.2
    · have hcop : Nat.Coprime 2 (p ^ E) :=
        ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2)).pow_right E
      have hu : IsUnit (2 : ZMod (p ^ E)) := by
        have := (ZMod.isUnit_iff_coprime 2 (p ^ E)).2 hcop
        exact_mod_cast this
      have hb : b.1 = 0 := by
        have h1 := b.2
        rw [← two_mul] at h1
        exact (hu.mul_right_eq_zero).1 h1
      rw [hb, zero_mul]

theorem tor2_mul_eq_zero_iff_odd (hp2 : p ≠ 2) (w : ZMod p) :
    (∀ b : Tor2 p, b.1 * w = 0) ↔ (p = 2 → ∃ y : ZMod p, w = 2 * y) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 this with h1 | h1
    · exact hp.out.one_lt.ne' h1
    · exact hp2 h1
  refine ⟨fun _ h => absurd h hp2, fun _ b => ?_⟩
  have hb : b.1 = 0 := by
    have h1 := b.2
    rw [← two_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left h2
  rw [hb, zero_mul]

variable {q : ℕ} [NeZero q]

omit hp in
theorem mem_GramSet_iff (hpar : ∀ w : ZMod q, (∀ b : Tor2 q, b.1 * w = 0) ↔
      (p = 2 → ∃ y : ZMod q, w = 2 * y))
    {Θ : Matrix (Fin r) (Fin r) (ZMod q)} (hΘ : Θᵀ = Θ) (u : Fin r → ZMod q) :
    (Θ, u) ∈ GramSet p q r ↔ coordsG Θ u ∈ GramCoord r q := by
  classical
  have hR : coordsG Θ u ∈ GramCoord r q ↔ ∀ i, ∀ b : Tor2 q, b.1 * (Θ i i - u i) = 0 := by
    simp only [GramCoord, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hL : (Θ, u) ∈ GramSet p q r ↔ (p = 2 → ∀ i, ∃ y : ZMod q, Θ i i - u i = 2 * y) := by
    simp only [GramSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hΘ, h⟩⟩
  rw [hL, hR]
  constructor
  · intro h i b
    exact (hpar _).2 (fun hp2 => h hp2 i) b
  · intro h hp2 i
    exact (hpar _).1 (h i) hp2

omit hp in
theorem card_GramSet_eq (hpar : ∀ w : ZMod q, (∀ b : Tor2 q, b.1 * w = 0) ↔
      (p = 2 → ∃ y : ZMod q, w = 2 * y)) :
    (GramSet p q r).card = (GramCoord r q).card := by
  classical
  refine Finset.card_nbij' (fun x => coordsG x.1 x.2) fromCoords ?_ ?_ ?_ ?_
  · intro x hx
    have hsym : x.1ᵀ = x.1 := by
      simp only [GramSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
      exact hx.1
    exact (mem_GramSet_iff hpar hsym x.2).1 hx
  · intro y hy
    have h1 := coordsG_fromCoords y
    have hsym := fromCoords_symm y
    have : (fromCoords y) ∈ GramSet p q r := by
      rw [show fromCoords y = ((fromCoords y).1, (fromCoords y).2) from rfl,
        mem_GramSet_iff hpar hsym, h1]
      exact hy
    exact this
  · intro x hx
    have hsym : x.1ᵀ = x.1 := by
      simp only [GramSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
      exact hx.1
    exact fromCoords_coordsG hsym x.2
  · intro y _
    exact coordsG_fromCoords y

omit hp in
theorem muGram_eq_Mmain (hpar : ∀ w : ZMod q, (∀ b : Tor2 q, b.1 * w = 0) ↔
      (p = 2 → ∃ y : ZMod q, w = 2 * y))
    {Θ : Matrix (Fin r) (Fin r) (ZMod q)} (hΘ : Θᵀ = Θ) (u : Fin r → ZMod q) :
    ((muGram p q r (Θ, u) : ℝ) : ℂ) = Mmain (coordsG Θ u) := by
  classical
  rw [Mmain_eq, muGram]
  have hcard := card_GramCoord (r := r) (q := q)
  have hcardeq := card_GramSet_eq (r := r) hpar
  have hT : (Fintype.card (Tor2 q) : ℂ) ^ r ≠ 0 := by
    have : 0 < Fintype.card (Tor2 q) := Fintype.card_pos_iff.2 ⟨⟨0, add_zero 0⟩⟩
    exact pow_ne_zero _ (by exact_mod_cast this.ne')
  by_cases hmem : coordsG Θ u ∈ GramCoord r q
  · rw [ite_eq_left hmem, ite_eq_left ((mem_GramSet_iff hpar hΘ u).2 hmem), hcardeq]
    push_cast
    rw [← hcard, mul_inv, mul_assoc, inv_mul_cancel₀ hT, mul_one]
  · rw [ite_eq_right hmem, ite_eq_right (fun h => hmem ((mem_GramSet_iff hpar hΘ u).1 h))]
    simp

theorem prob_gram_eq (n : ℕ) {Θ : Matrix (Fin r) (Fin r) (ZMod q)} (hΘ : Θᵀ = Θ)
    (u : Fin r → ZMod q) :
    prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) => Vᵀ * V = Θ ∧ Vᵀ *ᵥ (fun _ => 1) = u) =
      ((Finset.univ.filter fun W : Fin n → Fin r → ZMod q => gramVec W = coordsG Θ u).card : ℝ) /
        (q : ℝ) ^ (n * r) := by
  classical
  rw [prob_congr (fun V => gram_iff V hΘ u)]
  rw [← prob_equiv (Matrix.of : (Fin n → Fin r → ZMod q) ≃ Matrix (Fin n) (Fin r) (ZMod q))]
  rw [prob_eq_card_filter]
  congr 1
  rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rw [← pow_mul, mul_comm r n]

omit hp in
theorem abs_prob_gram_sub_le (hpar : ∀ w : ZMod q, (∀ b : Tor2 q, b.1 * w = 0) ↔
      (p = 2 → ∃ y : ZMod q, w = 2 * y)) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ ξ : GI r → ZMod q, ξ ∉ Zset r q → ‖Sxi ξ‖ ≤ c * (q : ℝ) ^ r) (n : ℕ)
    (Θ : Matrix (Fin r) (Fin r) (ZMod q)) (u : Fin r → ZMod q) :
    |prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) => Vᵀ * V = Θ ∧ Vᵀ *ᵥ (fun _ => 1) = u) -
      muGram p q r (Θ, u)| ≤ c ^ n := by
  classical
  by_cases hΘ : Θᵀ = Θ
  · have h1 := norm_prob_gram_sub_le (n := n) (coordsG Θ u) hc0 hc
    rw [← muGram_eq_Mmain hpar hΘ u] at h1
    rw [prob_gram_eq n hΘ u, ← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast
    exact h1
  · have h0 : prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) =>
        Vᵀ * V = Θ ∧ Vᵀ *ᵥ (fun _ => 1) = u) = 0 := by
      rw [prob_congr (Q := fun _ => False), prob_false]
      intro V
      constructor
      · rintro ⟨h, -⟩
        apply hΘ
        rw [← h, transpose_mul, transpose_transpose]
      · intro h; exact h.elim
    have hμ : muGram p q r (Θ, u) = 0 := by
      simp only [muGram, GramSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [ite_eq_right (fun h => hΘ h.1)]
    rw [h0, hμ, sub_zero, abs_zero]
    positivity

theorem lem_gram_b (hp2 : p ≠ 2) (n : ℕ) (Θ : Matrix (Fin r) (Fin r) (ZMod p))
    (u : Fin r → ZMod p) :
    |prob (fun V : Matrix (Fin n) (Fin r) (ZMod p) => Vᵀ * V = Θ ∧ Vᵀ *ᵥ (fun _ => 1) = u) -
      muGram p p r (Θ, u)| ≤ ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ n :=
  abs_prob_gram_sub_le (fun w => tor2_mul_eq_zero_iff_odd hp2 w) (by positivity)
    (fun ξ hξ => norm_Sxi_le_gauss hp2 hξ) n Θ u

theorem card_GramSet_odd (hp2 : p ≠ 2) : (GramSet p p r).card = p ^ (r * (r + 3) / 2) := by
  have h1 := card_GramCoord (r := r) (q := p)
  have h2 : Fintype.card (Tor2 p) = 1 := by
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      rcases (Nat.dvd_prime Nat.prime_two).1 this with h1 | h1
      · exact hp.out.one_lt.ne' h1
      · exact hp2 h1
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, add_zero 0⟩, fun x => Subtype.ext ?_⟩
    have h := x.2
    rw [← two_mul] at h
    exact (mul_eq_zero.1 h).resolve_left h2ne
  rw [h2, Nat.cast_one, one_pow, mul_one, card_GI] at h1
  rw [card_GramSet_eq (fun w => tor2_mul_eq_zero_iff_odd hp2 w)]
  exact_mod_cast h1

theorem lem_gram_b_count (hp2 : p ≠ 2) (n : ℕ) :
    |((Finset.univ.filter fun V : Matrix (Fin n) (Fin r) (ZMod p) =>
        Vᵀ * V = 0 ∧ Vᵀ *ᵥ (fun _ => 1) = 0).card : ℝ) -
      (p : ℝ) ^ (n * r) / (p : ℝ) ^ (r * (r + 3) / 2)| ≤
      (p : ℝ) ^ (n * r) * ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
  classical
  have h := lem_gram_b (r := r) hp2 n 0 0
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpnr : (0 : ℝ) < (p : ℝ) ^ (n * r) := by positivity
  have hmem : ((0 : Matrix (Fin r) (Fin r) (ZMod p)), (0 : Fin r → ZMod p)) ∈ GramSet p p r := by
    simp only [GramSet, Finset.mem_filter, Finset.mem_univ, true_and, transpose_zero]
    exact fun h2 => absurd h2 hp2
  have hμ : muGram p p r (0, 0) = ((p : ℝ) ^ (r * (r + 3) / 2))⁻¹ := by
    rw [muGram, ite_eq_left hmem, card_GramSet_odd hp2]
    push_cast; rfl
  have hprob : prob (fun V : Matrix (Fin n) (Fin r) (ZMod p) =>
      Vᵀ * V = 0 ∧ Vᵀ *ᵥ (fun _ => 1) = 0) =
      ((Finset.univ.filter fun V : Matrix (Fin n) (Fin r) (ZMod p) =>
        Vᵀ * V = 0 ∧ Vᵀ *ᵥ (fun _ => 1) = 0).card : ℝ) / (p : ℝ) ^ (n * r) := by
    rw [prob_eq_card_filter]
    congr 1
    rw [show Fintype.card (Matrix (Fin n) (Fin r) (ZMod p)) =
      Fintype.card (Fin n → Fin r → ZMod p) from rfl, Fintype.card_fun, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rw [← pow_mul, mul_comm r n]
  rw [hprob, hμ] at h
  have e : ((Finset.univ.filter fun V : Matrix (Fin n) (Fin r) (ZMod p) =>
        Vᵀ * V = 0 ∧ Vᵀ *ᵥ (fun _ => 1) = 0).card : ℝ) -
      (p : ℝ) ^ (n * r) / (p : ℝ) ^ (r * (r + 3) / 2) =
      (p : ℝ) ^ (n * r) * (((Finset.univ.filter fun V : Matrix (Fin n) (Fin r) (ZMod p) =>
        Vᵀ * V = 0 ∧ Vᵀ *ᵥ (fun _ => 1) = 0).card : ℝ) / (p : ℝ) ^ (n * r) -
          ((p : ℝ) ^ (r * (r + 3) / 2))⁻¹) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hpnr]
  exact mul_le_mul_of_nonneg_left h hpnr.le

omit [NeZero q] in
theorem fromCoords_injective : Function.Injective (fromCoords (r := r) (R := ZMod q)) := by
  intro y y' h
  rw [← coordsG_fromCoords y, ← coordsG_fromCoords y', h]

omit hp in
theorem abs_prob_gram_sub_eq_zero {n : ℕ} {Θ : Matrix (Fin r) (Fin r) (ZMod q)} (hΘ : Θᵀ ≠ Θ)
    (u : Fin r → ZMod q) :
    |prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) => Vᵀ * V = Θ ∧ Vᵀ *ᵥ (fun _ => 1) = u) -
      muGram p q r (Θ, u)| = 0 := by
  classical
  have h0 : prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) =>
      Vᵀ * V = Θ ∧ Vᵀ *ᵥ (fun _ => 1) = u) = 0 := by
    rw [prob_congr (Q := fun _ => False), prob_false]
    intro V
    constructor
    · rintro ⟨h, -⟩
      apply hΘ
      rw [← h, transpose_mul, transpose_transpose]
    · intro h; exact h.elim
  have hμ : muGram p q r (Θ, u) = 0 := by
    simp only [muGram, GramSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ite_eq_right (fun h => hΘ h.1)]
  rw [h0, hμ, sub_zero, abs_zero]

omit hp in
theorem sum_abs_prob_gram_sub_le (hpar : ∀ w : ZMod q, (∀ b : Tor2 q, b.1 * w = 0) ↔
      (p = 2 → ∃ y : ZMod q, w = 2 * y)) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ ξ : GI r → ZMod q, ξ ∉ Zset r q → ‖Sxi ξ‖ ≤ c * (q : ℝ) ^ r) (n : ℕ) :
    ∑ x : Matrix (Fin r) (Fin r) (ZMod q) × (Fin r → ZMod q),
      |prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) => Vᵀ * V = x.1 ∧ Vᵀ *ᵥ (fun _ => 1) = x.2) -
        muGram p q r x| ≤ (q : ℝ) ^ (r * (r + 3) / 2) * c ^ n := by
  classical
  set F := fun x : Matrix (Fin r) (Fin r) (ZMod q) × (Fin r → ZMod q) =>
    |prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) => Vᵀ * V = x.1 ∧ Vᵀ *ᵥ (fun _ => 1) = x.2) -
      muGram p q r x| with hF
  have hzero : ∀ x ∉ Set.range (fromCoords (r := r) (R := ZMod q)), F x = 0 := by
    intro x hx
    have hΘ : x.1ᵀ ≠ x.1 := fun hs => hx ⟨coordsG x.1 x.2, fromCoords_coordsG hs x.2⟩
    exact abs_prob_gram_sub_eq_zero hΘ x.2
  rw [← Fintype.sum_of_injective fromCoords fromCoords_injective (fun y => F (fromCoords y)) F hzero
    (fun y => rfl)]
  calc ∑ y : GI r → ZMod q, F (fromCoords y) ≤ ∑ _y : GI r → ZMod q, c ^ n :=
        Finset.sum_le_sum fun y _ => abs_prob_gram_sub_le hpar hc0 hc n _ _
    _ = (q : ℝ) ^ (r * (r + 3) / 2) * c ^ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, card_GI, nsmul_eq_mul]
        push_cast; ring

theorem sum_u_Mmain (Θ : Matrix (Fin r) (Fin r) (ZMod q)) :
    ∑ u : Fin r → ZMod q, Mmain (coordsG Θ u) = ((q : ℂ) ^ Fintype.card (UT r))⁻¹ := by
  classical
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [Mmain]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h0Z : (0 : GI r → ZMod q) ∈ Zset r q := by
    simp only [Zset, Finset.mem_filter, Finset.mem_univ, true_and]
    intro y; simp [Fxi]
  have h1 : ∀ ξ ∈ Zset r q, ∑ u : Fin r → ZMod q, ZMod.stdAddChar (-dotG ξ (coordsG Θ u)) =
      if ξ = 0 then (q : ℂ) ^ r else 0 := by
    intro ξ hξ
    have hsplit : ∀ u : Fin r → ZMod q, -dotG ξ (coordsG Θ u) =
        -(∑ x : UT r, ξ (Sum.inl x) * Θ x.1.1 x.1.2) + ∑ i, u i * (-ξ (Sum.inr i)) := by
      intro u
      simp only [dotG, Fintype.sum_sum_type, coordsG]
      rw [neg_add, ← Finset.sum_neg_distrib (f := fun i => ξ (Sum.inr i) * u i)]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [hsplit, AddChar.map_add_eq_mul]
    rw [← Finset.mul_sum, sum_stdAddChar_dot, Fintype.card_fin]
    by_cases h0 : ξ = 0
    · have hz : (fun i => -ξ (Sum.inr i)) = 0 := by funext i; simp [h0]
      rw [ite_eq_left hz, ite_eq_left h0]
      simp [h0, AddChar.map_zero_eq_one]
    · have hne : (fun i => -ξ (Sum.inr i)) ≠ 0 := by
        intro h
        apply h0
        simp only [Zset, Finset.mem_filter, Finset.mem_univ, true_and, Fxi_eq_zero_iff] at hξ
        obtain ⟨hoff, hdiag⟩ := hξ
        have hinr : ∀ i, ξ (Sum.inr i) = 0 := fun i => by
          have := congrFun h i
          simpa using this
        funext c
        rcases c with x | i
        · by_cases hx : x.1.1 = x.1.2
          · have hxd : x = diagUT x.1.1 := Subtype.ext (by simp [diagUT, Prod.ext_iff, hx])
            have h2 := (hdiag x.1.1).1
            rw [hinr] at h2
            rw [hxd]
            simpa using h2.symm
          · exact hoff x hx
        · exact hinr i
      rw [ite_eq_right hne, ite_eq_right h0, mul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' (Zset r q) 0, ite_eq_left h0Z, Fintype.card_sum,
    Fintype.card_fin, pow_add, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq), mul_one]

omit hp in
theorem abs_prob_gram_fst_sub_le (hpar : ∀ w : ZMod q, (∀ b : Tor2 q, b.1 * w = 0) ↔
      (p = 2 → ∃ y : ZMod q, w = 2 * y)) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ ξ : GI r → ZMod q, ξ ∉ Zset r q → ‖Sxi ξ‖ ≤ c * (q : ℝ) ^ r) (n : ℕ)
    {Θ : Matrix (Fin r) (Fin r) (ZMod q)} (hΘ : Θᵀ = Θ) :
    |prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) => Vᵀ * V = Θ) -
      ((q : ℝ) ^ (r * (r + 1) / 2))⁻¹| ≤ (q : ℝ) ^ r * c ^ n := by
  classical
  have hsum : prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) => Vᵀ * V = Θ) =
      ∑ u : Fin r → ZMod q, prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) =>
        Vᵀ * V = Θ ∧ Vᵀ *ᵥ (fun _ => 1) = u) := by
    simp only [prob_eq_card_filter]
    rw [← Finset.sum_div]
    congr 1
    have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter
      fun V : Matrix (Fin n) (Fin r) (ZMod q) => Vᵀ * V = Θ) (t := Finset.univ)
      (f := fun V => Vᵀ *ᵥ (fun _ => (1 : ZMod q))) (fun _ _ => Finset.mem_univ _)
    rw [h]
    push_cast
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 2
    ext V
    simp
  have hμsum : ∑ u : Fin r → ZMod q, muGram p q r (Θ, u) = ((q : ℝ) ^ (r * (r + 1) / 2))⁻¹ := by
    have h := sum_u_Mmain (q := q) Θ
    simp_rw [← muGram_eq_Mmain hpar hΘ] at h
    rw [card_UT] at h
    apply Complex.ofReal_injective
    push_cast
    exact h
  rw [hsum, ← hμsum, ← Finset.sum_sub_distrib]
  calc |∑ u : Fin r → ZMod q, (prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) =>
        Vᵀ * V = Θ ∧ Vᵀ *ᵥ (fun _ => 1) = u) - muGram p q r (Θ, u))|
      ≤ ∑ u : Fin r → ZMod q, |prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) =>
        Vᵀ * V = Θ ∧ Vᵀ *ᵥ (fun _ => 1) = u) - muGram p q r (Θ, u)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u : Fin r → ZMod q, c ^ n :=
        Finset.sum_le_sum fun u _ => abs_prob_gram_sub_le hpar hc0 hc n Θ u
    _ = (q : ℝ) ^ r * c ^ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast; ring

noncomputable def cGram (q r : ℕ) : ℝ := ((q : ℝ) ^ r - 2 + 2 * tauq q) / (q : ℝ) ^ r

theorem cGram_bounds (hq2 : 2 ≤ q) (hr : 1 ≤ r) : 0 ≤ cGram q r ∧ cGram q r < 1 ∧
    ∀ ξ : GI r → ZMod q, ξ ∉ Zset r q → ‖Sxi ξ‖ ≤ cGram q r * (q : ℝ) ^ r := by
  have hq2' : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqr : (2 : ℝ) ≤ (q : ℝ) ^ r := by
    calc (2 : ℝ) ≤ (q : ℝ) := hq2'
      _ = (q : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (q : ℝ) ^ r := pow_le_pow_right₀ (by linarith) hr
  have hτ0 := tauq_nonneg hq2
  have hτ1 := tauq_lt_one hq2
  have hqpos : (0 : ℝ) < (q : ℝ) ^ r := by linarith
  refine ⟨div_nonneg (by linarith) hqpos.le, by rw [cGram, div_lt_one hqpos]; linarith,
    fun ξ hξ => ?_⟩
  rw [cGram, div_mul_cancel₀ _ hqpos.ne']
  exact norm_Sxi_le_of_not_mem hq2 hξ

theorem lem_gram_a {E : ℕ} (hE : 1 ≤ E) (hr : 1 ≤ r) : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
    (∀ n : ℕ, ∀ Θ : Matrix (Fin r) (Fin r) (ZMod (p ^ E)), ∀ u : Fin r → ZMod (p ^ E),
      |prob (fun V : Matrix (Fin n) (Fin r) (ZMod (p ^ E)) =>
          Vᵀ * V = Θ ∧ Vᵀ *ᵥ (fun _ => 1) = u) - muGram p (p ^ E) r (Θ, u)| ≤ c ^ n) ∧
    (∀ n : ℕ, ∑ x : Matrix (Fin r) (Fin r) (ZMod (p ^ E)) × (Fin r → ZMod (p ^ E)),
      |prob (fun V : Matrix (Fin n) (Fin r) (ZMod (p ^ E)) =>
          Vᵀ * V = x.1 ∧ Vᵀ *ᵥ (fun _ => 1) = x.2) - muGram p (p ^ E) r x| ≤
        ((p ^ E : ℕ) : ℝ) ^ (r * (r + 3) / 2) * c ^ n) ∧
    (∀ n : ℕ, ∀ Θ : Matrix (Fin r) (Fin r) (ZMod (p ^ E)), Θᵀ = Θ →
      |prob (fun V : Matrix (Fin n) (Fin r) (ZMod (p ^ E)) => Vᵀ * V = Θ) -
        (((p ^ E : ℕ) : ℝ) ^ (r * (r + 1) / 2))⁻¹| ≤ ((p ^ E : ℕ) : ℝ) ^ r * c ^ n) := by
  obtain ⟨hc0, hc1, hc⟩ := cGram_bounds (two_le_pow (p := p) hE) hr
  have hpar := fun w => tor2_mul_eq_zero_iff (p := p) hE w
  exact ⟨cGram (p ^ E) r, hc0, hc1, fun n Θ u => abs_prob_gram_sub_le hpar hc0 hc n Θ u,
    fun n => sum_abs_prob_gram_sub_le hpar hc0 hc n,
    fun n Θ hΘ => abs_prob_gram_fst_sub_le hpar hc0 hc n hΘ⟩

end Final

end DGS
