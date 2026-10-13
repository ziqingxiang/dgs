module

public import DGS.S08_Two.WangLC

@[expose] public section

open Matrix Polynomial

namespace DGS

section QForm

variable {R : Type*} [CommRing R] {n : ℕ}

def upperPart (B : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i l => if i < l then B i l else 0

theorem upperPart_add (B B' : Matrix (Fin n) (Fin n) R) :
    upperPart (B + B') = upperPart B + upperPart B' := by
  ext i l
  simp only [upperPart, of_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem upperPart_map {S : Type*} [CommRing S] (f : R →+* S) (B : Matrix (Fin n) (Fin n) R) :
    (upperPart B).map f = upperPart (B.map f) := by
  ext i l
  simp only [upperPart, of_apply, map_apply]
  split_ifs <;> simp

theorem upperPart_add_transpose {B : Matrix (Fin n) (Fin n) R} (hB : Bᵀ = B) (hd : ∀ i, B i i = 0) :
    upperPart B + (upperPart B)ᵀ = B := by
  ext a b
  simp only [upperPart, Matrix.add_apply, transpose_apply, of_apply]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [ite_eq_left h, ite_eq_right (not_lt.2 h.le), add_zero]
  · rw [ite_eq_right (lt_irrefl _), add_zero, hd]
  · rw [ite_eq_right (not_lt.2 h.le), ite_eq_left h, zero_add]
    exact congrFun (congrFun hB a) b

def qForm (B : Matrix (Fin n) (Fin n) R) (y : Fin n → R) : R := y ⬝ᵥ (upperPart B *ᵥ y)

theorem qForm_add_left (B B' : Matrix (Fin n) (Fin n) R) (y : Fin n → R) :
    qForm (B + B') y = qForm B y + qForm B' y := by
  rw [qForm, qForm, qForm, upperPart_add, add_mulVec, dotProduct_add]

@[simp] theorem qForm_zero_right (B : Matrix (Fin n) (Fin n) R) : qForm B 0 = 0 := by
  simp [qForm]

theorem dot_mulVec_eq_add {B : Matrix (Fin n) (Fin n) R} (hB : Bᵀ = B) (hd : ∀ i, B i i = 0)
    (y z : Fin n → R) :
    y ⬝ᵥ (B *ᵥ z) = y ⬝ᵥ (upperPart B *ᵥ z) + z ⬝ᵥ (upperPart B *ᵥ y) := by
  conv_lhs => rw [← upperPart_add_transpose hB hd]
  rw [add_mulVec, dotProduct_add, mulVec_transpose, dotProduct_mulVec z,
    dotProduct_comm (z ᵥ* _)]

theorem qForm_polar {B : Matrix (Fin n) (Fin n) R} (hB : Bᵀ = B) (hd : ∀ i, B i i = 0)
    (y z : Fin n → R) : qForm B (y + z) = qForm B y + qForm B z + y ⬝ᵥ (B *ᵥ z) := by
  rw [dot_mulVec_eq_add hB hd]
  simp only [qForm, mulVec_add, add_dotProduct, dotProduct_add]
  ring

theorem dot_mulVec_self_eq_two_mul {B : Matrix (Fin n) (Fin n) R} (hB : Bᵀ = B)
    (hd : ∀ i, B i i = 0) (y : Fin n → R) : y ⬝ᵥ (B *ᵥ y) = 2 * qForm B y := by
  rw [dot_mulVec_eq_add hB hd, qForm]
  ring

def offDiag (n : ℕ) (R : Type*) [CommRing R] : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i l => if i = l then 0 else 1

theorem offDiag_transpose : (offDiag n R)ᵀ = offDiag n R := by
  ext i l
  simp only [offDiag, transpose_apply, of_apply, eq_comm]

theorem offDiag_diag (i : Fin n) : offDiag n R i i = 0 := by simp [offDiag]

theorem offDiag_map {S : Type*} [CommRing S] (f : R →+* S) : (offDiag n R).map f = offDiag n S := by
  ext i l
  simp only [offDiag, map_apply, of_apply]
  split_ifs <;> simp

theorem modP_offDiag (p : ℕ) : modP p (offDiag n ℤ) = offDiag n (ZMod p) := offDiag_map _

theorem ones_dot_sq (y : Fin n → R) :
    (ones n R ⬝ᵥ y) ^ 2 = y ⬝ᵥ y + 2 * qForm (offDiag n R) y := by
  rw [← dot_mulVec_self_eq_two_mul offDiag_transpose offDiag_diag]
  have h1 : y ⬝ᵥ y + y ⬝ᵥ (offDiag n R *ᵥ y) = y ⬝ᵥ ((1 + offDiag n R) *ᵥ y) := by
    rw [add_mulVec, one_mulVec, dotProduct_add]
  have h2 : (1 + offDiag n R) *ᵥ y = fun _ => ones n R ⬝ᵥ y := by
    funext i
    simp only [mulVec, dotProduct, Matrix.add_apply, offDiag, of_apply, one_apply, ones]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [h1, h2, sq]
  simp only [dotProduct, ones, one_mul, Finset.sum_mul]

end QForm

section SqDecomp

theorem sq_decomp (f : (ZMod 2)[X]) : f = contract 2 f ^ 2 + X * contract 2 (divX f) ^ 2 := by
  rw [← ZMod.expand_card, ← ZMod.expand_card]
  ext m
  rw [coeff_add]
  rcases m with - | m
  · rw [coeff_X_mul_zero, add_zero, coeff_expand (by norm_num), ite_eq_left (dvd_zero 2),
      coeff_contract (by norm_num)]
  · rw [coeff_X_mul, coeff_expand (by norm_num), coeff_expand (by norm_num)]
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have h1 : ¬ 2 ∣ k + k + 1 := by omega
      have h2 : 2 ∣ k + k := ⟨k, by ring⟩
      rw [ite_eq_right h1, ite_eq_left h2, zero_add, coeff_contract (by norm_num), coeff_divX,
        Nat.div_mul_cancel h2]
    · have h1 : 2 ∣ 2 * k + 1 + 1 := ⟨k + 1, by ring⟩
      have h2 : ¬ 2 ∣ 2 * k + 1 := by omega
      rw [ite_eq_left h1, ite_eq_right h2, add_zero, coeff_contract (by norm_num), Nat.div_mul_cancel h1]

theorem contract_two_add (f g : (ZMod 2)[X]) : contract 2 (f + g) = contract 2 f + contract 2 g :=
  contract_add two_ne_zero f g

theorem contract_two_divX_add (f g : (ZMod 2)[X]) :
    contract 2 (divX (f + g)) = contract 2 (divX f) + contract 2 (divX g) := by
  rw [divX_add, contract_two_add]

end SqDecomp

section LambdaII

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}

theorem aeval_isSymm (hA : A.IsSymm) (g : ℤ[X]) : (aeval A g)ᵀ = aeval A g := by
  rw [aeval_eq_sum_range, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.transpose_smul, Matrix.transpose_pow, hA.eq]

theorem redVec_qForm (B : Matrix (Fin n) (Fin n) ℤ) (u : Fin n → ℤ) :
    ((qForm B u : ℤ) : ZMod 2) = qForm (modP 2 B) (redVec 2 u) := by
  rw [qForm, qForm, ← redVec_dotProduct, redVec_mulVec, modP, modP, upperPart_map]

variable (hA : A.IsSymm) (hd : ∀ i, A i i = 0) (hn : 1 ≤ n)
include hA hd hn

theorem lem_Lambda_ii (f₀ f₁ : (ZMod 2)[X]) (hodd : n % 2 = 1 → f₀.coeff 0 = 0) :
    omegaF A (f₀ ^ 2 + X * f₁ ^ 2) =
      qForm (offDiag n (ZMod 2)) (aeval (modP 2 A) f₀ *ᵥ ones n (ZMod 2)) +
        qForm (modP 2 A) (aeval (modP 2 A) f₁ *ᵥ ones n (ZMod 2)) := by
  set g₀ := liftZ 2 f₀ with hg₀
  set g₁ := liftZ 2 f₁ with hg₁
  have hmap : (g₀ ^ 2 + X * g₁ ^ 2).map (Int.castRingHom (ZMod 2)) = f₀ ^ 2 + X * f₁ ^ 2 := by
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_pow, map_X, hg₀,
      hg₁, map_liftZ, map_liftZ]
  rw [← hmap, omegaF_eq_of_lift hA hd hn]
  set u₀ := aeval A g₀ *ᵥ ones n ℤ with hu₀
  set u₁ := aeval A g₁ *ᵥ ones n ℤ with hu₁
  have hW : ones n ℤ ⬝ᵥ (aeval A (g₀ ^ 2 + X * g₁ ^ 2) *ᵥ ones n ℤ) = u₀ ⬝ᵥ u₀ + u₁ ⬝ᵥ (A *ᵥ u₁) := by
    rw [map_add, map_pow, map_mul, map_pow, aeval_X, add_mulVec, dotProduct_add, sq, sq,
      ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← hu₀, ← hu₁]
    congr 1
    · rw [dotProduct_mulVec, ← mulVec_transpose, aeval_isSymm hA, dotProduct_comm]
    · have hc : A * aeval A g₁ = aeval A g₁ * A := (aeval_mul_comm A g₁).symm
      rw [mulVec_mulVec, hc, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
        aeval_isSymm hA, dotProduct_comm]
  have h0 : (g₀ ^ 2 + X * g₁ ^ 2).coeff 0 = g₀.coeff 0 ^ 2 := by
    rw [coeff_add, coeff_X_mul_zero, add_zero, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero,
      eval_pow]
  rw [hW, h0]
  have hJ := ones_dot_sq u₀
  have hAq := dot_mulVec_self_eq_two_mul (B := A) hA.eq hd u₁
  set s := ones n ℤ ⬝ᵥ u₀ with hs
  have hs2 : (2 : ℤ) ∣ s := by
    suffices h : ((s : ℤ) : ZMod 2) = 0 by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd s 2).1 h
      simpa using this
    rw [hs, ← ones_dotProduct_redVec, hu₀,
      redVec_aeval_mulVec, hg₀, map_liftZ]
    have : redVec 2 (ones n ℤ) = ones n (ZMod 2) := by funext i; simp [redVec, ones]
    rw [this, ones_dot_aeval (modP_two_transpose hA) (modP_two_diag hd)]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [(ZMod.natCast_eq_zero_iff n 2).2 (Nat.dvd_of_mod_eq_zero h), mul_zero]
    · rw [hodd h, zero_mul]
  obtain ⟨a, ha⟩ := hs2
  have hkey : ∃ m : ℤ, s ^ 2 - ((n % 2 * n : ℕ) : ℤ) * g₀.coeff 0 ^ 2 = 4 * m := by
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · refine ⟨a ^ 2, ?_⟩
      rw [h, zero_mul, Nat.cast_zero, zero_mul, sub_zero, ha]
      ring
    · have hb : (2 : ℤ) ∣ g₀.coeff 0 := by
        suffices h : ((g₀.coeff 0 : ℤ) : ZMod 2) = 0 by
          have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h
          simpa using this
        have := congrArg (coeff · 0) (map_liftZ 2 f₀)
        simp only [coeff_map, eq_intCast] at this
        rw [← hg₀] at this
        rw [this, hodd h]
      obtain ⟨b, hb⟩ := hb
      refine ⟨a ^ 2 - n * b ^ 2, ?_⟩
      rw [h, one_mul, ha, hb]
      ring
  obtain ⟨m, hm⟩ := hkey
  have hfinal : u₀ ⬝ᵥ u₀ + u₁ ⬝ᵥ (A *ᵥ u₁) - ((n % 2 * n : ℕ) : ℤ) * g₀.coeff 0 ^ 2 =
      2 * (2 * m - qForm (offDiag n ℤ) u₀ + qForm A u₁) := by
    linear_combination hm - hJ + hAq
  rw [hfinal, Int.mul_ediv_cancel_left _ two_ne_zero]
  push_cast
  rw [redVec_qForm, redVec_qForm, modP_offDiag]
  have hred : ∀ (g : ℤ[X]) (f : (ZMod 2)[X]), g.map (Int.castRingHom (ZMod 2)) = f →
      redVec 2 (aeval A g *ᵥ ones n ℤ) = aeval (modP 2 A) f *ᵥ ones n (ZMod 2) := by
    intro g f hgf
    have h1 : redVec 2 (ones n ℤ) = ones n (ZMod 2) := by funext i; simp [redVec, ones]
    rw [redVec_aeval_mulVec, hgf, h1]
  rw [hred g₀ f₀ (map_liftZ 2 f₀), hred g₁ f₁ (map_liftZ 2 f₁)]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_mul, zero_sub, neg_eq_self_of_two_eq_zero h2]

end LambdaII

section Socle

theorem eq_of_pow_mul_eq {R : Type*} [CommRing R] [IsDomain R] {β u v : R} (hβ : Prime β)
    (hu : ¬ β ∣ u) (hv : ¬ β ∣ v) {a b : ℕ} (h : β ^ a * u = β ^ b * v) : a = b := by
  have hβ0 := hβ.ne_zero
  rcases lt_trichotomy a b with hab | rfl | hab
  · exfalso
    apply hu
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have h' : β ^ a * u = β ^ a * (β ^ k * β * v) := by rw [h]; ring
    have := mul_left_cancel₀ (pow_ne_zero a hβ0) h'
    exact ⟨β ^ k * v, by rw [this]; ring⟩
  · rfl
  · exfalso
    apply hv
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have h' : β ^ b * v = β ^ b * (β ^ k * β * u) := by rw [← h]; ring
    have := mul_left_cancel₀ (pow_ne_zero b hβ0) h'
    exact ⟨β ^ k * u, by rw [this]; ring⟩

theorem derivative_sq_decomp (f₀ f₁ : (ZMod 2)[X]) :
    derivative (f₀ ^ 2 + X * f₁ ^ 2) = f₁ ^ 2 := by
  have h2 : (C 2 : (ZMod 2)[X]) = 0 := by
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, C_0]
  rw [derivative_add, derivative_mul, derivative_X, one_mul, derivative_sq, derivative_sq, h2]
  ring

theorem lem_socle {β μ g t f f₀ f₁ : (ZMod 2)[X]} (hβ : Irreducible β) {c : ℕ} (hc : 1 ≤ c)
    (hμ : μ = β ^ c * g) (hg : ¬ β ∣ g) (ht : ¬ β ∣ t) (hf : f * β = μ ^ 2 * t)
    (hdec : f = f₀ ^ 2 + X * f₁ ^ 2) : β ^ (c - 1) ∣ f₁ ∧ ¬ β ^ c ∣ f₁ := by
  have hp := hβ.prime
  have hβ0 := hβ.ne_zero
  have hf' : f = β ^ (2 * c - 1) * (g ^ 2 * t) := by
    apply mul_right_cancel₀ hβ0
    rw [hf, hμ]
    have : β ^ (2 * c - 1) * (g ^ 2 * t) * β = β ^ (2 * c - 1 + 1) * g ^ 2 * t := by ring
    rw [this, show 2 * c - 1 + 1 = 2 * c by omega]
    ring
  set r := derivative β * (g ^ 2 * t) + β * derivative (g ^ 2 * t) with hr
  have hderiv : derivative f = β ^ (2 * c - 2) * r := by
    obtain ⟨k, hk⟩ : ∃ k, 2 * c - 1 = k + 1 := ⟨2 * c - 2, by omega⟩
    have hkeven : ((k : ℕ) : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff k 2).2 ⟨c - 1, by omega⟩
    rw [hf', derivative_mul, derivative_pow, hr, hk]
    simp only [Nat.cast_add, Nat.cast_one, hkeven, zero_add, C_1, one_mul, Nat.add_sub_cancel]
    rw [show 2 * c - 2 = k by omega, pow_succ]
    ring
  have hβ' : derivative β ≠ 0 :=
    (separable_iff_derivative_ne_zero hβ).1 (PerfectField.separable_of_irreducible hβ)
  have hβnd : ¬ β ∣ derivative β := by
    intro h
    have hdeg := natDegree_le_of_dvd h hβ'
    have hlt := natDegree_derivative_lt (p := β) (Irreducible.natDegree_pos hβ).ne'
    omega
  have hrnd : ¬ β ∣ r := by
    intro h
    have : β ∣ derivative β * (g ^ 2 * t) := by
      have h2 : β ∣ β * derivative (g ^ 2 * t) := dvd_mul_right _ _
      have := (dvd_sub h h2)
      rwa [hr, add_sub_cancel_right] at this
    rcases hp.dvd_or_dvd this with h1 | h1
    · exact hβnd h1
    · rcases hp.dvd_or_dvd h1 with h2 | h2
      · exact hg (hp.dvd_of_dvd_pow h2)
      · exact ht h2
  have hf1sq : f₁ ^ 2 = β ^ (2 * c - 2) * r := by
    rw [← hderiv, hdec, derivative_sq_decomp]
  have hf10 : f₁ ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hf1sq
    have hr0 : r ≠ 0 := fun h => hrnd (by rw [h]; exact dvd_zero β)
    exact (mul_ne_zero (pow_ne_zero _ hβ0) hr0) hf1sq.symm
  obtain ⟨a, h, hnd, rfl⟩ := WfDvdMonoid.max_power_factor hf10 hβ
  have heq : β ^ (2 * a) * h ^ 2 = β ^ (2 * c - 2) * r := by
    rw [← hf1sq]; ring
  have ha : 2 * a = 2 * c - 2 :=
    eq_of_pow_mul_eq hp (fun h2 => hnd (hp.dvd_of_dvd_pow h2)) hrnd heq
  have ha' : a = c - 1 := by omega
  refine ⟨⟨h, by rw [ha']⟩, ?_⟩
  intro hdvd
  apply hnd
  rw [ha'] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  have : β ^ (c - 1) * h = β ^ (c - 1) * (β * k) := by
    rw [hk, ← mul_assoc, ← pow_succ, show c - 1 + 1 = c by omega]
  exact ⟨k, mul_left_cancel₀ (pow_ne_zero _ hβ0) this⟩

end Socle

end DGS
