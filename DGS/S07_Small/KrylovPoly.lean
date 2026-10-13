module

public import DGS.S07_Small.ZeroDensity

@[expose] public section

open Matrix

namespace DGS

variable {r : ℕ}

section Fdet

variable {R : Type*} [CommRing R]

def Fdet (Θ : Matrix (Fin r) (Fin r) R) (u : Fin r → R) (H : Matrix (Fin r) (Fin r) R) : R :=
  (krylov (Θ.adjugate * H) (Θ.adjugate *ᵥ u)).det

theorem krylov_map {S : Type*} [CommRing S] (φ : R →+* S) (B : Matrix (Fin r) (Fin r) R)
    (w : Fin r → R) : (krylov B w).map φ = krylov (B.map φ) (φ ∘ w) := by
  ext i j
  simp only [krylov, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec, Matrix.map_pow]

theorem Fdet_map {S : Type*} [CommRing S] (φ : R →+* S) (Θ : Matrix (Fin r) (Fin r) R)
    (u : Fin r → R) (H : Matrix (Fin r) (Fin r) R) :
    φ (Fdet Θ u H) = Fdet (Θ.map φ) (φ ∘ u) (H.map φ) := by
  rw [Fdet, Fdet, RingHom.map_det, RingHom.mapMatrix_apply, krylov_map, Matrix.map_mul]
  have h1 : Θ.adjugate.map φ = (Θ.map φ).adjugate := by
    have := RingHom.map_adjugate φ Θ
    rwa [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at this
  have h2 : φ ∘ (Θ.adjugate *ᵥ u) = (Θ.map φ).adjugate *ᵥ (φ ∘ u) := by
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec, h1]
  rw [h1, h2]

theorem Fdet_mul_eq {Θ : Matrix (Fin r) (Fin r) R} (hΘ : IsUnit Θ.det) (u : Fin r → R)
    (B : Matrix (Fin r) (Fin r) R) :
    Fdet Θ u (Θ * B) = (∏ j : Fin r, Θ.det ^ ((j : ℕ) + 1)) * (krylov B (Θ⁻¹ *ᵥ u)).det := by
  have hadj : Θ.adjugate = Θ.det • Θ⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hΘ, one_smul]
  have h1 : Θ.adjugate * (Θ * B) = Θ.det • B := by
    rw [hadj, smul_mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hΘ, Matrix.one_mul]
  have h2 : Θ.adjugate *ᵥ u = Θ.det • (Θ⁻¹ *ᵥ u) := by
    rw [hadj, smul_mulVec]
  rw [Fdet, h1, h2, ← det_mul_row]
  congr 1
  ext i j
  simp only [krylov, Matrix.of_apply]
  rw [smul_pow, smul_mulVec, mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, pow_succ]
  ring

end Fdet

abbrev KVar (r : ℕ) := GI r ⊕ UT r

section Coords

variable {R : Type*} [CommRing R]

def symOfUT (z : UT r → R) : Matrix (Fin r) (Fin r) R := (fromCoords (Sum.elim z (fun _ => 0))).1

def kData (x : KVar r → R) :
    Matrix (Fin r) (Fin r) R × (Fin r → R) × Matrix (Fin r) (Fin r) R :=
  ((fromCoords fun c => x (Sum.inl c)).1, (fromCoords fun c => x (Sum.inl c)).2,
    symOfUT fun c => x (Sum.inr c))

theorem fromCoords_map {S : Type*} [CommRing S] (φ : R →+* S) (y : GI r → R) :
    ((fromCoords y).1.map φ, φ ∘ (fromCoords y).2) = fromCoords (φ ∘ y) := by
  refine Prod.ext ?_ ?_
  · ext i j
    simp only [fromCoords, Matrix.map_apply, Matrix.of_apply, Function.comp_apply]
    split_ifs <;> rfl
  · funext i
    simp [fromCoords]

theorem symOfUT_map {S : Type*} [CommRing S] (φ : R →+* S) (z : UT r → R) :
    (symOfUT z).map φ = symOfUT (φ ∘ z) := by
  ext i j
  simp only [symOfUT, fromCoords, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem symOfUT_symm (z : UT r → R) : (symOfUT z)ᵀ = symOfUT z := fromCoords_symm _

end Coords

noncomputable def FKr (r : ℕ) : MvPolynomial (KVar r) ℤ :=
  Fdet (kData (fun c => MvPolynomial.X c)).1 (kData (fun c => MvPolynomial.X c)).2.1
    (kData (fun c => MvPolynomial.X c)).2.2

theorem eval_FKr {S : Type*} [CommRing S] (x : KVar r → S) :
    MvPolynomial.eval₂ (Int.castRingHom S) x (FKr r) =
      Fdet (kData x).1 (kData x).2.1 (kData x).2.2 := by
  set φ := MvPolynomial.eval₂Hom (Int.castRingHom S) x with hφ
  have hX : ∀ c, φ (MvPolynomial.X c) = x c := fun c => MvPolynomial.eval₂Hom_X' _ _ _
  have e1 := fromCoords_map φ (fun c => MvPolynomial.X (Sum.inl c))
  have e2 := symOfUT_map φ (fun c => MvPolynomial.X (Sum.inr c))
  have hc1 : (φ ∘ fun c => MvPolynomial.X (Sum.inl c)) = fun c => x (Sum.inl c) := by
    funext c; exact hX _
  have hc2 : (φ ∘ fun c => MvPolynomial.X (Sum.inr c)) = fun c => x (Sum.inr c) := by
    funext c; exact hX _
  rw [hc1] at e1
  rw [hc2] at e2
  show φ (FKr r) = _
  rw [FKr, Fdet_map]
  simp only [kData]
  rw [e2]
  have e1a := congrArg Prod.fst e1
  have e1b := congrArg Prod.snd e1
  simp only at e1a e1b
  rw [e1a, e1b]

def x0Kr (r : ℕ) : KVar r → ℤ :=
  Sum.elim (coordsG (1 : Matrix (Fin r) (Fin r) ℤ) (fun _ => 1))
    (fun c => (diagonal fun i : Fin r => (2 * (i : ℕ) : ℤ)) c.1.1 c.1.2)

theorem kData_x0Kr : kData (x0Kr r) =
    ((1 : Matrix (Fin r) (Fin r) ℤ), (fun _ => 1), diagonal fun i : Fin r => (2 * (i : ℕ) : ℤ)) := by
  have h1 : (fromCoords fun c => x0Kr r (Sum.inl c)) = ((1 : Matrix (Fin r) (Fin r) ℤ), fun _ => 1) := by
    have : (fun c => x0Kr r (Sum.inl c)) = coordsG (1 : Matrix (Fin r) (Fin r) ℤ) (fun _ => 1) := by
      funext c; rfl
    rw [this, fromCoords_coordsG (by rw [transpose_one])]
  have h2 : symOfUT (fun c => x0Kr r (Sum.inr c)) = diagonal fun i : Fin r => (2 * (i : ℕ) : ℤ) := by
    have : Sum.elim (fun c => x0Kr r (Sum.inr c)) (fun _ => (0 : ℤ)) =
        coordsG (diagonal fun i : Fin r => (2 * (i : ℕ) : ℤ)) (fun _ => 0) := by
      funext c
      rcases c with c | i
      · rfl
      · rfl
    rw [symOfUT, this, fromCoords_coordsG (by rw [diagonal_transpose])]
  rw [kData, h1, h2]

theorem FKr_ne_zero (r : ℕ) : FKr r ≠ 0 := by
  intro h0
  have h1 := eval_FKr (S := ℤ) (x0Kr r)
  rw [h0, MvPolynomial.eval₂_zero, kData_x0Kr] at h1
  simp only at h1
  rw [Fdet, adjugate_one, Matrix.one_mul, one_mulVec] at h1
  have h2 : krylov (diagonal fun i : Fin r => (2 * (i : ℕ) : ℤ)) (fun _ => 1) =
      vandermonde fun i : Fin r => (2 * (i : ℕ) : ℤ) := by
    ext i j
    simp only [krylov, Matrix.of_apply, vandermonde_apply, diagonal_pow]
    rw [mulVec_diagonal, mul_one]
    rfl
  rw [h2] at h1
  have h3 : Function.Injective fun i : Fin r => (2 * (i : ℕ) : ℤ) := by
    intro i j hij
    simp only at hij
    apply Fin.ext
    omega
  exact det_vandermonde_ne_zero_iff.2 h3 h1.symm

end DGS
