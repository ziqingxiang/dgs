module

public import DGS.Prob.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

open Matrix Polynomial

namespace DGS

theorem walkMatrix_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (f : R →+* S) : (walkMatrix A).map f = walkMatrix (A.map f) := by
  ext i j
  simp only [walkMatrix, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec, ← Matrix.map_pow]
  congr 1
  funext k
  simp [ones]

def toQ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  A.map (Int.castRingHom ℚ)

def QG {n : ℕ} (G : SimpleGraph (Fin n)) : Set (Matrix (Fin n) (Fin n) ℚ) :=
  {Q | Qᵀ * Q = 1 ∧ Q *ᵥ ones n ℚ = ones n ℚ ∧
    ∃ H : SimpleGraph (Fin n), Qᵀ * toQ (adj G) * Q = toQ (adj H)}

def IsIntegralMul {n : ℕ} (ℓ : ℕ) (Q : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ i j, ∃ z : ℤ, (ℓ : ℚ) * Q i j = z

noncomputable def level {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  sInf {ℓ : ℕ | 0 < ℓ ∧ IsIntegralMul ℓ Q}

def IsPermMatrix {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), Q = σ.permMatrix ℚ

def modP (p : ℕ) {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin m) (Fin m) (ZMod p) :=
  A.map (Int.castRingHom (ZMod p))

section Subspaces

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [CommRing F]

def IsInvariant (M : Matrix ι ι F) (U : Submodule F (ι → F)) : Prop :=
  ∀ u ∈ U, M *ᵥ u ∈ U

def IsSimpleInvariant (M : Matrix ι ι F) (U : Submodule F (ι → F)) : Prop :=
  IsInvariant M U ∧ U ≠ ⊥ ∧
    ∀ W : Submodule F (ι → F), IsInvariant M W → W ≤ U → W = ⊥ ∨ W = U

def IsTotallyIsotropic (U : Submodule F (ι → F)) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U, u ⬝ᵥ v = 0

def HasType (M : Matrix ι ι F) (U : Submodule F (ι → F)) (β : F[X]) : Prop :=
  β.Monic ∧ Irreducible β ∧ ∀ u ∈ U, aeval M β *ᵥ u = 0

end Subspaces

def IsLocalFailure (p d : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ U : Submodule (ZMod p) (Fin n → ZMod p),
    IsSimpleInvariant (modP p A) U ∧ Module.finrank (ZMod p) U = d ∧ IsTotallyIsotropic U ∧
      ∀ u ∈ U, ones n (ZMod p) ⬝ᵥ u = 0

def E (p d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  IsLocalFailure p d (adj G)

def IsRepeatedFactor (p : ℕ) {m : ℕ} (T : Matrix (Fin m) (Fin m) ℤ) (β : (ZMod p)[X]) :
    Prop :=
  β.Monic ∧ Irreducible β ∧ β ^ 2 ∣ (modP p T).charpoly

end DGS
