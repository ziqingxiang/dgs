module

public import DGS.Statement
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open Filter Topology Matrix

namespace DGS

noncomputable def prob {Ω : Type*} (P : Ω → Prop) : ℝ :=
  (Nat.card {ω // P ω} : ℝ) / Nat.card Ω

def ones (n : ℕ) (R : Type*) [One R] : Fin n → R := fun _ => 1

def walkMatrix {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (A ^ (j : ℕ) *ᵥ ones n R) i

def Controllable {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (walkMatrix (adj G)).det ≠ 0

abbrev Pairs (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}

def symOf {m : ℕ} (a b : ℤ) (ω : Pairs m → Bool) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun i j =>
    if h : i < j then (if ω ⟨(i, j), h⟩ then a else b)
    else if h' : j < i then (if ω ⟨(j, i), h'⟩ then a else b) else 0

def seidelOf {m : ℕ} (ω : Pairs m → Bool) : Matrix (Fin m) (Fin m) ℤ :=
  symOf 1 (-1) ω

noncomputable def probSeidel (m : ℕ) (P : Matrix (Fin m) (Fin m) ℤ → Prop) : ℝ :=
  prob (fun ω : Pairs m → Bool => P (seidelOf ω))

def TaoVuStatement : Prop :=
  Tendsto (fun m : ℕ => probSeidel m (fun S => S.charpoly.discr = 0)) atTop (𝓝 0)

def ORourkeTouriStatement : Prop :=
  Tendsto (fun n : ℕ => probG n Controllable) atTop (𝓝 1)

def addStab {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (S : Finset G) : Finset G :=
  Finset.univ.filter fun g => S.image (g + ·) = S

end DGS
