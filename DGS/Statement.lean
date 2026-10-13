module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Filter Topology

namespace DGS

open Classical in
noncomputable def adj {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  G.adjMatrix ℤ

def SameGenSpectrum {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  (adj G).charpoly = (adj H).charpoly ∧ (adj (Gᶜ)).charpoly = (adj (Hᶜ)).charpoly

def IsDGS {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ H : SimpleGraph (Fin n), SameGenSpectrum G H → Nonempty (G ≃g H)

noncomputable def probG (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (Nat.card {G : SimpleGraph (Fin n) // P G} : ℝ) / Nat.card (SimpleGraph (Fin n))

def MainStatement : Prop :=
  Tendsto (fun n : ℕ ↦ probG n IsDGS) atTop (𝓝 1)

end DGS
