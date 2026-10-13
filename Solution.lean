module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import DGS.Final

@[expose] public section

open Filter Topology

namespace DGSMain

open Classical in
noncomputable def adj {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  G.adjMatrix ℤ

def SameGenSpectrum {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  (adj G).charpoly = (adj H).charpoly ∧ (adj Gᶜ).charpoly = (adj Hᶜ).charpoly

def IsDGS {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ H : SimpleGraph (Fin n), SameGenSpectrum G H → Nonempty (G ≃g H)

theorem almost_all_graphs_are_DGS :
    Tendsto (fun n : ℕ ↦ (Nat.card {G : SimpleGraph (Fin n) // IsDGS G} : ℝ) / Nat.card (SimpleGraph (Fin n)))
      atTop (𝓝 1) :=
  DGS.main

end DGSMain
