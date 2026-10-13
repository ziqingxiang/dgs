module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Filter Topology

namespace DGSMain

open Classical in
/-- The adjacency matrix of a graph `G` on `Fin n`, with integer entries: the entry `(i, j)` is `1` if `i` and `j`
are adjacent in `G`, and `0` otherwise. -/
noncomputable def adj {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  G.adjMatrix ℤ

/-- `G` and `H` have the same generalized spectrum: their adjacency matrices have the same characteristic polynomial,
and so do the adjacency matrices of their complements. Adjacency matrices are real symmetric, so equal
characteristic polynomials means equal spectra (the eigenvalues with their multiplicities). -/
def SameGenSpectrum {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  (adj G).charpoly = (adj H).charpoly ∧ (adj Gᶜ).charpoly = (adj Hᶜ).charpoly

/-- `G` is determined by its generalized spectrum: every graph on the same vertex set with the same generalized
spectrum as `G` is isomorphic to `G`. -/
def IsDGS {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ H : SimpleGraph (Fin n), SameGenSpectrum G H → Nonempty (G ≃g H)

/-- Almost all graphs are determined by their generalized spectrum: the proportion of the graphs on the vertex set
`Fin n` that are determined by their generalized spectrum tends to `1` as `n → ∞`. -/
theorem almost_all_graphs_are_DGS :
    Tendsto (fun n : ℕ ↦ (Nat.card {G : SimpleGraph (Fin n) // IsDGS G} : ℝ) / Nat.card (SimpleGraph (Fin n)))
      atTop (𝓝 1) := by
  sorry

end DGSMain
