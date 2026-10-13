module

public import DGS.Core.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric

@[expose] public section

open Matrix

namespace DGS

theorem symOf_apply_lt {m : ℕ} (a b : ℤ) (ω : Pairs m → Bool) {i j : Fin m} (h : i < j) :
    symOf a b ω i j = if ω ⟨(i, j), h⟩ then a else b := by
  simp [symOf, h]

theorem symOf_apply_gt {m : ℕ} (a b : ℤ) (ω : Pairs m → Bool) {i j : Fin m} (h : j < i) :
    symOf a b ω i j = if ω ⟨(j, i), h⟩ then a else b := by
  simp [symOf, h, not_lt.2 h.le]

theorem symOf_comm {m : ℕ} (a b : ℤ) (ω : Pairs m → Bool) (i j : Fin m) :
    symOf a b ω i j = symOf a b ω j i := by
  unfold symOf
  simp only [Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.2 h.le]
  · simp
  · simp [h, not_lt.2 h.le]

@[simp] theorem symOf_apply_self {m : ℕ} (a b : ℤ) (ω : Pairs m → Bool) (i : Fin m) :
    symOf a b ω i i = 0 := by
  simp [symOf]

def IsSeidel {m : ℕ} (S : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  S.IsSymm ∧ (∀ i, S i i = 0) ∧ ∀ i j, i ≠ j → S i j = 1 ∨ S i j = -1

theorem isSeidel_seidelOf {m : ℕ} (ω : Pairs m → Bool) : IsSeidel (seidelOf ω) := by
  refine ⟨Matrix.IsSymm.ext fun i j => symOf_comm _ _ _ j i, fun i => symOf_apply_self _ _ _ i,
    fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · rw [seidelOf, symOf_apply_lt _ _ _ h]
    cases ω ⟨(i, j), h⟩ <;> simp
  · rw [seidelOf, symOf_apply_gt _ _ _ h]
    cases ω ⟨(j, i), h⟩ <;> simp

theorem seidelOf_bijective {m : ℕ} :
    Function.Bijective (fun ω : Pairs m → Bool => (⟨seidelOf ω, isSeidel_seidelOf ω⟩ :
      {S : Matrix (Fin m) (Fin m) ℤ // IsSeidel S})) := by
  constructor
  · intro ω ω' h
    funext q
    obtain ⟨⟨i, j⟩, hij⟩ := q
    have h1 := congrArg (fun S : {S : Matrix (Fin m) (Fin m) ℤ // IsSeidel S} => S.1 i j) h
    simp only [seidelOf, symOf_apply_lt _ _ _ hij] at h1
    cases hω : ω ⟨(i, j), hij⟩ <;> cases hω' : ω' ⟨(i, j), hij⟩ <;> simp_all
  · rintro ⟨S, hS⟩
    refine ⟨fun q => decide (S q.1.1 q.1.2 = 1), Subtype.ext ?_⟩
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [seidelOf, symOf_apply_lt _ _ _ h]
      rcases hS.2.2 i j h.ne with h1 | h1 <;> simp [h1]
    · simp [seidelOf, hS.2.1]
    · simp only [seidelOf, symOf_apply_gt _ _ _ h]
      rw [hS.1.apply i j]
      rcases hS.2.2 i j h.ne' with h1 | h1 <;> simp [h1]

def graphOf {m : ℕ} (ω : Pairs m → Bool) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ symOf 1 0 ω i j = 1
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [symOf_comm]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

theorem graphOf_adj_lt {m : ℕ} (ω : Pairs m → Bool) {i j : Fin m} (h : i < j) :
    (graphOf ω).Adj i j ↔ ω ⟨(i, j), h⟩ = true := by
  simp only [graphOf, symOf_apply_lt _ _ _ h]
  constructor
  · rintro ⟨-, h1⟩
    by_contra h2
    simp [h2] at h1
  · intro h1
    exact ⟨h.ne, by simp [h1]⟩

theorem graphOf_bijective {m : ℕ} : Function.Bijective (graphOf (m := m)) := by
  constructor
  · intro ω ω' h
    funext q
    obtain ⟨⟨i, j⟩, hij⟩ := q
    have h1 := graphOf_adj_lt ω hij
    have h2 := graphOf_adj_lt ω' hij
    rw [h] at h1
    cases hω : ω ⟨(i, j), hij⟩ <;> cases hω' : ω' ⟨(i, j), hij⟩ <;> simp_all
  · intro G
    classical
    refine ⟨fun q => decide (G.Adj q.1.1 q.1.2), ?_⟩
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [graphOf_adj_lt _ h]
      simp
    · simp [graphOf]
    · rw [(graphOf _).adj_comm, graphOf_adj_lt _ h, G.adj_comm]
      simp

theorem adj_graphOf {m : ℕ} (ω : Pairs m → Bool) : adj (graphOf ω) = symOf 1 0 ω := by
  classical
  ext i j
  rw [adj, SimpleGraph.adjMatrix_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [graphOf_adj_lt _ h, symOf_apply_lt _ _ _ h]
    cases ω ⟨(i, j), h⟩ <;> simp
  · simp
  · rw [(graphOf ω).adj_comm, graphOf_adj_lt _ h, symOf_apply_gt _ _ _ h]
    cases ω ⟨(j, i), h⟩ <;> simp

theorem probG_eq_prob_graphOf (m : ℕ) (P : SimpleGraph (Fin m) → Prop) :
    probG m P = prob (fun ω : Pairs m → Bool => P (graphOf ω)) :=
  (prob_equiv (Equiv.ofBijective _ graphOf_bijective) P).symm

noncomputable def seidelOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if i = j then 0 else 1 - 2 * adj G i j

theorem isSeidel_seidelOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) : IsSeidel (seidelOfGraph G) := by
  classical
  refine ⟨Matrix.IsSymm.ext fun i j => ?_, fun i => by simp [seidelOfGraph], fun i j hij => ?_⟩
  · by_cases h : i = j
    · subst h; rfl
    · simp only [seidelOfGraph, Matrix.of_apply, adj, SimpleGraph.adjMatrix_apply, ite_eq_right h,
        ite_eq_right (Ne.symm h), G.adj_comm]
  · simp only [seidelOfGraph, Matrix.of_apply, ite_eq_right hij, adj, SimpleGraph.adjMatrix_apply]
    split_ifs <;> simp

theorem seidelOfGraph_graphOf {m : ℕ} (ω : Pairs m → Bool) :
    seidelOfGraph (graphOf ω) = seidelOf (fun q => !ω q) := by
  ext i j
  simp only [seidelOfGraph, Matrix.of_apply, adj_graphOf]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [ite_eq_right h.ne, seidelOf, symOf_apply_lt _ _ _ h, symOf_apply_lt _ _ _ h]
    cases ω ⟨(i, j), h⟩ <;> simp
  · simp [seidelOf]
  · rw [ite_eq_right h.ne', seidelOf, symOf_apply_gt _ _ _ h, symOf_apply_gt _ _ _ h]
    cases ω ⟨(j, i), h⟩ <;> simp

theorem probG_seidelOfGraph (n : ℕ) (P : Matrix (Fin n) (Fin n) ℤ → Prop) :
    probG n (fun G => P (seidelOfGraph G)) = probSeidel n P := by
  rw [probG_eq_prob_graphOf, probSeidel]
  let e : (Pairs n → Bool) ≃ (Pairs n → Bool) :=
    Function.Involutive.toPerm (fun ω q => !ω q) (fun ω => by funext q; simp)
  rw [← prob_equiv e (fun ω => P (seidelOf ω))]
  congr 1
  funext ω
  rw [seidelOfGraph_graphOf]
  rfl

end DGS
