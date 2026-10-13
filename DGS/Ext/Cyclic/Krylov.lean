module

public import DGS.S03_Prelim.LocalFailures
public import DGS.S03_Prelim.Border

@[expose] public section

open Matrix Polynomial Module

namespace DGS

def krylovMat {R : Type*} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) R) (s : Fin k → R) :
    Matrix (Fin k) (Fin k) R :=
  Matrix.of fun i j => (M ^ (j : ℕ) *ᵥ s) i

theorem walkMatrix_eq_krylovMat {R : Type*} [CommRing R] {k : ℕ} (A : Matrix (Fin k) (Fin k) R) :
    walkMatrix A = krylovMat A (ones k R) := rfl

theorem krylovMat_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {k : ℕ}
    (M : Matrix (Fin k) (Fin k) R) (s : Fin k → R) :
    (krylovMat M s).map φ = krylovMat (M.map φ) (fun i => φ (s i)) := by
  ext i j
  simp only [krylovMat, map_apply, of_apply]
  rw [RingHom.map_mulVec, ← Matrix.map_pow]
  rfl

section Field

variable {F : Type*} [Field F] {k : ℕ}

theorem dotProduct_pow_mulVec_eq_zero {M : Matrix (Fin k) (Fin k) F} {s y : Fin k → F}
    (h : ∀ j < k, y ⬝ᵥ (M ^ j *ᵥ s) = 0) (j : ℕ) : y ⬝ᵥ (M ^ j *ᵥ s) = 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [dotProduct]
  have hχ : M.charpoly.Monic := charpoly_monic M
  have hdeg : M.charpoly.natDegree = k := by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hne1 : M.charpoly ≠ 1 := by
    intro h1
    rw [h1, natDegree_one] at hdeg
    omega
  have hr : aeval M ((X ^ j : F[X]) %ₘ M.charpoly) = M ^ j := by
    rw [aeval_modByMonic_eq_self_of_root (aeval_self_charpoly M), map_pow, aeval_X]
  have hrdeg : ((X ^ j : F[X]) %ₘ M.charpoly).natDegree < k := by
    have := natDegree_modByMonic_lt (X ^ j) hχ hne1
    rwa [hdeg] at this
  rw [← hr, aeval_eq_sum_range' hrdeg, sum_mulVec, dotProduct_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [smul_mulVec, dotProduct_smul, h i (Finset.mem_range.1 hi), smul_zero]

def perpKrylov (M : Matrix (Fin k) (Fin k) F) (s : Fin k → F) : Submodule F (Fin k → F) where
  carrier := {z | ∀ j : ℕ, z ⬝ᵥ (M ^ j *ᵥ s) = 0}
  add_mem' {a b} ha hb j := by
    rw [add_dotProduct, ha j, hb j, add_zero]
  zero_mem' j := zero_dotProduct _
  smul_mem' c a ha j := by
    rw [smul_dotProduct, ha j, smul_zero]

theorem mem_perpKrylov {M : Matrix (Fin k) (Fin k) F} {s z : Fin k → F} :
    z ∈ perpKrylov M s ↔ ∀ j : ℕ, z ⬝ᵥ (M ^ j *ᵥ s) = 0 := Iff.rfl

theorem perpKrylov_isInvariant {M : Matrix (Fin k) (Fin k) F} (hM : Mᵀ = M) (s : Fin k → F) :
    IsInvariant M (perpKrylov M s) := by
  intro z hz j
  rw [mulVec_dotProduct_of_symm hM, mulVec_mulVec, ← pow_succ']
  exact hz (j + 1)

theorem exists_simple_perp_of_det_eq_zero {M : Matrix (Fin k) (Fin k) F} (hM : Mᵀ = M) {s : Fin k → F}
    (hdet : (krylovMat M s).det = 0) :
    ∃ U : Submodule F (Fin k → F), IsSimpleInvariant M U ∧ ∀ x ∈ U, s ⬝ᵥ x = 0 := by
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have h1 : ∀ j < k, y ⬝ᵥ (M ^ j *ᵥ s) = 0 := by
    intro j hj
    have := congrFun hy ⟨j, hj⟩
    simpa [vecMul, dotProduct, krylovMat] using this
  have hyW : y ∈ perpKrylov M s := dotProduct_pow_mulVec_eq_zero h1
  have hWne : perpKrylov M s ≠ ⊥ := fun hb => hy0 (by rw [hb] at hyW; exact hyW)
  obtain ⟨U, hUW, hU⟩ := exists_simpleInvariant_le M (perpKrylov_isInvariant hM s) hWne
  refine ⟨U, hU, fun x hx => ?_⟩
  have h0 := hUW hx 0
  rw [pow_zero, one_mulVec] at h0
  rw [dotProduct_comm]
  exact h0

end Field

end DGS
