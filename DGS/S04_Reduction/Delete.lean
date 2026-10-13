module

public import DGS.S03_Prelim.Border

@[expose] public section

open Matrix Module

namespace DGS

section Delete

variable {R : Type*} {m : ℕ}

def delMat (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (i : Fin (m + 1)) : Matrix (Fin m) (Fin m) R :=
  A.submatrix i.succAbove i.succAbove

def delCol (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (i : Fin (m + 1)) : Fin m → R :=
  fun j => A (i.succAbove j) i

theorem delMat_map {S : Type*} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (i : Fin (m + 1))
    (f : R → S) : delMat (A.map f) i = (delMat A i).map f := rfl

theorem delCol_map {S : Type*} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (i : Fin (m + 1))
    (f : R → S) : delCol (A.map f) i = fun j => f (delCol A i j) := rfl

theorem delMat_transpose (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (i : Fin (m + 1)) :
    (delMat A i)ᵀ = delMat Aᵀ i := rfl

variable {F : Type*} [Field F]

theorem mulVec_succAbove (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (i : Fin (m + 1))
    (x : Fin (m + 1) → F) (j : Fin m) :
    (A *ᵥ x) (i.succAbove j) = (delMat A i *ᵥ (fun l => x (i.succAbove l))) j + delCol A i j * x i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_succAbove _ i, delMat, delCol, submatrix_apply]
  ring

theorem mulVec_self_of_symm {A : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hA : Aᵀ = A)
    (i : Fin (m + 1)) (x : Fin (m + 1) → F) :
    (A *ᵥ x) i = delCol A i ⬝ᵥ (fun l => x (i.succAbove l)) + A i i * x i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_succAbove _ i, delCol]
  have h : ∀ l, A i (i.succAbove l) = A (i.succAbove l) i := fun l => by
    conv_lhs => rw [← hA]
    rfl
  simp only [h]
  ring

def insertZero (i : Fin (m + 1)) : (Fin m → F) →ₗ[F] (Fin (m + 1) → F) where
  toFun v := Fin.insertNth i 0 v
  map_add' v w := by
    rw [← Fin.insertNth_add, add_zero]
  map_smul' c v := by
    funext k
    refine Fin.succAboveCases i ?_ (fun j => ?_) k
    · simp
    · simp

theorem insertZero_apply (i : Fin (m + 1)) (v : Fin m → F) :
    insertZero i v = Fin.insertNth i 0 v := rfl

theorem insertZero_injective (i : Fin (m + 1)) : Function.Injective (insertZero (F := F) i) := by
  intro v w h
  funext j
  have := congrFun h (i.succAbove j)
  simpa [insertZero_apply] using this

theorem insertZero_dotProduct (i : Fin (m + 1)) (v w : Fin m → F) :
    insertZero i v ⬝ᵥ insertZero i w = v ⬝ᵥ w := by
  simp [insertZero_apply, dotProduct, Fin.sum_univ_succAbove _ i]

theorem lem_delete {B : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hB : Bᵀ = B) (i : Fin (m + 1))
    (hi : ∃ w ∈ LinearMap.ker B.mulVecLin, w i ≠ 0) :
    corank (delMat B i) + 1 = corank B ∧
      (∀ v ∈ LinearMap.ker (delMat B i).mulVecLin, delCol B i ⬝ᵥ v = 0) ∧
      (∀ x : Fin (m + 1) → F, (x ∈ LinearMap.ker B.mulVecLin ∧ x i = 0) ↔
        ∃ v ∈ LinearMap.ker (delMat B i).mulVecLin, x = Fin.insertNth i 0 v) := by
  obtain ⟨w, hw, hwi⟩ := hi
  rw [mem_ker_mulVecLin] at hw
  have hBi : (delMat B i)ᵀ = delMat B i := by rw [delMat_transpose, hB]
  have hcol : delCol B i = (-(w i)⁻¹) • (delMat B i *ᵥ fun l => w (i.succAbove l)) := by
    funext j
    have h1 := mulVec_succAbove B i w j
    rw [hw, Pi.zero_apply] at h1
    have h2 : (delMat B i *ᵥ fun l => w (i.succAbove l)) j = -(delCol B i j * w i) := by
      linear_combination -h1
    rw [Pi.smul_apply, smul_eq_mul, h2]
    field_simp
  have horth : ∀ v ∈ LinearMap.ker (delMat B i).mulVecLin, delCol B i ⬝ᵥ v = 0 := by
    intro v hv
    rw [mem_ker_mulVecLin] at hv
    rw [hcol, smul_dotProduct, mulVec_dotProduct_of_symm hBi, hv, dotProduct_zero, smul_zero]
  have hchar : ∀ x : Fin (m + 1) → F, (x ∈ LinearMap.ker B.mulVecLin ∧ x i = 0) ↔
      ∃ v ∈ LinearMap.ker (delMat B i).mulVecLin, x = Fin.insertNth i 0 v := by
    intro x
    constructor
    · rintro ⟨hx, hxi⟩
      rw [mem_ker_mulVecLin] at hx
      refine ⟨fun l => x (i.succAbove l), ?_, ?_⟩
      · rw [mem_ker_mulVecLin]
        funext j
        have h1 := mulVec_succAbove B i x j
        rw [hx, hxi, mul_zero, add_zero] at h1
        exact h1.symm
      · rw [← hxi]
        exact (Fin.insertNth_self_removeNth i x).symm
    · rintro ⟨v, hv, rfl⟩
      refine ⟨?_, Fin.insertNth_apply_same _ _ _⟩
      rw [mem_ker_mulVecLin]
      have hv' := mem_ker_mulVecLin.1 hv
      funext k
      refine Fin.succAboveCases i ?_ (fun j => ?_) k
      · rw [mulVec_self_of_symm hB, Fin.insertNth_apply_same, mul_zero, add_zero, Pi.zero_apply]
        simp only [Fin.insertNth_apply_succAbove]
        exact horth v hv
      · rw [mulVec_succAbove, Fin.insertNth_apply_same, mul_zero, add_zero, Pi.zero_apply]
        simp only [Fin.insertNth_apply_succAbove]
        rw [hv', Pi.zero_apply]
  refine ⟨?_, horth, hchar⟩
  have hmap : LinearMap.ker B.mulVecLin ⊓ LinearMap.ker (dotProductLin (Pi.single i (1 : F))) =
      (LinearMap.ker (delMat B i).mulVecLin).map (insertZero i) := by
    ext x
    have hxi : x ∈ LinearMap.ker (dotProductLin (Pi.single i (1 : F))) ↔ x i = 0 := by
      rw [LinearMap.mem_ker]
      show Pi.single i (1 : F) ⬝ᵥ x = 0 ↔ x i = 0
      rw [single_dotProduct, one_mul]
    rw [Submodule.mem_inf, hxi, hchar, Submodule.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
  have hdim := finrank_inf_perp_add_one (K := LinearMap.ker B.mulVecLin) (y := Pi.single i (1 : F))
    (mem_ker_mulVecLin.2 hw) (by rw [single_dotProduct, one_mul]; exact hwi)
  rw [hmap, ← (Submodule.equivMapOfInjective _ (insertZero_injective i) _).finrank_eq] at hdim
  exact hdim

end Delete

end DGS
