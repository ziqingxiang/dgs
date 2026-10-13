module

public import DGS.S06_Fourier.Gram

@[expose] public section

open Matrix Polynomial

namespace DGS

section Krylov

variable {F : Type*} [Field F] {n d : ℕ}

def compMat (β : F[X]) (d : ℕ) : Matrix (Fin d) (Fin d) F :=
  Matrix.of fun i j => if (j : ℕ) + 1 < d then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0)
    else -β.coeff i

def krylovN (M : Matrix (Fin n) (Fin n) F) (u : Fin n → F) (d : ℕ) : Matrix (Fin n) (Fin d) F :=
  Matrix.of fun i j => (M ^ (j : ℕ) *ᵥ u) i

theorem aeval_sum_fin (M : Matrix (Fin n) (Fin n) F) (c : Fin d → F) :
    aeval M (∑ j : Fin d, C (c j) * X ^ (j : ℕ)) = ∑ j : Fin d, c j • M ^ (j : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, aeval_C, aeval_X_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem krylovN_mulVec (M : Matrix (Fin n) (Fin n) F) (u : Fin n → F) (c : Fin d → F) :
    krylovN M u d *ᵥ c = aeval M (∑ j : Fin d, C (c j) * X ^ (j : ℕ)) *ᵥ u := by
  rw [aeval_sum_fin, sum_mulVec]
  funext i
  rw [Finset.sum_apply]
  simp only [smul_mulVec, Pi.smul_apply, smul_eq_mul]
  show ∑ j, krylovN M u d i j * c j = ∑ j, c j * (M ^ (j : ℕ) *ᵥ u) i
  simp only [krylovN, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem mul_krylovN (M : Matrix (Fin n) (Fin n) F) (u : Fin n → F) {β : F[X]} (hβ : β.Monic)
    (hd : β.natDegree = d) (hu : aeval M β *ᵥ u = 0) :
    M * krylovN M u d = krylovN M u d * compMat β d := by
  have hcoeff : β.coeff d = 1 := hd ▸ hβ.coeff_natDegree
  have hrel : M ^ d *ᵥ u = -∑ i : Fin d, β.coeff i • (M ^ (i : ℕ) *ᵥ u) := by
    have h1 : (∑ i ∈ Finset.range (d + 1), β.coeff i • M ^ i) *ᵥ u = 0 := by
      rw [← hd, ← aeval_eq_sum_range]; exact hu
    rw [Finset.sum_range_succ, hcoeff, one_smul, add_mulVec, sum_mulVec] at h1
    simp only [smul_mulVec] at h1
    rw [Fin.sum_univ_eq_sum_range (fun i => β.coeff i • (M ^ i *ᵥ u)) d, eq_neg_iff_add_eq_zero,
      add_comm]
    exact h1
  ext k j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ l, M k l * krylovN M u d l j = (M ^ ((j : ℕ) + 1) *ᵥ u) k := by
    rw [pow_succ', ← mulVec_mulVec]
    rfl
  rw [hL]
  simp only [compMat, Matrix.of_apply]
  by_cases hj : (j : ℕ) + 1 < d
  · simp only [hj, ite_true]
    rw [Fintype.sum_eq_single ⟨(j : ℕ) + 1, hj⟩]
    · simp [krylovN]
    · intro i hi
      have : (i : ℕ) ≠ (j : ℕ) + 1 := fun h => hi (Fin.ext h)
      simp [this]
  · simp only [hj, ite_false]
    have hjd : (j : ℕ) + 1 = d := by omega
    rw [hjd, hrel]
    simp only [krylovN, Matrix.of_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      mul_neg, Finset.sum_neg_distrib]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ => mul_comm _ _)

theorem krylovN_mulVec_eq_zero {M : Matrix (Fin n) (Fin n) F} {u : Fin n → F} (hu0 : u ≠ 0)
    {β : F[X]} (hirr : Irreducible β) (hd : β.natDegree = d) (hu : aeval M β *ᵥ u = 0)
    {c : Fin d → F} (hc : krylovN M u d *ᵥ c = 0) : c = 0 := by
  classical
  by_contra hc0
  set g := ∑ j : Fin d, C (c j) * X ^ (j : ℕ) with hg
  have hgdeg : g.degree < d := degree_sum_fin_lt c
  have hg0 : g ≠ 0 := by
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra h; push Not at h; exact hc0 (funext h)
    intro h
    apply hj
    have h1 := congrArg (fun f => f.coeff j) h
    simp only [hg, Polynomial.finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at h1
    rw [Finset.sum_eq_single j] at h1
    · simpa using h1
    · intro b _ hb
      have : (j : ℕ) ≠ (b : ℕ) := fun h' => hb (Fin.ext h').symm
      simp [this]
    · simp
  have hcop : IsCoprime β g := by
    rw [Irreducible.coprime_iff_not_dvd hirr]
    intro hdvd
    have h1 := Polynomial.natDegree_le_of_dvd hdvd hg0
    have h2 := (Polynomial.natDegree_lt_iff_degree_lt hg0).2 hgdeg
    omega
  obtain ⟨a, b, hab⟩ := hcop
  have hgu : aeval M g *ᵥ u = 0 := by rw [← krylovN_mulVec]; exact hc
  apply hu0
  have h1 : aeval M (a * β + b * g) *ᵥ u = u := by rw [hab, map_one, one_mulVec]
  rw [map_add, map_mul, map_mul, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hu, hgu, mulVec_zero,
    mulVec_zero, add_zero] at h1
  exact h1.symm

theorem krylovN_mulVec_mem {M : Matrix (Fin n) (Fin n) F} {U : Submodule F (Fin n → F)}
    (hU : IsInvariant M U) {u : Fin n → F} (hu : u ∈ U) (c : Fin d → F) :
    krylovN M u d *ᵥ c ∈ U := by
  have hpow : ∀ j : ℕ, M ^ j *ᵥ u ∈ U := by
    intro j
    induction j with
    | zero => simpa using hu
    | succ j ih => rw [pow_succ', ← mulVec_mulVec]; exact hU _ ih
  rw [krylovN_mulVec, aeval_sum_fin, sum_mulVec]
  exact Submodule.sum_mem _ fun j _ => by rw [smul_mulVec]; exact U.smul_mem _ (hpow j)

end Krylov

section Irr

variable (p : ℕ) [Fact p.Prime] (d : ℕ)

noncomputable def monicOfCoeffs (c : Fin d → ZMod p) : (ZMod p)[X] :=
  X ^ d + ∑ i : Fin d, C (c i) * X ^ (i : ℕ)

open Classical in
noncomputable def irrSet : Finset (ZMod p)[X] :=
  (Finset.univ.image (monicOfCoeffs p d)).filter Irreducible

noncomputable def piCount : ℕ := (irrSet p d).card

theorem piCount_le : piCount p d ≤ p ^ d := by
  classical
  calc piCount p d ≤ (Finset.univ.image (monicOfCoeffs p d)).card := Finset.card_filter_le _ _
    _ ≤ (Finset.univ : Finset (Fin d → ZMod p)).card := Finset.card_image_le
    _ = p ^ d := by rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

variable {p d}

theorem monicOfCoeffs_monic (c : Fin d → ZMod p) : (monicOfCoeffs p d c).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)

theorem monicOfCoeffs_natDegree (c : Fin d → ZMod p) : (monicOfCoeffs p d c).natDegree = d := by
  rw [monicOfCoeffs, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt c

theorem mem_irrSet_iff {β : (ZMod p)[X]} :
    β ∈ irrSet p d ↔ β.Monic ∧ Irreducible β ∧ β.natDegree = d := by
  classical
  simp only [irrSet, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨c, rfl⟩, hirr⟩
    exact ⟨monicOfCoeffs_monic c, hirr, monicOfCoeffs_natDegree c⟩
  · rintro ⟨hm, hirr, hd⟩
    refine ⟨⟨fun i => β.coeff i, ?_⟩, hirr⟩
    have h := hm.as_sum
    rw [hd] at h
    simp only [monicOfCoeffs]
    rw [Fin.sum_univ_eq_sum_range (fun i => C (β.coeff i) * X ^ i) d]
    exact h.symm

end Irr

end DGS
