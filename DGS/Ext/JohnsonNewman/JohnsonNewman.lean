module

public import DGS.Ext.JohnsonNewman.MainAngles
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

@[expose] public section

open Matrix Finset

namespace DGS

section JohnsonNewman

variable {n : ℕ}

theorem spectral_real {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ A = U * diagonal hA.eigenvalues * Uᵀ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ), ?_, ?_, ?_⟩
  · have h := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  · conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    congr 2

theorem det_conj_orthogonal {U M : Matrix (Fin n) (Fin n) ℝ} (hU : U * Uᵀ = 1) :
    (U * M * Uᵀ).det = M.det := by
  have h1 : U.det * Uᵀ.det = 1 := by rw [← det_mul, hU, det_one]
  rw [det_mul, det_mul]
  linear_combination M.det * h1

theorem adj_compl_map (G : SimpleGraph (Fin n)) :
    (adj Gᶜ).map (Int.castRingHom ℝ) =
      vecMulVec (ones n ℝ) (ones n ℝ) - 1 - (adj G).map (Int.castRingHom ℝ) := by
  classical
  ext i j
  simp only [adj, Matrix.map_apply, SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj, Matrix.sub_apply,
    vecMulVec_apply, ones, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · by_cases hG : G.Adj i j <;> simp [hij, hG]

theorem adj_isHermitian (G : SimpleGraph (Fin n)) : ((adj G).map (Int.castRingHom ℝ)).IsHermitian := by
  classical
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply, SimpleGraph.adjMatrix_apply]
  by_cases h : G.Adj i j
  · simp [h, h.symm]
  · have h' : ¬ G.Adj j i := fun h'' => h h''.symm
    simp [h, h']

theorem det_shift_sub_J {U : Matrix (Fin n) (Fin n) ℝ} (hU : U * Uᵀ = 1) (d : Fin n → ℝ) {x : ℝ}
    (hx : ∀ i, x + d i ≠ 0) :
    (x • (1 : Matrix (Fin n) (Fin n) ℝ) + U * diagonal d * Uᵀ - vecMulVec (ones n ℝ) (ones n ℝ)).det =
      (∏ i, (x + d i)) * (1 - ∑ i, (Uᵀ *ᵥ ones n ℝ) i ^ 2 / (x + d i)) := by
  set a := Uᵀ *ᵥ ones n ℝ with ha
  have hUa : U *ᵥ a = ones n ℝ := by rw [ha, mulVec_mulVec, hU, one_mulVec]
  have h1 : x • (1 : Matrix (Fin n) (Fin n) ℝ) + U * diagonal d * Uᵀ - vecMulVec (ones n ℝ) (ones n ℝ) =
      U * (diagonal (fun i => x + d i) - vecMulVec a a) * Uᵀ := by
    have h2 : diagonal (fun i => x + d i) = x • (1 : Matrix (Fin n) (Fin n) ℝ) + diagonal d := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    have h3 : U * vecMulVec a a * Uᵀ = vecMulVec (ones n ℝ) (ones n ℝ) := by
      rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose, hUa]
    rw [Matrix.mul_sub, Matrix.sub_mul, h3, h2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hU]
  rw [h1, det_conj_orthogonal hU, det_diagonal_sub_vecMulVec _ _ hx]

theorem exists_block_reflection (d a b : Fin n → ℝ)
    (hab : ∀ lam : ℝ, ∑ i ∈ univ.filter (fun i => d i = lam), a i ^ 2 =
      ∑ i ∈ univ.filter (fun i => d i = lam), b i ^ 2) :
    ∃ W : Matrix (Fin n) (Fin n) ℝ, Wᵀ = W ∧ W * W = 1 ∧ W * diagonal d = diagonal d * W ∧ W *ᵥ b = a := by
  classical
  set w : Fin n → ℝ := b - a with hw
  set s : Fin n → ℝ := fun i => ∑ j ∈ univ.filter (fun j => d j = d i), w j ^ 2 with hs
  set c : Fin n → ℝ := fun i => (s i)⁻¹ with hc
  set E : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => if d i = d j then c i * w i * w j else 0 with hE
  have hsc : ∀ i j, d i = d j → s i = s j := by
    intro i j hij
    simp only [hs, hij]
  have hcc : ∀ i j, d i = d j → c i = c j := by
    intro i j hij
    simp only [hc, hsc i j hij]
  have hcs : ∀ i, c i * c i * s i = c i := by
    intro i
    rcases eq_or_ne (s i) 0 with h0 | h0
    · simp [hc, h0]
    · simp only [hc]
      field_simp
  have hw0 : ∀ i, s i = 0 → w i = 0 := by
    intro i h0
    have h1 : w i ^ 2 ≤ s i :=
      single_le_sum (f := fun j => w j ^ 2) (fun j _ => sq_nonneg _) (mem_filter.2 ⟨mem_univ i, rfl⟩)
    rw [h0] at h1
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h1 (sq_nonneg _))
  have hET : Eᵀ = E := by
    ext i j
    simp only [hE, Matrix.transpose_apply, Matrix.of_apply]
    by_cases hij : d j = d i
    · rw [ite_eq_left hij, ite_eq_left hij.symm, hcc j i hij]
      ring
    · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij)]
  have hEE : E * E = E := by
    ext i k
    simp only [hE, Matrix.mul_apply, Matrix.of_apply]
    by_cases hik : d i = d k
    · rw [ite_eq_left hik]
      have h1 : ∑ j, (if d i = d j then c i * w i * w j else 0) * (if d j = d k then c j * w j * w k else 0) =
          ∑ j ∈ univ.filter (fun j => d j = d i), c i * c i * w i * w k * w j ^ 2 := by
        rw [sum_filter]
        refine sum_congr rfl fun j _ => ?_
        by_cases hji : d j = d i
        · rw [ite_eq_left hji.symm, ite_eq_left (hji.trans hik), ite_eq_left hji, hcc j i hji]
          ring
        · rw [ite_eq_right (Ne.symm hji), ite_eq_right hji, zero_mul]
      rw [h1, ← mul_sum, mul_comm (c i * c i * w i * w k), mul_comm (s i)⁻¹]
      have h2 := hcs i
      simp only [hs] at h2
      calc (∑ j ∈ univ.filter (fun j => d j = d i), w j ^ 2) * (c i * c i * w i * w k)
          = (c i * c i * ∑ j ∈ univ.filter (fun j => d j = d i), w j ^ 2) * (w i * w k) := by ring
        _ = c i * w i * w k := by rw [h2]; ring
    · rw [ite_eq_right hik]
      refine sum_eq_zero fun j _ => ?_
      by_cases hij : d i = d j
      · rw [ite_eq_right (fun hjk => hik (hij.trans hjk)), mul_zero]
      · rw [ite_eq_right hij, zero_mul]
  have hED : E * diagonal d = diagonal d * E := by
    ext i j
    rw [mul_diagonal, diagonal_mul]
    simp only [hE, Matrix.of_apply]
    by_cases hij : d i = d j
    · rw [ite_eq_left hij, hij]
      ring
    · rw [ite_eq_right hij, zero_mul, mul_zero]
  have hEb : E *ᵥ b = (1 / 2 : ℝ) • w := by
    funext i
    simp only [hE, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : ∑ j, (if d i = d j then c i * w i * w j else 0) * b j =
        c i * w i * ∑ j ∈ univ.filter (fun j => d j = d i), w j * b j := by
      rw [mul_sum, sum_filter]
      refine sum_congr rfl fun j _ => ?_
      by_cases hji : d j = d i
      · rw [ite_eq_left hji.symm, ite_eq_left hji]
        ring
      · rw [ite_eq_right (Ne.symm hji), ite_eq_right hji, zero_mul]
    have h2 : ∑ j ∈ univ.filter (fun j => d j = d i), w j * b j = s i / 2 := by
      have h3 := hab (d i)
      simp only [hs, hw, Pi.sub_apply]
      have h4 : ∑ j ∈ univ.filter (fun j => d j = d i), (b j - a j) ^ 2 =
          ∑ j ∈ univ.filter (fun j => d j = d i), b j ^ 2 - 2 * ∑ j ∈ univ.filter (fun j => d j = d i), a j * b j +
            ∑ j ∈ univ.filter (fun j => d j = d i), a j ^ 2 := by
        rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun j _ => by ring
      have h5 : ∑ j ∈ univ.filter (fun j => d j = d i), (b j - a j) * b j =
          ∑ j ∈ univ.filter (fun j => d j = d i), b j ^ 2 - ∑ j ∈ univ.filter (fun j => d j = d i), a j * b j := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun j _ => by ring
      rw [h4, h5, h3]
      ring
    rw [h1, h2]
    rcases eq_or_ne (s i) 0 with h0 | h0
    · rw [hw0 i h0]
      ring
    · simp only [hc]
      field_simp
  refine ⟨1 - E - E, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_one, hET]
  · have h1 : (1 - E - E) * (1 - E - E) = 1 - 4 • E + 4 • (E * E) := by noncomm_ring
    rw [h1, hEE]
    abel
  · rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hED]
  · rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hEb, hw]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

end JohnsonNewman

theorem ext_johnson_newman {n : ℕ} (G H : SimpleGraph (Fin n)) (h : SameGenSpectrum G H) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ, Qᵀ * Q = 1 ∧ Q *ᵥ ones n ℝ = ones n ℝ ∧
      Qᵀ * (adj G).map (Int.castRingHom ℝ) * Q = (adj H).map (Int.castRingHom ℝ) := by
  classical
  set A := (adj G).map (Int.castRingHom ℝ) with hAdef
  set B := (adj H).map (Int.castRingHom ℝ) with hBdef
  have hA : A.IsHermitian := adj_isHermitian G
  have hB : B.IsHermitian := adj_isHermitian H
  have hchar : A.charpoly = B.charpoly := by
    rw [hAdef, hBdef, Matrix.charpoly_map, Matrix.charpoly_map, h.1]
  have hd : hA.eigenvalues = hB.eigenvalues := (hA.eigenvalues_eq_eigenvalues_iff hB).2 hchar
  set d := hA.eigenvalues with hddef
  obtain ⟨U, hUU, hUU', hAU⟩ := spectral_real hA
  obtain ⟨V, hVV, hVV', hBV⟩ := spectral_real hB
  rw [← hd] at hBV
  set e := ones n ℝ with he
  set a := Uᵀ *ᵥ e with ha
  set b := Vᵀ *ᵥ e with hb
  have hres : ∀ x : ℝ, (∀ i, x + d i ≠ 0) → ∑ i, a i ^ 2 / (x + d i) = ∑ i, b i ^ 2 / (x + d i) := by
    intro x hx
    have h1 : ((adj Gᶜ).map (Int.castRingHom ℝ)).charpoly = ((adj Hᶜ).map (Int.castRingHom ℝ)).charpoly := by
      rw [Matrix.charpoly_map, Matrix.charpoly_map, h.2]
    have h2 := congrArg (Polynomial.eval (x - 1)) h1
    rw [Matrix.eval_charpoly, Matrix.eval_charpoly, adj_compl_map, adj_compl_map, ← hAdef, ← hBdef] at h2
    have hsc : ∀ M : Matrix (Fin n) (Fin n) ℝ, Matrix.scalar (Fin n) (x - 1) - (vecMulVec e e - 1 - M) =
        x • (1 : Matrix (Fin n) (Fin n) ℝ) + M - vecMulVec e e := by
      intro M
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, sub_smul, one_smul]
      abel
    rw [hsc, hsc, hAU, hBV, det_shift_sub_J hUU' d hx, det_shift_sub_J hVV' d hx] at h2
    have hprod : (∏ i, (x + d i)) ≠ 0 := prod_ne_zero_iff.2 fun i _ => hx i
    have h3 := mul_left_cancel₀ hprod h2
    linarith
  have hab := sum_sq_eq_of_resolvent_eq hres
  obtain ⟨W, hWT, hWW, hWD, hWb⟩ := exists_block_reflection d a b hab
  refine ⟨U * W * Vᵀ, ?_, ?_, ?_⟩
  · have hT : (U * W * Vᵀ)ᵀ = V * W * Uᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hWT, Matrix.mul_assoc]
    rw [hT]
    calc V * W * Uᵀ * (U * W * Vᵀ) = V * W * (Uᵀ * U) * W * Vᵀ := by simp only [Matrix.mul_assoc]
      _ = V * (W * W) * Vᵀ := by rw [hUU, Matrix.mul_one, Matrix.mul_assoc V W W]
      _ = 1 := by rw [hWW, Matrix.mul_one, hVV']
  · rw [← mulVec_mulVec, ← mulVec_mulVec, ← hb, hWb, ha, mulVec_mulVec, hUU', one_mulVec]
  · have hT : (U * W * Vᵀ)ᵀ = V * W * Uᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hWT, Matrix.mul_assoc]
    rw [hT, hAU, hBV]
    calc V * W * Uᵀ * (U * diagonal d * Uᵀ) * (U * W * Vᵀ)
        = V * W * (Uᵀ * U) * diagonal d * (Uᵀ * U) * W * Vᵀ := by simp only [Matrix.mul_assoc]
      _ = V * (W * diagonal d * W) * Vᵀ := by
          rw [hUU, Matrix.mul_one, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = V * diagonal d * Vᵀ := by
          rw [hWD, Matrix.mul_assoc (diagonal d) W W, hWW, Matrix.mul_one]

end DGS
