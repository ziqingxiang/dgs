module

public import DGS.S14_NoFactor.Schur
public import DGS.Core.Seidel
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.LinearAlgebra.Matrix.Gershgorin

@[expose] public section

open Finset Polynomial

namespace DGS

theorem abs_coeff_le {g : ℤ[X]} (hg : g.Monic) {R : ℝ} (hR1 : 1 ≤ R)
    (hR : ∀ α ∈ (g.map (Int.castRingHom ℂ)).roots, ‖α‖ ≤ R) (k : ℕ) :
    |(g.coeff k : ℝ)| ≤ 2 ^ g.natDegree * R ^ g.natDegree := by
  set G := g.map (Int.castRingHom ℂ) with hG
  have hGdeg : G.natDegree = g.natDegree := hg.natDegree_map _
  have hGlc : G.leadingCoeff = 1 := (hg.map _).leadingCoeff
  have hM : G.mahlerMeasure ≤ R ^ g.natDegree := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hGlc, norm_one, one_mul]
    calc (G.roots.map fun a => max 1 ‖a‖).prod ≤ (G.roots.map fun _ => R).prod :=
          Multiset.prod_map_le_prod_map₀ _ _ (fun a _ => by positivity) fun a ha => max_le hR1 (hR a ha)
      _ = R ^ g.natDegree := by rw [Multiset.map_const', Multiset.prod_replicate, card_roots_complex hg]
  have hcoeff : ‖G.coeff k‖ = |(g.coeff k : ℝ)| := by
    rw [hG, coeff_map, eq_intCast, Complex.norm_intCast]
  rw [← hcoeff]
  have hch : ((G.natDegree.choose k : ℕ) : ℝ) ≤ 2 ^ g.natDegree := by
    rw [hGdeg]
    exact_mod_cast Nat.choose_le_two_pow _ _
  calc ‖G.coeff k‖ ≤ (G.natDegree.choose k) * G.mahlerMeasure := norm_coeff_le_choose_mul_mahlerMeasure k G
    _ ≤ 2 ^ g.natDegree * R ^ g.natDegree := mul_le_mul hch hM (mahlerMeasure_nonneg _) (by positivity)

noncomputable def monicBox (j B : ℕ) : Finset ℤ[X] :=
  (Fintype.piFinset fun _ : Fin j => Icc (-(B : ℤ)) B).image
    fun v => X ^ j + ∑ i : Fin j, C (v i) * X ^ (i : ℕ)

theorem card_monicBox_le (j B : ℕ) : (monicBox j B).card ≤ (2 * B + 1) ^ j := by
  unfold monicBox
  refine card_image_le.trans ?_
  rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, Int.card_Icc]
  have : ((B : ℤ) + 1 - -(B : ℤ)).toNat = 2 * B + 1 := by omega
  rw [this]

theorem mem_monicBox {g : ℤ[X]} (hg : g.Monic) {B : ℕ} (hB : ∀ k < g.natDegree, |g.coeff k| ≤ B) :
    g ∈ monicBox g.natDegree B := by
  unfold monicBox
  rw [mem_image]
  refine ⟨fun i => g.coeff i, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro i
    rw [mem_Icc]
    exact abs_le.1 (hB i i.2)
  · conv_rhs => rw [hg.as_sum]
    rw [Fin.sum_univ_eq_sum_range (fun i => C (g.coeff i) * X ^ i)]

theorem box_count_le {m j : ℕ} (hm : 6 ≤ m) (hj : 1 ≤ j) :
    (2 * (2 ^ j * m ^ j) + 1) ^ j ≤ m ^ (2 * j * j) := by
  have h1 : 1 ≤ 2 ^ j * m ^ j := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h2 : 3 ≤ 3 ^ j := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have h3 : 6 ^ j ≤ m ^ j := Nat.pow_le_pow_left hm j
  have h4 : 2 * (2 ^ j * m ^ j) + 1 ≤ m ^ (2 * j) := by
    calc 2 * (2 ^ j * m ^ j) + 1 ≤ 3 * (2 ^ j * m ^ j) := by omega
      _ ≤ 3 ^ j * (2 ^ j * m ^ j) := Nat.mul_le_mul_right _ h2
      _ = 6 ^ j * m ^ j := by rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_pow]; ring
      _ ≤ m ^ j * m ^ j := Nat.mul_le_mul_right _ h3
      _ = m ^ (2 * j) := by ring
  calc (2 * (2 ^ j * m ^ j) + 1) ^ j ≤ (m ^ (2 * j)) ^ j := Nat.pow_le_pow_left h4 j
    _ = m ^ (2 * j * j) := by rw [← pow_mul]

theorem mem_monicBox_of_roots {g : ℤ[X]} (hg : g.Monic) {m : ℕ} (hm : 1 ≤ m)
    (hR : ∀ α ∈ (g.map (Int.castRingHom ℂ)).roots, ‖α‖ ≤ (m : ℝ)) :
    g ∈ monicBox g.natDegree (2 ^ g.natDegree * m ^ g.natDegree) := by
  refine mem_monicBox hg fun k _ => ?_
  have h := abs_coeff_le hg (by exact_mod_cast hm) hR k
  have h' : ((|g.coeff k| : ℤ) : ℝ) ≤ (((2 ^ g.natDegree * m ^ g.natDegree : ℕ) : ℤ) : ℝ) := by
    push_cast
    exact h
  exact_mod_cast h'

theorem norm_root_charpoly_le {m : ℕ} {S : Matrix (Fin m) (Fin m) ℤ} (hS : IsSeidel S) {α : ℂ}
    (hα : (S.charpoly.map (Int.castRingHom ℂ)).eval α = 0) : ‖α‖ ≤ (m : ℝ) - 1 := by
  by_contra hlt
  push Not at hlt
  rw [← Matrix.charpoly_map, Matrix.eval_charpoly] at hα
  refine det_ne_zero_of_sum_row_lt_diag (A := Matrix.scalar (Fin m) α - S.map (Int.castRingHom ℂ))
    (fun k => ?_) hα
  have hm : 1 ≤ m := k.pos
  have hkk : (Matrix.scalar (Fin m) α - S.map (Int.castRingHom ℂ)) k k = α := by
    simp [hS.2.1 k]
  have hkj : ∀ j ∈ univ.erase k, ‖(Matrix.scalar (Fin m) α - S.map (Int.castRingHom ℂ)) k j‖ ≤ 1 := by
    intro j hj
    have hjk : j ≠ k := ne_of_mem_erase hj
    have hS' := hS.2.2 k j (Ne.symm hjk)
    have : (Matrix.scalar (Fin m) α - S.map (Int.castRingHom ℂ)) k j = -((S k j : ℤ) : ℂ) := by
      simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (Ne.symm hjk)]
    rw [this, norm_neg]
    rcases hS' with h | h <;> simp [h]
  rw [hkk]
  calc ∑ j ∈ univ.erase k, ‖(Matrix.scalar (Fin m) α - S.map (Int.castRingHom ℂ)) k j‖
      ≤ ∑ j ∈ univ.erase k, (1 : ℝ) := sum_le_sum hkj
    _ = (m : ℝ) - 1 := by
        rw [sum_const, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
          Nat.cast_sub hm, Nat.cast_one]
    _ < ‖α‖ := hlt

theorem norm_root_le_of_dvd {m : ℕ} {S : Matrix (Fin m) (Fin m) ℤ} (hS : IsSeidel S) {g : ℤ[X]}
    (hdvd : g ∣ S.charpoly) : ∀ α ∈ (g.map (Int.castRingHom ℂ)).roots, ‖α‖ ≤ (m : ℝ) := by
  intro α hα
  have hroot : (g.map (Int.castRingHom ℂ)).eval α = 0 := (mem_roots'.1 hα).2
  obtain ⟨q, hq⟩ := hdvd
  have h0 : (S.charpoly.map (Int.castRingHom ℂ)).eval α = 0 := by
    rw [hq, Polynomial.map_mul, eval_mul, hroot, zero_mul]
  have := norm_root_charpoly_le hS h0
  linarith

theorem exists_good_divisor {χ f : ℤ[X]} (hf : f.Monic) (hf1 : 1 ≤ f.natDegree) (hfχ : f ∣ χ) :
    ∃ g : ℤ[X], g.Monic ∧ 1 ≤ g.natDegree ∧ g.natDegree ≤ f.natDegree ∧ g ∣ χ ∧
      (g.natDegree = 1 ∨ ∀ a : ℤ, g.eval a ≠ 0) := by
  classical
  have hex : ∃ j, ∃ g : ℤ[X], g.Monic ∧ 1 ≤ g.natDegree ∧ g ∣ χ ∧ g.natDegree = j :=
    ⟨_, f, hf, hf1, hfχ, rfl⟩
  obtain ⟨g, hg, hg1, hgχ, hgj⟩ := Nat.find_spec hex
  refine ⟨g, hg, hg1, ?_, hgχ, ?_⟩
  · rw [hgj]
    exact Nat.find_min' hex ⟨f, hf, hf1, hfχ, rfl⟩
  · by_cases h1 : g.natDegree = 1
    · exact Or.inl h1
    · right
      intro a ha
      have hdvd : X - C a ∣ g := dvd_iff_isRoot.2 ha
      have hmin := Nat.find_min' hex ⟨X - C a, monic_X_sub_C a, by rw [natDegree_X_sub_C], hdvd.trans hgχ, rfl⟩
      rw [natDegree_X_sub_C] at hmin
      omega

end DGS
