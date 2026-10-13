module

public import DGS.S05_Local.Euler

@[expose] public section

open Matrix Polynomial Module

namespace DGS

variable {n : ℕ}

section Iota

variable {R : Type*} [CommRing R]

theorem aeval_mulVec_ones_of_natDegree_lt (A : Matrix (Fin n) (Fin n) R) {r : R[X]}
    (hr : r.natDegree < n) : aeval A r *ᵥ ones n R = walkMatrix A *ᵥ (fun j => r.coeff j) := by
  rw [aeval_eq_sum_range' hr, Matrix.sum_mulVec, ← Fin.sum_univ_eq_sum_range]
  funext i
  simp only [Finset.sum_apply, smul_mulVec, Pi.smul_apply, smul_eq_mul, walkMatrix, mulVec,
    dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

variable [Nontrivial R]

theorem natDegree_modByMonic_charpoly_lt (A : Matrix (Fin n) (Fin n) R) (hn : 1 ≤ n) (f : R[X]) :
    (f %ₘ A.charpoly).natDegree < n := by
  have h1 : A.charpoly ≠ 1 := fun h => by
    have := congrArg natDegree h
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin, natDegree_one] at this
    omega
  have := natDegree_modByMonic_lt f (charpoly_monic A) h1
  rwa [charpoly_natDegree_eq_dim, Fintype.card_fin] at this

theorem aeval_mulVec_ones_eq (A : Matrix (Fin n) (Fin n) R) (hn : 1 ≤ n) (f : R[X]) :
    aeval A f *ᵥ ones n R = walkMatrix A *ᵥ (fun j => (f %ₘ A.charpoly).coeff j) := by
  rw [← aeval_modByMonic_eq_self_of_root (aeval_self_charpoly A)]
  exact aeval_mulVec_ones_of_natDegree_lt A (natDegree_modByMonic_charpoly_lt A hn f)

omit [Nontrivial R] in
theorem psiPoly_map {S : Type*} [CommRing S] (A : Matrix (Fin n) (Fin n) R) (f : R →+* S) :
    psiPoly (A.map f) = (psiPoly A).map f := by
  have h := RingHom.map_adjugate (Polynomial.mapRingHom f) (charmatrix A)
  have h2 : ((charmatrix A).map (Polynomial.map f)).adjugate =
      ((charmatrix A).adjugate).map (Polynomial.map f) := h.symm
  rw [psiPoly, psiPoly, charmatrix_map, h2, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_sum]
  rfl

omit [Nontrivial R] in
theorem tauF_map {S : Type*} [CommRing S] [Nontrivial S] (A : Matrix (Fin n) (Fin n) R) (f : R →+* S)
    (g : R[X]) : tauF (A.map f) (g.map f) = f (tauF A g) := by
  rw [tauF, tauF, charpoly_map, ← map_modByMonic f (charpoly_monic A), coeff_map]

end Iota

section EulerUnimodular

variable {K : Type*} [Field K]

theorem tauF_X_pow_of_lt (A : Matrix (Fin n) (Fin n) K) {m : ℕ} (hm : m < n) :
    tauF A (X ^ m) = if m = n - 1 then 1 else 0 := by
  rw [tauF, (modByMonic_eq_self_iff (charpoly_monic A)).2, coeff_X_pow]
  · by_cases h : m = n - 1
    · simp [h]
    · simp [h, Ne.symm h]
  · rw [degree_X_pow, degree_eq_natDegree (charpoly_monic A).ne_zero, charpoly_natDegree_eq_dim,
      Fintype.card_fin]
    exact_mod_cast hm

theorem tauF_add (A : Matrix (Fin n) (Fin n) K) (f g : K[X]) :
    tauF A (f + g) = tauF A f + tauF A g := by
  have := (modByMonicHom A.charpoly).map_add f g
  simp only [modByMonicHom_apply] at this
  rw [tauF, tauF, tauF, this, coeff_add]

theorem tauF_smul (A : Matrix (Fin n) (Fin n) K) (c : K) (f : K[X]) :
    tauF A (c • f) = c * tauF A f := by
  rw [tauF, tauF, smul_modByMonic, coeff_smul, smul_eq_mul]

theorem tauF_sum (A : Matrix (Fin n) (Fin n) K) {ι : Type*} (s : Finset ι) (f : ι → K[X]) :
    tauF A (∑ i ∈ s, f i) = ∑ i ∈ s, tauF A (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tauF]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tauF_add, ih]

theorem tauF_X_pow_mul (A : Matrix (Fin n) (Fin n) K) {f : K[X]} (hf : f.natDegree < n) (j : ℕ) :
    tauF A (X ^ j * f) = ∑ i ∈ Finset.range n, f.coeff i * tauF A (X ^ (i + j)) := by
  conv_lhs => rw [as_sum_range' f n hf, Finset.mul_sum]
  rw [tauF_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, mul_comm (X ^ j), mul_assoc, ← pow_add, ← smul_eq_C_mul,
    tauF_smul, add_comm]

theorem coeff_int_of_tauF_int (A : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n) {f : ℚ[X]}
    (hf : f.natDegree < n)
    (h : ∀ j < n, ∃ k : ℤ, tauF (A.map (Int.castRingHom ℚ)) (X ^ j * f) = k) :
    ∀ i, ∃ k : ℤ, f.coeff i = k := by
  set Aq := A.map (Int.castRingHom ℚ) with hAq
  have hE : ∀ m, ∃ k : ℤ, tauF Aq (X ^ m) = k := by
    intro m
    refine ⟨tauF A (X ^ m), ?_⟩
    have := tauF_map A (Int.castRingHom ℚ) (X ^ m)
    rw [Polynomial.map_pow, Polynomial.map_X] at this
    rw [hAq, this]
    rfl
  have key : ∀ t, ∀ i, n - 1 - t ≤ i → i < n → ∃ k : ℤ, f.coeff i = k := by
    intro t
    induction t with
    | zero =>
      intro i hi hin
      have hi' : i = n - 1 := by omega
      subst hi'
      obtain ⟨k, hk⟩ := h 0 (by omega)
      refine ⟨k, ?_⟩
      rw [← hk, tauF_X_pow_mul Aq hf 0]
      rw [Finset.sum_eq_single (n - 1)]
      · rw [add_zero, tauF_X_pow_of_lt Aq (by omega), ite_eq_left rfl, mul_one]
      · intro b hb hbn
        rw [Finset.mem_range] at hb
        rw [add_zero, tauF_X_pow_of_lt Aq hb, ite_eq_right hbn, mul_zero]
      · intro h0; exact absurd (Finset.mem_range.2 (by omega)) h0
    | succ t ih =>
      intro i hi hin
      by_cases hit : n - 1 - t ≤ i
      · exact ih i hit hin
      · have hi' : i = n - 1 - (t + 1) := by omega
        have htn : t + 1 < n := by omega
        obtain ⟨k, hk⟩ := h (t + 1) htn
        have hsplit := tauF_X_pow_mul Aq hf (t + 1)
        rw [hk] at hsplit
        have hterm : ∀ i' ∈ Finset.range n, i' ≠ i →
            ∃ k' : ℤ, f.coeff i' * tauF Aq (X ^ (i' + (t + 1))) = k' := by
          intro i' hi' hne
          rw [Finset.mem_range] at hi'
          by_cases hlt : i' < i
          · refine ⟨0, ?_⟩
            rw [tauF_X_pow_of_lt Aq (by omega), ite_eq_right (by omega), mul_zero, Int.cast_zero]
          · obtain ⟨k1, hk1⟩ := ih i' (by omega) hi'
            obtain ⟨k2, hk2⟩ := hE (i' + (t + 1))
            exact ⟨k1 * k2, by rw [hk1, hk2]; push_cast; ring⟩
        have hii : f.coeff i * tauF Aq (X ^ (i + (t + 1))) = f.coeff i := by
          rw [tauF_X_pow_of_lt Aq (by omega), ite_eq_left (by omega), mul_one]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hin), hii] at hsplit
        choose g hg using hterm
        have hrest : ∑ x ∈ (Finset.range n).erase i, f.coeff x * tauF Aq (X ^ (x + (t + 1))) =
            ((∑ x ∈ ((Finset.range n).erase i).attach,
              g x.1 (Finset.mem_of_mem_erase x.2) (Finset.ne_of_mem_erase x.2) : ℤ) : ℚ) := by
          push_cast
          rw [← Finset.sum_attach]
          exact Finset.sum_congr rfl fun x _ => hg _ _ _
        rw [hrest] at hsplit
        exact ⟨k - ∑ x ∈ ((Finset.range n).erase i).attach,
          g x.1 (Finset.mem_of_mem_erase x.2) (Finset.ne_of_mem_erase x.2), by
            rw [Int.cast_sub]; linarith⟩
  intro i
  by_cases hin : i < n
  · exact key (n - 1) i (by omega) hin
  · exact ⟨0, by rw [coeff_eq_zero_of_natDegree_lt (by omega), Int.cast_zero]⟩

end EulerUnimodular

end DGS
