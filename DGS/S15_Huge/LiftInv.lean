module

public import DGS.S15_Huge.LinAlg

@[expose] public section

open Matrix Finset Polynomial

namespace DGS

section Lift

variable {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def piMat (M : Matrix (Fin m) ι ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  (Mᵀ * M).det • (1 : Matrix (Fin m) (Fin m) ℤ) - M * (Mᵀ * M).adjugate * Mᵀ

theorem piMat_mul (M : Matrix (Fin m) ι ℤ) : piMat M * M = 0 := by
  unfold piMat
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc (M * _) Mᵀ M,
    Matrix.mul_assoc M, Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]

theorem piMat_map (M : Matrix (Fin m) ι ℤ) {F : Type*} [Field F] (φ : ℤ →+* F) :
    (piMat M).map φ = φ (Mᵀ * M).det • (1 : Matrix (Fin m) (Fin m) F) -
      M.map φ * (Mᵀ * M).adjugate.map φ * (M.map φ)ᵀ := by
  have h1 : (M * (Mᵀ * M).adjugate * Mᵀ).map φ = M.map φ * (Mᵀ * M).adjugate.map φ * (M.map φ)ᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [← h1]
  ext i j
  simp only [piMat, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul]
  congr 1
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

theorem eq_mulVec_of_piMat {F : Type*} [Field F] (M : Matrix (Fin m) ι ℤ) (φ : ℤ →+* F)
    (hdet : φ (Mᵀ * M).det ≠ 0) {z : Fin m → F} (hz : (piMat M).map φ *ᵥ z = 0) :
    z = M.map φ *ᵥ ((φ (Mᵀ * M).det)⁻¹ • ((Mᵀ * M).adjugate.map φ *ᵥ ((M.map φ)ᵀ *ᵥ z))) := by
  rw [piMat_map, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hz, smul_smul, inv_mul_cancel₀ hdet,
    one_smul]

def blockKrylovMat (T : Matrix (Fin m) (Fin m) ℤ) (M : Matrix (Fin m) ι ℤ) :
    Matrix (Fin (Fintype.card ι) × Fin m) ι ℤ :=
  Matrix.of fun x k => (piMat M * T ^ (x.1.val + 1) * M) x.2 k

theorem blockKrylovMat_mulVec {F : Type*} [Field F] (T : Matrix (Fin m) (Fin m) ℤ) (M : Matrix (Fin m) ι ℤ)
    (φ : ℤ →+* F) (a : ι → F) (x : Fin (Fintype.card ι) × Fin m) :
    ((blockKrylovMat T M).map φ *ᵥ a) x =
      ((piMat M).map φ *ᵥ ((T.map φ) ^ (x.1.val + 1) *ᵥ (M.map φ *ᵥ a))) x.2 := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_pow, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

theorem liftinv_core (hm : 2 ≤ m) (hιm : Fintype.card ι < m)
    (T : Matrix (Fin m) (Fin m) ℤ) (hT : ∀ i j, |T i j| ≤ 1)
    (M : Matrix (Fin m) ι ℤ) (hM : ∀ i k, |M i k| ≤ 1)
    (hMinj : ∀ a : ι → ℚ, M.map (Int.castRingHom ℚ) *ᵥ a = 0 → a = 0)
    (hU : ∀ W : Submodule ℚ (Fin m → ℚ), IsInvariant (T.map (Int.castRingHom ℚ)) W →
      W ≤ LinearMap.range (M.map (Int.castRingHom ℚ)).mulVecLin → W = ⊥)
    {p : ℕ} [Fact p.Prime] (hp : m ^ (Fintype.card ι * (6 * Fintype.card ι + 13)) < p)
    (V : Submodule (ZMod p) (Fin m → ZMod p)) (hV : IsInvariant (modP p T) V)
    (hVπ : ∀ w ∈ V, (piMat M).map (Int.castRingHom (ZMod p)) *ᵥ w = 0) : V = ⊥ := by
  classical
  set d := Fintype.card ι with hd
  set G := Mᵀ * M with hG
  set Λ := blockKrylovMat T M with hΛ
  have hm1 : 1 ≤ m := by omega
  have hdm : d ≤ m := hιm.le
  have hdm' : d ≤ m ^ 1 := by simpa using hdm
  have hGdet : G.det ≠ 0 := det_gram_ne_zero M hMinj
  have hMb : ∀ i k, |M i k| ≤ (m : ℤ) ^ 0 := by simpa using hM
  have hMtb : ∀ k i, |Mᵀ k i| ≤ (m : ℤ) ^ 0 := fun k i => hMb i k
  have hGb : ∀ k l, |G k l| ≤ (m : ℤ) ^ 1 :=
    abs_mul_apply_le_pow (e₁ := 0) (e₂ := 0) (e₃ := 1) hm1 (by simp) hMtb hMb (by omega)
  have hGdetb : |G.det| ≤ (m : ℤ) ^ (d * (1 + 1)) := abs_det_le_pow hdm hGb
  have hadjb : ∀ k l, |G.adjugate k l| ≤ (m : ℤ) ^ (d * (1 + 1)) :=
    abs_adjugate_apply_le_pow hm1 hdm hGb
  have hN1 : ∀ i l, |(M * G.adjugate) i l| ≤ (m : ℤ) ^ (2 * d + 1) :=
    abs_mul_apply_le_pow (e₁ := 0) (e₂ := d * (1 + 1)) (e₃ := 1) hm1 hdm' hMb hadjb (by ring_nf; omega)
  have hN2 : ∀ i j, |(M * G.adjugate * Mᵀ) i j| ≤ (m : ℤ) ^ (2 * d + 2) :=
    abs_mul_apply_le_pow (e₁ := 2 * d + 1) (e₂ := 0) (e₃ := 1) hm1 hdm' hN1 hMtb (by omega)
  have hπb : ∀ i j, |piMat M i j| ≤ (m : ℤ) ^ (2 * d + 3) := by
    intro i j
    have hm2 : (2 : ℤ) ≤ m := by exact_mod_cast hm
    have hX : (0 : ℤ) ≤ (m : ℤ) ^ (2 * d + 2) := by positivity
    have h3 : (m : ℤ) ^ (d * (1 + 1)) ≤ (m : ℤ) ^ (2 * d + 2) :=
      pow_le_pow_right₀ (by omega) (by ring_nf; omega)
    have h1 : |G.det * (1 : Matrix (Fin m) (Fin m) ℤ) i j| ≤ (m : ℤ) ^ (d * (1 + 1)) := by
      rw [Matrix.one_apply]
      split_ifs
      · simpa using hGdetb
      · simp only [mul_zero, abs_zero]
        positivity
    have h4 : (m : ℤ) ^ (2 * d + 3) = (m : ℤ) ^ (2 * d + 2) * m := by ring
    unfold piMat
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    calc |G.det * (1 : Matrix (Fin m) (Fin m) ℤ) i j - (M * G.adjugate * Mᵀ) i j|
        ≤ |G.det * (1 : Matrix (Fin m) (Fin m) ℤ) i j| + |(M * G.adjugate * Mᵀ) i j| := abs_sub _ _
      _ ≤ (m : ℤ) ^ (2 * d + 2) + (m : ℤ) ^ (2 * d + 2) := add_le_add (h1.trans h3) (hN2 i j)
      _ ≤ (m : ℤ) ^ (2 * d + 3) := by rw [h4]; nlinarith
  have hΛb : ∀ x k, |Λ x k| ≤ (m : ℤ) ^ (3 * d + 5) := by
    intro x k
    have hTj : ∀ i l, |(T ^ (x.1.val + 1)) i l| ≤ (m : ℤ) ^ d := fun i l =>
      (abs_pow_apply_le hm1 hT _ i l).trans (pow_le_pow_right₀ (by exact_mod_cast hm1) (by omega))
    have h1 : ∀ i l, |(piMat M * T ^ (x.1.val + 1)) i l| ≤ (m : ℤ) ^ (3 * d + 4) :=
      abs_mul_apply_le_pow (e₁ := 2 * d + 3) (e₂ := d) (e₃ := 1) hm1 (by simp) hπb hTj (by omega)
    exact abs_mul_apply_le_pow (e₁ := 3 * d + 4) (e₂ := 0) (e₃ := 1) hm1 (by simp) h1 hMb (by omega) x.2 k
  have hHb : ∀ k l, |(Λᵀ * Λ) k l| ≤ (m : ℤ) ^ (6 * d + 12) := by
    have hcard : Fintype.card (Fin d × Fin m) ≤ m ^ 2 := by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, sq]
      exact Nat.mul_le_mul_right m hdm
    exact abs_mul_apply_le_pow (e₁ := 3 * d + 5) (e₂ := 3 * d + 5) (e₃ := 2) hm1 hcard
      (fun k x => hΛb x k) hΛb (by omega)
  have hHdetb : |(Λᵀ * Λ).det| ≤ (m : ℤ) ^ (d * (6 * d + 12 + 1)) := abs_det_le_pow hdm hHb
  have hΛinj : ∀ a : ι → ℚ, Λ.map (Int.castRingHom ℚ) *ᵥ a = 0 → a = 0 := by
    intro a ha
    set y := M.map (Int.castRingHom ℚ) *ᵥ a with hy
    have hdetq : (Int.castRingHom ℚ) G.det ≠ 0 := by
      rw [eq_intCast]
      exact_mod_cast hGdet
    have hyU : ∀ j ≤ d, ((T.map (Int.castRingHom ℚ)) ^ j) *ᵥ y ∈
        LinearMap.range (M.map (Int.castRingHom ℚ)).mulVecLin := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [pow_zero, Matrix.one_mulVec]
        exact ⟨a, rfl⟩
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hπ : (piMat M).map (Int.castRingHom ℚ) *ᵥ ((T.map (Int.castRingHom ℚ)) ^ (j' + 1) *ᵥ y) = 0 := by
          funext i
          have h1 := congrFun ha (⟨j', by omega⟩, i)
          rw [blockKrylovMat_mulVec] at h1
          exact h1
        exact ⟨_, (eq_mulVec_of_piMat M (Int.castRingHom ℚ) hdetq hπ).symm⟩
    by_contra hne
    have hy0 : y ≠ 0 := fun h0 => hne (hMinj a h0)
    have hJ : Module.finrank ℚ (LinearMap.range (M.map (Int.castRingHom ℚ)).mulVecLin) ≤ d := by
      refine (LinearMap.finrank_range_le _).trans ?_
      simp [hd]
    obtain ⟨W, hW0, hWU, hWinv⟩ := exists_invariant_of_krylov (T.map (Int.castRingHom ℚ)) _ hJ hy0 hyU
    exact hW0 (hU W hWinv hWU)
  have hHdet : (Λᵀ * Λ).det ≠ 0 := det_gram_ne_zero Λ hΛinj
  have hpm : (m : ℤ) ^ (d * (6 * d + 13)) < p := by exact_mod_cast hp
  have hpG : (Int.castRingHom (ZMod p)) G.det ≠ 0 := by
    rw [eq_intCast]
    refine intCast_zmod_ne_zero hGdet (hGdetb.trans_lt (lt_of_le_of_lt ?_ hpm))
    exact pow_le_pow_right₀ (by exact_mod_cast hm1) (by nlinarith)
  have hpH : (Int.castRingHom (ZMod p)) (Λᵀ * Λ).det ≠ 0 := by
    rw [eq_intCast]
    refine intCast_zmod_ne_zero hHdet (hHdetb.trans_lt (lt_of_le_of_lt ?_ hpm))
    exact pow_le_pow_right₀ (by exact_mod_cast hm1) (by nlinarith)
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  have hwa := eq_mulVec_of_piMat M (Int.castRingHom (ZMod p)) hpG (hVπ w hw)
  set a := ((Int.castRingHom (ZMod p)) G.det)⁻¹ •
    (G.adjugate.map (Int.castRingHom (ZMod p)) *ᵥ ((M.map (Int.castRingHom (ZMod p)))ᵀ *ᵥ w)) with ha
  have hpow : ∀ j, (modP p T) ^ j *ᵥ w ∈ V := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, Matrix.one_mulVec]
      exact hw
    | succ j ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact hV _ ih
  have hΛa : Λ.map (Int.castRingHom (ZMod p)) *ᵥ a = 0 := by
    funext x
    rw [blockKrylovMat_mulVec, ← hwa]
    exact congrFun (hVπ _ (hpow _)) x.2
  have ha0 : a = 0 := eq_zero_of_gram_det Λ (Int.castRingHom (ZMod p)) hpH hΛa
  rw [hwa, ha0, Matrix.mulVec_zero]

end Lift

theorem lem_liftinv {m : ℕ} (hm : 2 ≤ m) {κ : Type*} [Fintype κ] (hκm : Fintype.card κ < m)
    (T : Matrix (Fin m) (Fin m) ℤ) (hT : ∀ i j, |T i j| ≤ 1) (u : κ → Fin m → ℤ) (hu : ∀ k i, |u k i| ≤ 1)
    (hU : ∀ W : Submodule ℚ (Fin m → ℚ), IsInvariant (T.map (Int.castRingHom ℚ)) W →
      W ≤ Submodule.span ℚ (Set.range fun k i => (u k i : ℚ)) → W = ⊥)
    {p : ℕ} [Fact p.Prime] (hp : m ^ (20 * Fintype.card κ ^ 2) < p)
    (V : Submodule (ZMod p) (Fin m → ZMod p)) (hV : IsInvariant (modP p T) V)
    (hVu : V ≤ Submodule.span (ZMod p) (Set.range fun k i => (u k i : ZMod p))) : V = ⊥ := by
  classical
  set uq : κ → Fin m → ℚ := fun k i => (u k i : ℚ) with huq
  obtain ⟨b, -, -, hbspan, hbli⟩ := exists_linearIndepOn_extension (K := ℚ) (v := uq)
    (linearIndepOn_empty ℚ uq) (Set.empty_subset Set.univ)
  set M : Matrix (Fin m) b ℤ := Matrix.of fun i k => u k i with hMdef
  have hMq : ∀ k : b, (M.map (Int.castRingHom ℚ))ᵀ k = uq k := fun k => by
    funext i
    simp [hMdef, huq]
  have hcardb : Fintype.card b ≤ Fintype.card κ := Fintype.card_subtype_le _
  have hMinj : ∀ a : b → ℚ, M.map (Int.castRingHom ℚ) *ᵥ a = 0 → a = 0 := by
    intro a ha
    have hsum : ∑ k : b, a k • uq k = 0 := by
      rw [← ha]
      funext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, hMdef, huq, mul_comm]
    funext k
    exact Fintype.linearIndependent_iff.1 hbli a hsum k
  have hrange : LinearMap.range (M.map (Int.castRingHom ℚ)).mulVecLin =
      Submodule.span ℚ (uq '' b) := by
    rw [Matrix.range_mulVecLin, Set.image_eq_range]
    congr 1
  have hU' : ∀ W : Submodule ℚ (Fin m → ℚ), IsInvariant (T.map (Int.castRingHom ℚ)) W →
      W ≤ LinearMap.range (M.map (Int.castRingHom ℚ)).mulVecLin → W = ⊥ := by
    intro W hW hWU
    refine hU W hW (hWU.trans ?_)
    rw [hrange]
    exact Submodule.span_mono (by rintro _ ⟨k, -, rfl⟩; exact ⟨k, rfl⟩)
  have hπu : ∀ k, piMat M *ᵥ u k = 0 := by
    intro k
    have hk : uq k ∈ LinearMap.range (M.map (Int.castRingHom ℚ)).mulVecLin := by
      rw [hrange]
      exact hbspan ⟨k, Set.mem_univ _, rfl⟩
    obtain ⟨c, hc⟩ := hk
    have hq : (piMat M).map (Int.castRingHom ℚ) *ᵥ uq k = 0 := by
      rw [← hc, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, piMat_mul, Matrix.map_zero,
        Matrix.zero_mulVec]
      · exact map_zero _
    funext i
    have h1 := congrFun hq i
    have h2 : (Int.castRingHom ℚ) ((piMat M *ᵥ u k) i) = 0 := by
      rw [RingHom.map_mulVec]
      exact h1
    simpa using h2
  have hVπ : ∀ w ∈ V, (piMat M).map (Int.castRingHom (ZMod p)) *ᵥ w = 0 := by
    have hker : Submodule.span (ZMod p) (Set.range fun k i => (u k i : ZMod p)) ≤
        LinearMap.ker ((piMat M).map (Int.castRingHom (ZMod p))).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
      funext i
      have h1 := congrArg (Int.castRingHom (ZMod p)) (congrFun (hπu k) i)
      rw [RingHom.map_mulVec, Pi.zero_apply, map_zero] at h1
      exact h1
    intro w hw
    have := hker (hVu hw)
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
  have hp' : m ^ (Fintype.card b * (6 * Fintype.card b + 13)) < p := by
    refine lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) ?_) hp
    have h1 : Fintype.card b * (6 * Fintype.card b + 13) ≤ Fintype.card κ * (6 * Fintype.card κ + 13) :=
      Nat.mul_le_mul hcardb (by omega)
    refine h1.trans ?_
    rcases Nat.eq_zero_or_pos (Fintype.card κ) with h0 | h0
    · simp [h0]
    · nlinarith
  exact liftinv_core hm (lt_of_le_of_lt hcardb hκm) T hT M (fun i k => hu k i) hMinj hU' hp' V hV hVπ

end DGS
