module

public import DGS.S03_Prelim.Mates

@[expose] public section

open Matrix

namespace DGS

variable {n : ℕ}

theorem exists_simpleInvariant_le {F : Type*} [Field F] {m : ℕ} (M : Matrix (Fin m) (Fin m) F)
    {U : Submodule F (Fin m → F)} (hU : IsInvariant M U) (hne : U ≠ ⊥) :
    ∃ W ≤ U, IsSimpleInvariant M W := by
  classical
  have hP : ∃ k, ∃ W : Submodule F (Fin m → F), W ≤ U ∧ IsInvariant M W ∧ W ≠ ⊥ ∧
      Module.finrank F W = k := ⟨_, U, le_rfl, hU, hne, rfl⟩
  obtain ⟨W, hWU, hWinv, hWne, hWk⟩ := Nat.find_spec hP
  refine ⟨W, hWU, hWinv, hWne, ?_⟩
  intro W' hW'inv hW'W
  by_cases h : W' = ⊥
  · exact Or.inl h
  · right
    apply Submodule.eq_of_le_of_finrank_le hW'W
    rw [hWk]
    exact Nat.find_min' hP ⟨W', hW'W.trans hWU, hW'inv, h, rfl⟩

noncomputable def levelMat (Q : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => ((level Q : ℚ) * Q i j).num

theorem levelMat_cast (Q : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    ((levelMat Q i j : ℤ) : ℚ) = (level Q : ℚ) * Q i j := by
  obtain ⟨z, hz⟩ := isIntegralMul_level Q i j
  simp only [levelMat, Matrix.of_apply, hz, Rat.num_intCast]

theorem toQ_levelMat (Q : Matrix (Fin n) (Fin n) ℚ) : toQ (levelMat Q) = (level Q : ℚ) • Q := by
  ext i j
  simp [toQ, levelMat_cast]

noncomputable def colSpaceModP (p : ℕ) (Q : Matrix (Fin n) (Fin n) ℚ) :
    Submodule (ZMod p) (Fin n → ZMod p) :=
  LinearMap.range (modP p (levelMat Q)).mulVecLin

theorem toQ_mul (M N : Matrix (Fin n) (Fin n) ℤ) : toQ (M * N) = toQ M * toQ N := by
  unfold toQ
  exact Matrix.map_mul

theorem modP_mul (p : ℕ) (M N : Matrix (Fin n) (Fin n) ℤ) : modP p (M * N) = modP p M * modP p N := by
  unfold modP
  exact Matrix.map_mul

theorem modP_transpose (p : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) : modP p Mᵀ = (modP p M)ᵀ := by
  unfold modP
  exact transpose_map

theorem toQ_transpose (M : Matrix (Fin n) (Fin n) ℤ) : toQ Mᵀ = (toQ M)ᵀ := by
  unfold toQ
  exact transpose_map

theorem lem_matesfail_colSpace {G : SimpleGraph (Fin n)} {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : Q ∈ QG G)
    {p : ℕ} [Fact p.Prime] (_hp2 : p ≠ 2) (hdvd : p ∣ level Q) :
    colSpaceModP p Q ≠ ⊥ ∧ IsInvariant (modP p (adj G)) (colSpaceModP p Q) ∧
      IsTotallyIsotropic (colSpaceModP p Q) ∧ ∀ u ∈ colSpaceModP p Q, ones n (ZMod p) ⬝ᵥ u = 0 := by
  obtain ⟨hQQ', he, H, hH⟩ := hQ
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQQ'
  have hinj : Function.Injective (fun M : Matrix (Fin n) (Fin n) ℤ => toQ M) :=
    Matrix.map_injective Int.cast_injective
  have hT : toQ (levelMat Q)ᵀ = (level Q : ℚ) • Qᵀ := by
    rw [toQ_transpose, toQ_levelMat, transpose_smul]
  have hAQ : toQ (adj G) * Q = Q * toQ (adj H) := by
    rw [← hH, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hAN : adj G * levelMat Q = levelMat Q * adj H := by
    apply hinj
    simp only [toQ_mul, toQ_levelMat, Matrix.mul_smul, Matrix.smul_mul, hAQ]
  have hNN : (levelMat Q)ᵀ * levelMat Q = Matrix.diagonal (fun _ => ((level Q : ℤ) ^ 2)) := by
    apply hinj
    show toQ ((levelMat Q)ᵀ * levelMat Q) = toQ (Matrix.diagonal (fun _ => ((level Q : ℤ) ^ 2)))
    rw [toQ_mul, hT, toQ_levelMat, Matrix.smul_mul, Matrix.mul_smul, hQQ', smul_smul]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [toQ, sq]
    · simp [toQ, hij]
  have hNe : (levelMat Q)ᵀ *ᵥ ones n ℤ = (level Q : ℤ) • ones n ℤ := by
    funext i
    apply Int.cast_injective (α := ℚ)
    have h1 := RingHom.map_mulVec (Int.castRingHom ℚ) (levelMat Q)ᵀ (ones n ℤ) i
    simp only [eq_intCast] at h1
    rw [h1]
    have e2 : (Int.castRingHom ℚ) ∘ ones n ℤ = ones n ℚ := by
      funext k
      simp [ones]
    rw [e2]
    change (toQ (levelMat Q)ᵀ *ᵥ ones n ℚ) i = _
    rw [hT, smul_mulVec, transpose_mulVec_ones hQQ' he]
    simp [ones]
  have hℓp : (level Q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
  have hAb : modP p (adj G) * modP p (levelMat Q) = modP p (levelMat Q) * modP p (adj H) := by
    rw [← modP_mul, ← modP_mul, hAN]
  have hNNb : (modP p (levelMat Q))ᵀ * modP p (levelMat Q) = 0 := by
    rw [← modP_transpose, ← modP_mul, hNN]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [modP, hℓp]
    · simp [modP, hij]
  have hNeb : (modP p (levelMat Q))ᵀ *ᵥ ones n (ZMod p) = 0 := by
    funext i
    have h1 := RingHom.map_mulVec (Int.castRingHom (ZMod p)) (levelMat Q)ᵀ (ones n ℤ) i
    have e2 : (Int.castRingHom (ZMod p)) ∘ ones n ℤ = ones n (ZMod p) := by
      funext k
      simp [ones]
    rw [e2, hNe] at h1
    rw [← modP_transpose]
    change ((levelMat Q)ᵀ.map (Int.castRingHom (ZMod p)) *ᵥ ones n (ZMod p)) i = 0
    rw [← h1]
    simp [ones, hℓp]
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro hbot
    have hcol : ∀ i j, modP p (levelMat Q) i j = 0 := by
      intro i j
      classical
      have hmem : (modP p (levelMat Q)).mulVecLin (Pi.single j 1) ∈ colSpaceModP p Q :=
        LinearMap.mem_range_self _ _
      rw [hbot, Submodule.mem_bot, mulVecLin_apply, mulVec_single_one] at hmem
      exact congrFun hmem i
    obtain ⟨k, hk⟩ := hdvd
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hℓpos : 0 < level Q := level_pos Q
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk
        omega
      · exact h
    have hint : IsIntegralMul k Q := by
      intro i j
      have hz : (p : ℤ) ∣ levelMat Q i j := by
        have := hcol i j
        simp only [modP, Matrix.map_apply, eq_intCast] at this
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
      obtain ⟨m, hm⟩ := hz
      refine ⟨m, ?_⟩
      have h1 := levelMat_cast Q i j
      rw [hm, hk] at h1
      push_cast at h1
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      have h2 : (p : ℚ) * ((k : ℚ) * Q i j - m) = 0 := by linear_combination -h1
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h hp0
      · linarith
    have hle := level_le hkpos hint
    rw [hk] at hle
    nlinarith
  ·
    intro u hu
    obtain ⟨x, rfl⟩ := hu
    refine ⟨modP p (adj H) *ᵥ x, ?_⟩
    simp only [mulVecLin_apply]
    rw [mulVec_mulVec, mulVec_mulVec, hAb]
  ·
    intro u hu v hv
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨y, rfl⟩ := hv
    simp only [mulVecLin_apply]
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hNNb, zero_mulVec, zero_dotProduct]
  ·
    intro u hu
    obtain ⟨x, rfl⟩ := hu
    simp only [mulVecLin_apply]
    rw [dotProduct_mulVec, ← mulVec_transpose, hNeb, zero_dotProduct]

theorem lem_matesfail {G : SimpleGraph (Fin n)} {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : Q ∈ QG G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ level Q) : ∃ d, 1 ≤ d ∧ E p d G := by
  have := Fact.mk hp
  obtain ⟨hne, hinv, hiso, horth⟩ := lem_matesfail_colSpace hQ hp2 hdvd
  obtain ⟨W, hWU, hW⟩ := exists_simpleInvariant_le (modP p (adj G)) hinv hne
  refine ⟨Module.finrank (ZMod p) W, Submodule.one_le_finrank_iff.2 hW.2.1, W, hW, rfl, ?_, ?_⟩
  · intro u hu v hv
    exact hiso u (hWU hu) v (hWU hv)
  · intro u hu
    exact horth u (hWU hu)

end DGS
