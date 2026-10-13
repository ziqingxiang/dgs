module

public import DGS.Core.Seidel
public import DGS.External

@[expose] public section

open Matrix Filter Topology

namespace DGS

variable {n : ℕ}

theorem level_mem (Q : Matrix (Fin n) (Fin n) ℚ) :
    level Q ∈ {ℓ : ℕ | 0 < ℓ ∧ IsIntegralMul ℓ Q} := by
  apply Nat.sInf_mem
  refine ⟨∏ i, ∏ j, (Q i j).den, ?_, ?_⟩
  · exact Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => Rat.den_pos _
  · intro i j
    obtain ⟨k, hk⟩ : (Q i j).den ∣ ∏ i, ∏ j, (Q i j).den :=
      (Finset.dvd_prod_of_mem (fun j => (Q i j).den) (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j, (Q i j).den) (Finset.mem_univ i))
    refine ⟨(k : ℤ) * (Q i j).num, ?_⟩
    rw [hk]
    push_cast
    rw [← Rat.mul_den_eq_num (Q i j)]
    ring

theorem level_pos (Q : Matrix (Fin n) (Fin n) ℚ) : 0 < level Q := (level_mem Q).1

theorem isIntegralMul_level (Q : Matrix (Fin n) (Fin n) ℚ) : IsIntegralMul (level Q) Q :=
  (level_mem Q).2

theorem level_le {Q : Matrix (Fin n) (Fin n) ℚ} {ℓ : ℕ} (hℓ : 0 < ℓ) (h : IsIntegralMul ℓ Q) :
    level Q ≤ ℓ :=
  Nat.sInf_le ⟨hℓ, h⟩

section Walk

variable {R : Type*} [CommRing R]

theorem transpose_mulVec_ones {Q : Matrix (Fin n) (Fin n) R} (hQ : Qᵀ * Q = 1)
    (he : Q *ᵥ ones n R = ones n R) : Qᵀ *ᵥ ones n R = ones n R := by
  calc Qᵀ *ᵥ ones n R = Qᵀ *ᵥ (Q *ᵥ ones n R) := by rw [he]
    _ = ones n R := by rw [mulVec_mulVec, hQ, one_mulVec]

theorem transpose_mul_walkMatrix {A B Q : Matrix (Fin n) (Fin n) R}
    (hQ : Qᵀ * Q = 1) (he : Q *ᵥ ones n R = ones n R) (hAB : Qᵀ * A * Q = B) :
    Qᵀ * walkMatrix A = walkMatrix B := by
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have heT := transpose_mulVec_ones hQ he
  have hcomm : Qᵀ * A = B * Qᵀ := by
    rw [← hAB, Matrix.mul_assoc (Qᵀ * A), hQQ, Matrix.mul_one]
  have hpow : ∀ k : ℕ, Qᵀ * A ^ k = B ^ k * Qᵀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hcomm, Matrix.mul_assoc]
  ext i j
  have key : Qᵀ *ᵥ (A ^ (j : ℕ) *ᵥ ones n R) = B ^ (j : ℕ) *ᵥ ones n R := by
    rw [mulVec_mulVec, hpow, ← mulVec_mulVec, heT]
  rw [Matrix.mul_apply]
  simp only [walkMatrix, Matrix.of_apply]
  rw [← key]
  rfl

end Walk

theorem det_walkMatrix_map_ne_zero {G : SimpleGraph (Fin n)} (hG : Controllable G) (K : Type*) [Field K]
    [CharZero K] : ((walkMatrix (adj G)).map (Int.castRingHom K)).det ≠ 0 := by
  have h := RingHom.map_det (Int.castRingHom K) (walkMatrix (adj G))
  rw [RingHom.mapMatrix_apply] at h
  rw [← h, eq_intCast]
  exact_mod_cast hG

theorem thm_wangxu_unique {G H : SimpleGraph (Fin n)}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1) (he : Q *ᵥ ones n ℝ = ones n ℝ)
    (hA : Qᵀ * (adj G).map (Int.castRingHom ℝ) * Q = (adj H).map (Int.castRingHom ℝ)) :
    Qᵀ * (walkMatrix (adj G)).map (Int.castRingHom ℝ) = (walkMatrix (adj H)).map (Int.castRingHom ℝ) := by
  rw [walkMatrix_map, walkMatrix_map]
  exact transpose_mul_walkMatrix hQ he hA

theorem thm_wangxu_exists {G H : SimpleGraph (Fin n)} (hG : Controllable G) (h : SameGenSpectrum G H) :
    ∃ Q ∈ QG G, Qᵀ * toQ (adj G) * Q = toQ (adj H) ∧
      Qᵀ = toQ (walkMatrix (adj H)) * (toQ (walkMatrix (adj G)))⁻¹ := by
  obtain ⟨Q₀, h1, h2, h3⟩ := ext_johnson_newman G H h
  set WG := toQ (walkMatrix (adj G)) with hWGdef
  set WH := toQ (walkMatrix (adj H)) with hWHdef
  set Q : Matrix (Fin n) (Fin n) ℚ := (WH * WG⁻¹)ᵀ with hQdef
  have hWG : IsUnit WG.det := isUnit_iff_ne_zero.2 (det_walkMatrix_map_ne_zero hG ℚ)
  have hQW : Qᵀ * WG = WH := by
    rw [hQdef, transpose_transpose, Matrix.mul_assoc, nonsing_inv_mul _ hWG, Matrix.mul_one]
  let φ : ℚ →+* ℝ := Rat.castHom ℝ
  have hφ : Function.Injective φ := Rat.cast_injective
  have hcast : ∀ M : Matrix (Fin n) (Fin n) ℤ, (toQ M).map φ = M.map (Int.castRingHom ℝ) := by
    intro M
    ext i j
    simp [toQ, φ]
  have hWGR : IsUnit (WG.map φ).det := by
    rw [hWGdef, hcast]
    exact isUnit_iff_ne_zero.2 (det_walkMatrix_map_ne_zero hG ℝ)
  have hQ0 : Q.map φ = Q₀ := by
    have e1 : (Q.map φ)ᵀ * WG.map φ = WH.map φ := by
      rw [← transpose_map, ← Matrix.map_mul, hQW]
    have e2 : Q₀ᵀ * WG.map φ = WH.map φ := by
      rw [hWGdef, hWHdef, hcast, hcast]
      exact thm_wangxu_unique Q₀ h1 h2 h3
    have e3 : (Q.map φ)ᵀ = Q₀ᵀ := by
      have := congrArg (· * (WG.map φ)⁻¹) (e1.trans e2.symm)
      simpa only [Matrix.mul_assoc, mul_nonsing_inv _ hWGR, Matrix.mul_one] using this
    exact transpose_injective e3
  have hconj : Qᵀ * toQ (adj G) * Q = toQ (adj H) := by
    apply Matrix.map_injective hφ
    simp only [Matrix.map_mul, transpose_map]
    rw [hQ0, hcast, hcast]
    exact h3
  refine ⟨Q, ⟨?_, ?_, H, hconj⟩, hconj, ?_⟩
  · apply Matrix.map_injective hφ
    show (Qᵀ * Q).map φ = (1 : Matrix (Fin n) (Fin n) ℚ).map φ
    rw [Matrix.map_mul, transpose_map, hQ0, h1, Matrix.map_one _ (map_zero φ) (map_one φ)]
  · funext i
    apply hφ
    have e : φ ∘ ones n ℚ = ones n ℝ := by
      funext k
      simp [ones]
    rw [RingHom.map_mulVec, e, hQ0, h2]
    simp [ones]
  · rw [hQdef, transpose_transpose]

theorem permMatrix_apply' (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    σ.permMatrix ℚ i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem permMatrix_conj (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) ℚ) :
    (σ.permMatrix ℚ)ᵀ * M * σ.permMatrix ℚ = M.submatrix σ.symm σ.symm := by
  rw [transpose_permMatrix, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem permMatrix_transpose_mul (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix ℚ)ᵀ * σ.permMatrix ℚ = 1 := by
  rw [← Matrix.mul_one ((σ.permMatrix ℚ)ᵀ), permMatrix_conj]
  ext i j
  simp [Matrix.one_apply]

theorem permMatrix_mulVec_ones (σ : Equiv.Perm (Fin n)) : σ.permMatrix ℚ *ᵥ ones n ℚ = ones n ℚ := by
  rw [permMatrix_mulVec]
  rfl

theorem level_permMatrix (σ : Equiv.Perm (Fin n)) : level (σ.permMatrix ℚ) = 1 := by
  apply le_antisymm
  · apply level_le one_pos
    intro i j
    refine ⟨if σ i = j then 1 else 0, ?_⟩
    rw [permMatrix_apply']
    split_ifs <;> simp
  · exact level_pos _

theorem isPermMatrix_of_integral {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : Qᵀ * Q = 1)
    (he : Q *ᵥ ones n ℚ = ones n ℚ) (hint : IsIntegralMul 1 Q) : IsPermMatrix Q := by
  choose Z hZ using hint
  have hZ' : ∀ i j, Q i j = Z i j := fun i j => by simpa using hZ i j
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have hrow2 : ∀ i, ∑ j, Z i j * Z i j = 1 := by
    intro i
    have := congrFun (congrFun hQQ i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, hZ'] at this
    exact_mod_cast this
  have hrow1 : ∀ i, ∑ j, Z i j = 1 := by
    intro i
    have := congrFun he i
    simp only [mulVec, dotProduct, ones, mul_one, hZ'] at this
    exact_mod_cast this
  have hcol2 : ∀ j, ∑ i, Z i j * Z i j = 1 := by
    intro j
    have := congrFun (congrFun hQ j) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, hZ'] at this
    exact_mod_cast this
  have h01 : ∀ i j, Z i j = 0 ∨ Z i j = 1 := by
    intro i
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ Z i j * Z i j - Z i j := by
      intro j _
      rcases le_or_gt (Z i j) 0 with h | h
      · nlinarith
      · nlinarith
    have hsum : ∑ j, (Z i j * Z i j - Z i j) = 0 := by
      rw [Finset.sum_sub_distrib, hrow2, hrow1, sub_self]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum
    intro j
    have hj := hz j (Finset.mem_univ j)
    have : Z i j * (Z i j - 1) = 0 := by linarith [hj]
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hsq : ∀ i j, Z i j * Z i j = Z i j := fun i j => by
    rcases h01 i j with h | h <;> simp [h]
  have hunique : ∀ (s : Fin n → ℤ), (∀ k, s k = 0 ∨ s k = 1) → ∑ k, s k = 1 → ∃! k, s k = 1 := by
    intro s hs hsum
    classical
    have hsk : ∀ k, s k = if s k = 1 then 1 else 0 := fun k => by
      rcases hs k with h | h <;> simp [h]
    have hcard : ((Finset.univ.filter fun k => s k = 1).card : ℤ) = 1 :=
      calc ((Finset.univ.filter fun k => s k = 1).card : ℤ)
          = ∑ k, (if s k = 1 then (1 : ℤ) else 0) := Finset.natCast_card_filter _ _
        _ = ∑ k, s k := Finset.sum_congr rfl fun k _ => (hsk k).symm
        _ = 1 := hsum
    have hc : (Finset.univ.filter fun k => s k = 1).card = 1 := by exact_mod_cast hcard
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
    refine ⟨a, ?_, ?_⟩
    · have : a ∈ Finset.univ.filter fun k => s k = 1 := by
        rw [ha]
        exact Finset.mem_singleton_self a
      exact (Finset.mem_filter.1 this).2
    · intro k hk
      have : k ∈ Finset.univ.filter fun k => s k = 1 := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
      rw [ha] at this
      exact Finset.mem_singleton.1 this
  have hrow : ∀ i, ∃! j, Z i j = 1 := fun i => hunique (Z i) (h01 i) (hrow1 i)
  have hcol : ∀ j, ∃! i, Z i j = 1 := fun j =>
    hunique (fun i => Z i j) (fun i => h01 i j) (by simpa only [hsq] using hcol2 j)
  choose f hf hfu using hrow
  have hinj : Function.Injective f := by
    intro i i' hii'
    obtain ⟨k, _, hk⟩ := hcol (f i)
    have h1 : Z i (f i) = 1 := hf i
    have h2 : Z i' (f i) = 1 := by rw [hii']; exact hf i'
    exact (hk i h1).trans (hk i' h2).symm
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  refine ⟨σ, ?_⟩
  ext i j
  rw [permMatrix_apply', hZ']
  have hσ : σ i = f i := rfl
  by_cases hij : f i = j
  · rw [hσ, ite_eq_left hij, ← hij, hf i]
    simp
  · rw [hσ, ite_eq_right hij]
    rcases h01 i j with h | h
    · simp [h]
    · exact absurd (hfu i j h).symm hij

theorem thm_wangxu_perm_iff_level {G : SimpleGraph (Fin n)} {Q : Matrix (Fin n) (Fin n) ℚ}
    (hQ : Q ∈ QG G) : IsPermMatrix Q ↔ level Q = 1 := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact level_permMatrix σ
  · intro h
    have hint := isIntegralMul_level Q
    rw [h] at hint
    exact isPermMatrix_of_integral hQ.1 hQ.2.1 hint

def onesMat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun _ _ => 1

theorem toQ_adj_compl (G : SimpleGraph (Fin n)) :
    toQ (adj (Gᶜ)) = onesMat n - 1 - toQ (adj G) := by
  classical
  ext i j
  simp only [toQ, adj, Matrix.map_apply, SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj,
    Matrix.sub_apply, Matrix.one_apply, onesMat, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · by_cases h : G.Adj i j <;> simp [hij, h]

theorem charpoly_eq_of_conj {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : Qᵀ * Q = 1)
    {A B : Matrix (Fin n) (Fin n) ℤ} (h : Qᵀ * toQ A * Q = toQ B) : A.charpoly = B.charpoly := by
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  let U : (Matrix (Fin n) (Fin n) ℚ)ˣ := ⟨Q, Qᵀ, hQQ, hQ⟩
  have hinv : (U : Matrix (Fin n) (Fin n) ℚ)⁻¹ = Qᵀ := inv_eq_left_inv hQ
  have hc := charpoly_units_conj' U (toQ A)
  rw [hinv] at hc
  change (Qᵀ * toQ A * Q).charpoly = (toQ A).charpoly at hc
  rw [h] at hc
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← charpoly_map, ← charpoly_map]
  exact hc.symm

theorem transpose_mul_ones_mul {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : Qᵀ * Q = 1)
    (he : Q *ᵥ ones n ℚ = ones n ℚ) :
    Qᵀ * onesMat n * Q = onesMat n := by
  have heT := transpose_mulVec_ones hQ he
  ext i j
  have h1 : ∀ l, (Qᵀ * onesMat n) i l = 1 := by
    intro l
    have := congrFun heT i
    simpa [Matrix.mul_apply, mulVec, dotProduct, ones, onesMat] using this
  rw [Matrix.mul_apply]
  simp only [h1, one_mul]
  have := congrFun heT j
  simpa [mulVec, dotProduct, ones, onesMat, Matrix.transpose_apply] using this

theorem sameGenSpectrum_of_conj {G H : SimpleGraph (Fin n)} {Q : Matrix (Fin n) (Fin n) ℚ}
    (hQ : Qᵀ * Q = 1) (he : Q *ᵥ ones n ℚ = ones n ℚ) (h : Qᵀ * toQ (adj G) * Q = toQ (adj H)) :
    SameGenSpectrum G H := by
  refine ⟨charpoly_eq_of_conj hQ h, charpoly_eq_of_conj hQ ?_⟩
  rw [toQ_adj_compl, toQ_adj_compl, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
    transpose_mul_ones_mul hQ he, Matrix.mul_one, hQ, h]

theorem iso_of_permMatrix_conj {G H : SimpleGraph (Fin n)} (σ : Equiv.Perm (Fin n))
    (h : (σ.permMatrix ℚ)ᵀ * toQ (adj G) * σ.permMatrix ℚ = toQ (adj H)) : Nonempty (G ≃g H) := by
  classical
  rw [permMatrix_conj] at h
  refine ⟨⟨σ, ?_⟩⟩
  intro a b
  have := congrFun (congrFun h (σ a)) (σ b)
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, toQ, adj, Matrix.map_apply,
    SimpleGraph.adjMatrix_apply] at this
  by_cases hG : G.Adj a b <;> by_cases hH : H.Adj (σ a) (σ b) <;> simp_all

theorem permMatrix_conj_of_iso {G H : SimpleGraph (Fin n)} (φ : G ≃g H) :
    (Equiv.Perm.permMatrix ℚ φ.toEquiv)ᵀ * toQ (adj G) * Equiv.Perm.permMatrix ℚ φ.toEquiv = toQ (adj H) := by
  classical
  rw [permMatrix_conj]
  ext i j
  simp only [Matrix.submatrix_apply, toQ, adj, Matrix.map_apply, SimpleGraph.adjMatrix_apply]
  have := φ.map_rel_iff' (a := φ.toEquiv.symm i) (b := φ.toEquiv.symm j)
  simp only [Equiv.apply_symm_apply] at this
  by_cases hH : H.Adj i j
  · have hG : G.Adj (φ.toEquiv.symm i) (φ.toEquiv.symm j) := (this.1 (by simpa using hH))
    simp [hH, hG]
  · have hG : ¬ G.Adj (φ.toEquiv.symm i) (φ.toEquiv.symm j) := fun hG => hH (by simpa using this.2 hG)
    simp [hH, hG]

theorem thm_wangxu {G : SimpleGraph (Fin n)} (hG : Controllable G) :
    IsDGS G ↔ ∀ Q ∈ QG G, IsPermMatrix Q := by
  constructor
  · rintro hdgs Q ⟨hQ, he, H, hH⟩
    obtain ⟨φ⟩ := hdgs H (sameGenSpectrum_of_conj hQ he hH)
    set P := Equiv.Perm.permMatrix ℚ φ.toEquiv with hPdef
    have hP := permMatrix_conj_of_iso φ
    have hWG : IsUnit (toQ (walkMatrix (adj G))).det :=
      isUnit_iff_ne_zero.2 (det_walkMatrix_map_ne_zero hG ℚ)
    have eQ : Qᵀ * toQ (walkMatrix (adj G)) = toQ (walkMatrix (adj H)) := by
      simp only [toQ]
      rw [walkMatrix_map, walkMatrix_map]
      exact transpose_mul_walkMatrix hQ he hH
    have eP : Pᵀ * toQ (walkMatrix (adj G)) = toQ (walkMatrix (adj H)) := by
      simp only [toQ]
      rw [walkMatrix_map, walkMatrix_map]
      exact transpose_mul_walkMatrix (permMatrix_transpose_mul _) (permMatrix_mulVec_ones _) hP
    have hQP : Qᵀ = Pᵀ := by
      have := congrArg (· * (toQ (walkMatrix (adj G)))⁻¹) (eQ.trans eP.symm)
      simpa only [Matrix.mul_assoc, mul_nonsing_inv _ hWG, Matrix.mul_one] using this
    exact ⟨φ.toEquiv, transpose_injective hQP⟩
  · intro hall H hH
    obtain ⟨Q, hQ, hconj, -⟩ := thm_wangxu_exists hG hH
    obtain ⟨σ, rfl⟩ := hall Q hQ
    exact iso_of_permMatrix_conj σ hconj

theorem thm_OT (hOT : ORourkeTouriStatement) : Tendsto (fun n : ℕ => probG n Controllable) atTop (𝓝 1) :=
  hOT

end DGS
