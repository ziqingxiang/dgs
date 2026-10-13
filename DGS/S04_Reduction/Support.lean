module

public import DGS.S03_Prelim.SuppD
public import DGS.S03_Prelim.Switching
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

open Matrix Filter Topology

namespace DGS

section SignCols

variable {k N : ℕ}

def signColsR (R : Type*) [One R] [Neg R] (y : Fin k → Fin N → Bool) : Matrix (Fin N) (Fin k) R :=
  Matrix.of fun r j => twoValued (1 : R) (-1) (y j) r

def gramSigns (y : Fin k → Fin N → Bool) : Matrix (Fin k) (Fin k) ℤ :=
  (signColsR ℤ y)ᵀ * signColsR ℤ y

theorem signColsR_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (y : Fin k → Fin N → Bool) :
    (signColsR R y).map f = signColsR S y := by
  ext r j
  simp only [signColsR, twoValued, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem signColsR_mulVec {F : Type*} [Field F] (y : Fin k → Fin N → Bool) (v : Fin k → F) :
    signColsR F y *ᵥ v = ∑ j, v j • twoValued (1 : F) (-1) (y j) := by
  funext r
  simp only [signColsR, mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm]

theorem eq_zero_of_linearIndependent {F : Type*} [Field F] {y : Fin k → Fin N → Bool}
    (hy : LinearIndependent F (fun j => twoValued (1 : F) (-1) (y j))) {v : Fin k → F}
    (hv : signColsR F y *ᵥ v = 0) : v = 0 := by
  rw [signColsR_mulVec] at hv
  funext j
  exact Fintype.linearIndependent_iff.1 hy v hv j

theorem det_gramSigns_ne_zero {y : Fin k → Fin N → Bool}
    (hy : LinearIndependent ℚ (fun j => twoValued (1 : ℚ) (-1) (y j))) : (gramSigns y).det ≠ 0 := by
  intro h0
  have h1 : ((gramSigns y).map (Int.castRingHom ℚ)).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h1
  have hG : (gramSigns y).map (Int.castRingHom ℚ) = (signColsR ℚ y)ᵀ * signColsR ℚ y := by
    rw [gramSigns, Matrix.map_mul, Matrix.transpose_map, signColsR_map]
  rw [hG, ← mulVec_mulVec] at hv
  have h2 : (signColsR ℚ y *ᵥ v) ⬝ᵥ (signColsR ℚ y *ᵥ v) = 0 := by
    have := congrArg (fun x => v ⬝ᵥ x) hv
    simp only [dotProduct_zero] at this
    rw [dotProduct_mulVec, vecMul_transpose] at this
    exact this
  exact hv0 (eq_zero_of_linearIndependent hy (dotProduct_self_eq_zero.1 h2))

theorem eq_zero_of_not_dvd_det {p : ℕ} [Fact p.Prime] {y : Fin k → Fin N → Bool}
    (hκ : ¬ (p : ℤ) ∣ (gramSigns y).det) {L : Type*} [Field L] [Algebra (ZMod p) L] {v : Fin k → L}
    (hv : signColsR L y *ᵥ v = 0) : v = 0 := by
  classical
  set G := (gramSigns y).map (Int.castRingHom L) with hGdef
  have hG : G = (signColsR L y)ᵀ * signColsR L y := by
    rw [hGdef, gramSigns, Matrix.map_mul, Matrix.transpose_map, signColsR_map]
  have hGv : G *ᵥ v = 0 := by rw [hG, ← mulVec_mulVec, hv, mulVec_zero]
  have hdet : G.det ≠ 0 := by
    rw [hGdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast,
      ← map_intCast (algebraMap (ZMod p) L)]
    intro h
    apply hκ
    have h2 : ((gramSigns y).det : ZMod p) = 0 :=
      (algebraMap (ZMod p) L).injective (by rw [h, map_zero])
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2
  have h3 : G.adjugate *ᵥ (G *ᵥ v) = G.det • v := by
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  rw [hGv, mulVec_zero] at h3
  exact (smul_eq_zero.1 h3.symm).resolve_left hdet

theorem eq_zero_of_linearIndependent_zmod {p : ℕ} [Fact p.Prime] {z : Fin k → Fin N → Bool}
    (hz : LinearIndependent (ZMod p) (fun j => twoValued (1 : ZMod p) (-1) (z j)))
    {L : Type*} [Field L] [Algebra (ZMod p) L] {v : Fin k → L} (hv : signColsR L z *ᵥ v = 0) :
    v = 0 := by
  classical
  set M := signColsR (ZMod p) z with hM
  have hker : LinearMap.ker M.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact eq_zero_of_linearIndependent hz (by rw [← mulVecLin_apply]; exact hx)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin hker
  set P := LinearMap.toMatrix' g with hP
  have hPM : P * M = 1 := by
    rw [hP, ← LinearMap.toMatrix'_toLin' M, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply', hg,
      LinearMap.toMatrix'_id]
  have hPM' : P.map (algebraMap (ZMod p) L) * signColsR L z = 1 := by
    rw [← signColsR_map (algebraMap (ZMod p) L), ← hM, ← Matrix.map_mul, hPM, Matrix.map_one _
      (map_zero _) (map_one _)]
  have := congrArg (fun x => P.map (algebraMap (ZMod p) L) *ᵥ x) hv
  simp only [mulVec_mulVec, hPM', one_mulVec, mulVec_zero] at this
  exact this

theorem abs_det_le {A : Matrix (Fin k) (Fin k) ℤ} {B : ℤ} (hA : ∀ i j, |A i j| ≤ B) :
    |A.det| ≤ k.factorial * B ^ k := by
  rw [det_apply]
  calc |∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • ∏ i, A (σ i) i|
      ≤ ∑ σ : Equiv.Perm (Fin k), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), B ^ k := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [Units.smul_def, zsmul_eq_mul, abs_mul]
        have h1 : |((Equiv.Perm.sign σ : ℤˣ) : ℤ)| = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [Int.cast_id, h1, one_mul, Finset.abs_prod]
        calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin k, B :=
              Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hA _ _)
          _ = B ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = k.factorial * B ^ k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem abs_gramSigns_le (y : Fin k → Fin N → Bool) (a b : Fin k) : |gramSigns y a b| ≤ N := by
  simp only [gramSigns, mul_apply, transpose_apply]
  calc |∑ r, signColsR ℤ y r a * signColsR ℤ y r b| ≤ ∑ r : Fin N, |signColsR ℤ y r a * signColsR ℤ y r b| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin N, (1 : ℤ) := by
        refine Finset.sum_le_sum fun r _ => ?_
        simp only [signColsR, twoValued, Matrix.of_apply]
        split_ifs <;> simp
    _ = N := by simp

theorem card_primeFactors_le {κ : ℤ} (hκ : κ ≠ 0) {e : ℕ} (h : |κ| ≤ 2 ^ e) :
    κ.natAbs.primeFactors.card ≤ e := by
  have h1 : 2 ^ κ.natAbs.primeFactors.card ≤ ∏ p ∈ κ.natAbs.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have h2 : ∏ p ∈ κ.natAbs.primeFactors, p ≤ κ.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.2 hκ) (Nat.prod_primeFactors_dvd _)
  have h3 : κ.natAbs ≤ 2 ^ e := by
    have : ((κ.natAbs : ℕ) : ℤ) ≤ ((2 ^ e : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      push_cast
      exact h
    exact_mod_cast this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans (h2.trans h3))

theorem card_primeFactors_gramSigns_le {y : Fin k → Fin N → Bool} (hκ : (gramSigns y).det ≠ 0) :
    (gramSigns y).det.natAbs.primeFactors.card ≤ k * (k + N) := by
  apply card_primeFactors_le hκ
  refine (abs_det_le (abs_gramSigns_le y)).trans ?_
  have h1 : (k.factorial : ℤ) ≤ 2 ^ (k * k) := by
    have : k.factorial ≤ 2 ^ (k * k) :=
      (Nat.factorial_le_pow k).trans (by
        rw [pow_mul]
        exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le k)
    exact_mod_cast this
  have h2 : (N : ℤ) ^ k ≤ 2 ^ (k * N) := by
    have : N ^ k ≤ 2 ^ (k * N) := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le k
    exact_mod_cast this
  calc (k.factorial : ℤ) * (N : ℤ) ^ k ≤ 2 ^ (k * k) * 2 ^ (k * N) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 2 ^ (k * (k + N)) := by rw [← pow_add, mul_add]

end SignCols

section Cols

variable {k N₁ N₂ : ℕ}

def BadCols (y : Fin k → Fin N₁ → Bool) (z : Fin k → Fin N₂ → Bool) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod p) L) (v : Fin k → L),
    v ≠ 0 ∧ signColsR L y *ᵥ v = 0 ∧ signColsR L z *ᵥ v = 0

theorem one_ne_neg_one_zmod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (1 : ZMod p) ≠ -1 := by
  intro h
  have h2 : (2 : ZMod p) = 0 := by
    have : (2 : ZMod p) = 1 - (-1) := by ring
    rw [this, ← h, sub_self]
  exact two_ne_zero_zmod hp h2

theorem prob_badCols_le :
    prob (fun x : (Fin k → Fin N₁ → Bool) × (Fin k → Fin N₂ → Bool) => BadCols x.1 x.2) ≤
      ((2 : ℝ) ^ k - 1) / 2 ^ N₁ + (k * (k + N₁) : ℕ) * (((2 : ℝ) ^ k - 1) / 2 ^ N₂) := by
  classical
  set LQ : (Fin k → Fin N₁ → Bool) → Prop :=
    fun y => LinearIndependent ℚ (fun j => twoValued (1 : ℚ) (-1) (y j)) with hLQ
  set LP : ℕ → (Fin k → Fin N₂ → Bool) → Prop := fun p z => ∃ _ : Fact p.Prime,
    LinearIndependent (ZMod p) (fun j => twoValued (1 : ZMod p) (-1) (z j)) with hLP
  have hsub : ∀ x : (Fin k → Fin N₁ → Bool) × (Fin k → Fin N₂ → Bool), BadCols x.1 x.2 →
      ¬ LQ x.1 ∨ (LQ x.1 ∧ ∃ p ∈ (gramSigns x.1).det.natAbs.primeFactors, p ≠ 2 ∧ ¬ LP p x.2) := by
    rintro ⟨y, z⟩ ⟨p, hp, hp2, L, _, _, v, hv0, hvy, hvz⟩
    have : Fact p.Prime := ⟨hp⟩
    by_cases hy : LQ y
    · right
      refine ⟨hy, p, ?_, hp2, ?_⟩
      · have hκ := det_gramSigns_ne_zero hy
        have hdvd : (p : ℤ) ∣ (gramSigns y).det := by
          by_contra h
          exact hv0 (eq_zero_of_not_dvd_det h hvy)
        exact Nat.mem_primeFactors.2 ⟨hp, Int.natCast_dvd.1 hdvd, Int.natAbs_ne_zero.2 hκ⟩
      · rintro ⟨_, hz⟩
        exact hv0 (eq_zero_of_linearIndependent_zmod hz hvz)
    · exact Or.inl hy
  refine (prob_mono hsub).trans ((prob_or_le _ _).trans (add_le_add ?_ ?_))
  · rw [prob_fst (fun y => ¬ LQ y)]
    exact prob_not_linearIndependent (1 : ℚ) (-1) (by norm_num) k
  · refine prob_le_of_forall_fst (fun y => ?_) (by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      positivity)
    by_cases hy : LQ y
    · calc prob (fun z => LQ (y, z).1 ∧ ∃ p ∈ (gramSigns (y, z).1).det.natAbs.primeFactors,
              p ≠ 2 ∧ ¬ LP p (y, z).2)
          ≤ prob (fun z => ∃ p ∈ (gramSigns y).det.natAbs.primeFactors, p ≠ 2 ∧ ¬ LP p z) :=
            prob_mono fun z h => h.2
        _ ≤ ∑ p ∈ (gramSigns y).det.natAbs.primeFactors, prob (fun z => p ≠ 2 ∧ ¬ LP p z) :=
            prob_exists_le_sum _ _
        _ ≤ ∑ _p ∈ (gramSigns y).det.natAbs.primeFactors, ((2 : ℝ) ^ k - 1) / 2 ^ N₂ := by
            refine Finset.sum_le_sum fun p hp => ?_
            have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
            by_cases hp2 : p = 2
            · have : prob (fun z : Fin k → Fin N₂ → Bool => p ≠ 2 ∧ ¬ LP p z) = 0 := by
                rw [← prob_false (Ω := Fin k → Fin N₂ → Bool)]
                exact prob_congr fun z => by simp [hp2]
              rw [this]
              have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
              positivity
            · refine (prob_mono fun z hz => ?_).trans
                (prob_not_linearIndependent (1 : ZMod p) (-1) (one_ne_neg_one_zmod hp2) k)
              intro hlin
              exact hz.2 ⟨inferInstance, hlin⟩
        _ = (gramSigns y).det.natAbs.primeFactors.card * (((2 : ℝ) ^ k - 1) / 2 ^ N₂) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (k * (k + N₁) : ℕ) * (((2 : ℝ) ^ k - 1) / 2 ^ N₂) := by
            have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
            have h2 : (0 : ℝ) ≤ ((2 : ℝ) ^ k - 1) / 2 ^ N₂ := by positivity
            have h3 := card_primeFactors_gramSigns_le (det_gramSigns_ne_zero hy)
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast h3) h2
    · have : prob (fun z : Fin k → Fin N₂ → Bool => LQ (y, z).1 ∧
          ∃ p ∈ (gramSigns (y, z).1).det.natAbs.primeFactors, p ≠ 2 ∧ ¬ LP p (y, z).2) = 0 := by
        rw [← prob_false (Ω := Fin k → Fin N₂ → Bool)]
        exact prob_congr fun z => by simp [hy]
      rw [this]
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      positivity

end Cols

section FixedSet

def rowSplitEquiv (k N₁ N₂ : ℕ) :
    (Fin k → Fin (N₁ + N₂) → Bool) ≃ (Fin k → Fin N₁ → Bool) × (Fin k → Fin N₂ → Bool) where
  toFun c := (fun j r => c j (Fin.castAdd N₂ r), fun j r => c j (Fin.natAdd N₁ r))
  invFun x := fun j => Fin.append (x.1 j) (x.2 j)
  left_inv c := by
    funext j
    exact Fin.append_castAdd_natAdd
  right_inv x := by
    refine Prod.ext (funext fun j => funext fun r => ?_) (funext fun j => funext fun r => ?_)
    · exact Fin.append_left _ _ r
    · exact Fin.append_right _ _ r

def BadBlock {n k : ℕ} (c : Fin k → Fin n → Bool) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod p) L) (v : Fin k → L),
    v ≠ 0 ∧ signColsR L c *ᵥ v = 0

theorem prob_badBlock_le (k N₁ N₂ : ℕ) :
    prob (fun c : Fin k → Fin (N₁ + N₂) → Bool => BadBlock c) ≤
      ((2 : ℝ) ^ k - 1) / 2 ^ N₁ + (k * (k + N₁) : ℕ) * (((2 : ℝ) ^ k - 1) / 2 ^ N₂) := by
  refine le_trans ?_ (prob_badCols_le (k := k) (N₁ := N₁) (N₂ := N₂))
  rw [← prob_equiv (rowSplitEquiv k N₁ N₂).symm (fun c => BadBlock c)]
  apply prob_mono
  rintro ⟨y, z⟩ ⟨p, hp, hp2, L, _, _, v, hv0, hv⟩
  refine ⟨p, hp, hp2, L, inferInstance, inferInstance, v, hv0, ?_, ?_⟩
  · funext r
    have := congrFun hv (Fin.castAdd N₂ r)
    simpa [signColsR, mulVec, dotProduct, rowSplitEquiv, Fin.append_left, twoValued] using this
  · funext r
    have := congrFun hv (Fin.natAdd N₁ r)
    simpa [signColsR, mulVec, dotProduct, rowSplitEquiv, Fin.append_right, twoValued] using this

def BadSupp {m : ℕ} (I : Finset (Fin m)) (ω : Pairs m → Bool) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod p) L) (w : Fin m → L),
    w ≠ 0 ∧ (∀ i ∉ I, w i = 0) ∧ ∀ i ∉ I, ((seidelOf ω).map (Int.castRingHom L) *ᵥ w) i = 0

theorem blockC_seidelOf_map {n k : ℕ} {L : Type*} [Field L] (ω : Pairs (n + k) → Bool) :
    blockC ((seidelOf ω).map (Int.castRingHom L)) = signColsR L (blockEquiv n k ω).2.1 := by
  ext i j
  simp only [blockC, Matrix.of_apply, Matrix.map_apply, seidelOf, symOf_block_RS, signColsR,
    twoValued]
  split_ifs <;> simp

theorem prob_badSupp_le {m n k : ℕ} (hm : n + k = m) (I : Finset (Fin m)) (hI : I.card = k)
    (N₁ N₂ : ℕ) (hn : N₁ + N₂ = n) :
    prob (BadSupp I) ≤
      ((2 : ℝ) ^ k - 1) / 2 ^ N₁ + (k * (k + N₁) : ℕ) * (((2 : ℝ) ^ k - 1) / 2 ^ N₂) := by
  subst hm
  subst hn
  obtain ⟨σ, hσ⟩ := exists_perm_compl I hI
  refine le_trans ?_ (prob_badBlock_le k N₁ N₂)
  have h1 : prob (fun c : Fin k → Fin (N₁ + N₂) → Bool => BadBlock c) =
      prob (fun ω : Pairs (N₁ + N₂ + k) → Bool => BadBlock (blockEquiv (N₁ + N₂) k ω).2.1) := by
    rw [← prob_equiv (blockEquiv (N₁ + N₂) k).symm]
    simp only [Equiv.apply_symm_apply]
    rw [prob_snd (fun x : (Fin k → Fin (N₁ + N₂) → Bool) × (Pairs k → Bool) => BadBlock x.1),
      prob_fst]
  rw [h1, ← prob_comp_permPairs σ (fun ω => BadBlock (blockEquiv (N₁ + N₂) k ω).2.1)]
  apply prob_mono
  rintro ω ⟨p, hp, hp2, L, _, _, w, hw0, hwI, hrow⟩
  set A := (seidelOf ω).map (Int.castRingHom L) with hA
  set w' : Fin (N₁ + N₂ + k) → L := w ∘ σ with hw'
  have hw'0 : w' ≠ 0 := by
    intro h
    apply hw0
    funext x
    have := congrFun h (σ.symm x)
    simpa [hw'] using this
  have htop : topPart w' = 0 := by
    funext i
    exact hwI _ (hσ i)
  have hA' : (seidelOf (ω ∘ permPairs σ)).map (Int.castRingHom L) = A.submatrix σ σ := by
    rw [seidelOf, symOf_comp_permPairs, hA, seidelOf, Matrix.submatrix_map]
  have hrow' : topPart ((seidelOf (ω ∘ permPairs σ)).map (Int.castRingHom L) *ᵥ w') = 0 := by
    rw [hA']
    funext i
    rw [topPart, Matrix.submatrix_mulVec_equiv]
    simp only [Function.comp_apply, hw']
    have : (w ∘ ⇑σ) ∘ ⇑σ.symm = w := by
      funext x
      simp
    rw [this]
    exact hrow _ (hσ i)
  refine ⟨p, hp, hp2, L, inferInstance, inferInstance, botPart w', botPart_ne_zero hw'0 htop, ?_⟩
  rw [topPart_mulVec, htop, mulVec_zero, zero_add, blockC_seidelOf_map] at hrow'
  exact hrow'

end FixedSet

section Estimates

theorem choose_le_twenty (m k : ℕ) (hk : k ≤ m) :
    (m.choose k : ℝ) ≤ (20 : ℝ) ^ k * (20 / 19 : ℝ) ^ (m - k) := by
  have hbin : ∑ j ∈ Finset.range (m + 1), ((1 : ℝ) / 20) ^ j * (19 / 20) ^ (m - j) * (m.choose j) = 1 := by
    rw [← add_pow]
    norm_num
  have hterm : ((1 : ℝ) / 20) ^ k * (19 / 20) ^ (m - k) * (m.choose k) ≤ 1 :=
    (Finset.single_le_sum (f := fun j => ((1 : ℝ) / 20) ^ j * (19 / 20) ^ (m - j) * (m.choose j))
      (fun j _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))).trans_eq hbin
  have h1 : ((1 : ℝ) / 20) ^ k * (19 / 20) ^ (m - k) * ((20 : ℝ) ^ k * (20 / 19 : ℝ) ^ (m - k)) = 1 := by
    rw [mul_mul_mul_comm, ← mul_pow, ← mul_pow]
    norm_num
  have hpos : (0 : ℝ) < ((1 : ℝ) / 20) ^ k * (19 / 20) ^ (m - k) := by positivity
  have h2 : (m.choose k : ℝ) = (((1 : ℝ) / 20) ^ k * (19 / 20) ^ (m - k) * (m.choose k)) *
      ((20 : ℝ) ^ k * (20 / 19 : ℝ) ^ (m - k)) := by
    rw [mul_comm (((1 : ℝ) / 20) ^ k * (19 / 20) ^ (m - k)) (m.choose k : ℝ), mul_assoc, h1, mul_one]
  rw [h2]
  have h3 : (0 : ℝ) ≤ (20 : ℝ) ^ k * (20 / 19 : ℝ) ^ (m - k) := by positivity
  calc (((1 : ℝ) / 20) ^ k * (19 / 20) ^ (m - k) * (m.choose k)) *
        ((20 : ℝ) ^ k * (20 / 19 : ℝ) ^ (m - k))
      ≤ 1 * ((20 : ℝ) ^ k * (20 / 19 : ℝ) ^ (m - k)) := mul_le_mul_of_nonneg_right hterm h3
    _ = (20 : ℝ) ^ k * (20 / 19 : ℝ) ^ (m - k) := one_mul _

theorem support_rate_le : (40 : ℝ) ^ ((1 : ℝ) / 20) * (20 / 19) * (2 : ℝ) ^ (-(7 / 20 : ℝ)) ≤ 0.994 := by
  have hx : 0 ≤ (40 : ℝ) ^ ((1 : ℝ) / 20) * (20 / 19) * (2 : ℝ) ^ (-(7 / 20 : ℝ)) := by positivity
  rw [← pow_le_pow_iff_left₀ hx (by norm_num) (by norm_num : (20 : ℕ) ≠ 0)]
  have h40 : ((40 : ℝ) ^ ((1 : ℝ) / 20)) ^ (20 : ℕ) = 40 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h2 : ((2 : ℝ) ^ (-(7 / 20 : ℝ))) ^ (20 : ℕ) = 1 / 128 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show (-(7 / 20 : ℝ)) * ((20 : ℕ) : ℝ) = -((7 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    norm_num
  rw [mul_pow, mul_pow, h40, h2]
  norm_num

theorem eventually_support_bound :
    ∀ᶠ m : ℕ in atTop, (m.choose (m / 20) : ℝ) * (1 + (m : ℝ) ^ 2) *
      ((2 : ℝ) ^ (m / 20) / 2 ^ ((m - m / 20) / 2)) ≤ (2 : ℝ) ^ (-(m : ℝ) / 8) := by
  set r : ℝ := 0.994 with hr
  have hF1 : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ 2 * r ^ m < 1 / 4 :=
    (tendsto_order.1 (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
      (by rw [hr]; norm_num : |r| < 1))).2 _ (by norm_num)
  have hF2 : ∀ᶠ m : ℕ in atTop, r ^ m < 1 / 4 :=
    (tendsto_order.1 (tendsto_pow_atTop_nhds_zero_of_lt_one (by rw [hr]; norm_num)
      (by rw [hr]; norm_num : r < 1))).2 _ (by norm_num)
  filter_upwards [hF1, hF2] with m h1 h2
  set k := m / 20 with hk
  set N₁ := (m - k) / 2 with hN₁
  have hk20 : 20 * k ≤ m := by rw [hk]; exact Nat.mul_div_le m 20
  have hkm : k ≤ m := by omega
  have hN₁' : m - k ≤ 2 * N₁ + 1 := by rw [hN₁]; omega
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hC : (m.choose k : ℝ) * (2 : ℝ) ^ k ≤ (40 : ℝ) ^ ((m : ℝ) / 20) * (20 / 19 : ℝ) ^ m := by
    have h3 := choose_le_twenty m k hkm
    have h4 : (20 / 19 : ℝ) ^ (m - k) ≤ (20 / 19 : ℝ) ^ m :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le m k)
    have h5 : (40 : ℝ) ^ k ≤ (40 : ℝ) ^ ((m : ℝ) / 20) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (20 : ℝ) * k ≤ m := by exact_mod_cast hk20
      linarith
    calc (m.choose k : ℝ) * (2 : ℝ) ^ k ≤ ((20 : ℝ) ^ k * (20 / 19 : ℝ) ^ (m - k)) * (2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (40 : ℝ) ^ k * (20 / 19 : ℝ) ^ (m - k) := by
          rw [mul_right_comm, ← mul_pow]
          norm_num
      _ ≤ (40 : ℝ) ^ ((m : ℝ) / 20) * (20 / 19 : ℝ) ^ m := mul_le_mul h5 h4 (by positivity) (by positivity)
  have hN : (1 : ℝ) / 2 ^ N₁ ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) * (2 : ℝ) ^ (-(19 * (m : ℝ) / 40)) := by
    rw [← Real.rpow_add two_pos, one_div, ← Real.rpow_natCast, ← Real.rpow_neg two_pos.le]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h6 : ((m - k : ℕ) : ℝ) ≤ 2 * N₁ + 1 := by exact_mod_cast hN₁'
    have h7 : ((m - k : ℕ) : ℝ) = m - k := Nat.cast_sub hkm
    have h8 : (20 : ℝ) * k ≤ m := by exact_mod_cast hk20
    linarith
  set ρ : ℝ := (40 : ℝ) ^ ((1 : ℝ) / 20) * (20 / 19) * (2 : ℝ) ^ (-(7 / 20 : ℝ)) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρm : (40 : ℝ) ^ ((m : ℝ) / 20) * (20 / 19 : ℝ) ^ m * (2 : ℝ) ^ (-(19 * (m : ℝ) / 40)) =
      ρ ^ m * (2 : ℝ) ^ (-(m : ℝ) / 8) := by
    rw [hρ, mul_pow, mul_pow, ← Real.rpow_natCast ((40 : ℝ) ^ ((1 : ℝ) / 20)),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-(7 / 20 : ℝ))),
      ← Real.rpow_mul (by norm_num)]
    have e1 : (1 : ℝ) / 20 * (m : ℝ) = (m : ℝ) / 20 := by ring
    rw [e1, mul_assoc, mul_assoc, mul_assoc]
    congr 2
    rw [← Real.rpow_add two_pos]
    congr 1
    ring
  have hρm' : ρ ^ m ≤ r ^ m := pow_le_pow_left₀ hρ0 support_rate_le m
  have hsqrt : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h2m : (0 : ℝ) < (2 : ℝ) ^ (-(m : ℝ) / 8) := Real.rpow_pos_of_pos two_pos _
  have hrm : 0 ≤ r ^ m := pow_nonneg (by rw [hr]; norm_num) m
  calc (m.choose k : ℝ) * (1 + (m : ℝ) ^ 2) * ((2 : ℝ) ^ k / 2 ^ N₁)
      = (1 + (m : ℝ) ^ 2) * (((m.choose k : ℝ) * (2 : ℝ) ^ k) * (1 / 2 ^ N₁)) := by ring
    _ ≤ (1 + (m : ℝ) ^ 2) * (((40 : ℝ) ^ ((m : ℝ) / 20) * (20 / 19 : ℝ) ^ m) *
          ((2 : ℝ) ^ ((1 : ℝ) / 2) * (2 : ℝ) ^ (-(19 * (m : ℝ) / 40)))) := by
        gcongr
    _ = (1 + (m : ℝ) ^ 2) * (2 : ℝ) ^ ((1 : ℝ) / 2) * (ρ ^ m * (2 : ℝ) ^ (-(m : ℝ) / 8)) := by
        rw [← hρm]; ring
    _ ≤ (1 + (m : ℝ) ^ 2) * 2 * (r ^ m * (2 : ℝ) ^ (-(m : ℝ) / 8)) := by
        gcongr
    _ = 2 * (r ^ m + (m : ℝ) ^ 2 * r ^ m) * (2 : ℝ) ^ (-(m : ℝ) / 8) := by ring
    _ ≤ 2 * (1 / 4 + 1 / 4) * (2 : ℝ) ^ (-(m : ℝ) / 8) := by
        gcongr
    _ = (2 : ℝ) ^ (-(m : ℝ) / 8) := by ring

end Estimates

def SuppGood {m : ℕ} (S : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (L : Type) [Field L] [Algebra (ZMod p) L] (μ : L) (w : Fin m → L),
    w ≠ 0 → S.map (Int.castRingHom L) *ᵥ w = μ • w →
      ∀ I : Finset (Fin m), (∀ i ∉ I, w i = 0) → (m : ℝ) / 20 < (I.card : ℝ)

theorem lem_support :
    ∀ᶠ m : ℕ in atTop, probSeidel m (fun S => ¬ SuppGood S) ≤ (2 : ℝ) ^ (-(m : ℝ) / 8) := by
  filter_upwards [eventually_support_bound] with m hm
  classical
  set k := m / 20 with hk
  set N₁ := (m - k) / 2 with hN₁
  set N₂ := m - k - N₁ with hN₂
  have hkm : k ≤ m := Nat.div_le_self m 20
  have hsub : ∀ ω : Pairs m → Bool, ¬ SuppGood (seidelOf ω) →
      ∃ I ∈ (Finset.univ : Finset (Fin m)).powersetCard k, BadSupp I ω := by
    intro ω hω
    unfold SuppGood at hω
    push Not at hω
    obtain ⟨p, hp, hp2, L, _, _, μ, w, hw0, hw, T, hT, hsupp⟩ := hω
    have hTk : T.card ≤ k := by
      rw [hk]
      apply Nat.le_div_iff_mul_le (by norm_num) |>.2
      have : (T.card : ℝ) * 20 ≤ m := by linarith
      exact_mod_cast this
    obtain ⟨I, hTI, hIcard⟩ := Finset.exists_superset_card_eq hTk (by simpa using hkm)
    have hwI : ∀ i ∉ I, w i = 0 := fun i hi => hT i (fun h => hi (hTI h))
    refine ⟨I, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hIcard⟩, p, hp, hp2, L,
      inferInstance, inferInstance, w, hw0, hwI, ?_⟩
    intro i hi
    rw [hw, Pi.smul_apply, hwI i hi, smul_zero]
  have hbound : ∀ I ∈ (Finset.univ : Finset (Fin m)).powersetCard k, prob (BadSupp I) ≤
      ((2 : ℝ) ^ k - 1) / 2 ^ N₁ + (k * (k + N₁) : ℕ) * (((2 : ℝ) ^ k - 1) / 2 ^ N₂) := by
    intro I hI
    exact prob_badSupp_le (n := m - k) (k := k) (by omega) I (Finset.mem_powersetCard.1 hI).2 N₁ N₂
      (by omega)
  have hcard : ((Finset.univ : Finset (Fin m)).powersetCard k).card = m.choose k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hone : ((2 : ℝ) ^ k - 1) / 2 ^ N₁ + (k * (k + N₁) : ℕ) * (((2 : ℝ) ^ k - 1) / 2 ^ N₂) ≤
      (1 + (m : ℝ) ^ 2) * ((2 : ℝ) ^ k / 2 ^ N₁) := by
    have hN : N₁ ≤ N₂ := by omega
    have h1 : ((2 : ℝ) ^ k - 1) / 2 ^ N₁ ≤ (2 : ℝ) ^ k / 2 ^ N₁ :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : ((2 : ℝ) ^ k - 1) / 2 ^ N₂ ≤ (2 : ℝ) ^ k / 2 ^ N₁ := by
      have h3 : ((2 : ℝ) ^ k - 1) / 2 ^ N₂ ≤ (2 : ℝ) ^ k / 2 ^ N₂ :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      refine h3.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by norm_num) hN))
    have h4 : ((k * (k + N₁) : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 := by
      have : k * (k + N₁) ≤ m * m := Nat.mul_le_mul hkm (by omega)
      have : ((k * (k + N₁) : ℕ) : ℝ) ≤ ((m * m : ℕ) : ℝ) := by exact_mod_cast this
      rw [sq]
      exact_mod_cast this
    have h5 : (0 : ℝ) ≤ ((2 : ℝ) ^ k - 1) / 2 ^ N₂ := by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      exact div_nonneg (by linarith) (by positivity)
    have h6 : (0 : ℝ) ≤ (2 : ℝ) ^ k / 2 ^ N₁ := by positivity
    calc ((2 : ℝ) ^ k - 1) / 2 ^ N₁ + (k * (k + N₁) : ℕ) * (((2 : ℝ) ^ k - 1) / 2 ^ N₂)
        ≤ (2 : ℝ) ^ k / 2 ^ N₁ + (m : ℝ) ^ 2 * ((2 : ℝ) ^ k / 2 ^ N₁) := by
          gcongr
      _ = (1 + (m : ℝ) ^ 2) * ((2 : ℝ) ^ k / 2 ^ N₁) := by ring
  calc probSeidel m (fun S => ¬ SuppGood S)
      ≤ prob (fun ω : Pairs m → Bool => ∃ I ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          BadSupp I ω) := prob_mono hsub
    _ ≤ ∑ I ∈ (Finset.univ : Finset (Fin m)).powersetCard k, prob (BadSupp I) :=
        prob_exists_le_sum _ _
    _ ≤ ∑ _I ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (1 + (m : ℝ) ^ 2) * ((2 : ℝ) ^ k / 2 ^ N₁) :=
        Finset.sum_le_sum fun I hI => (hbound I hI).trans hone
    _ = (m.choose k : ℝ) * (1 + (m : ℝ) ^ 2) * ((2 : ℝ) ^ k / 2 ^ N₁) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_assoc]
    _ ≤ (2 : ℝ) ^ (-(m : ℝ) / 8) := hm

end DGS
