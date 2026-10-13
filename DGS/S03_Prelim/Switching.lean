module

public import DGS.S03_Prelim.LocalFailures
public import DGS.S03_Prelim.SimpleSubmodules
public import DGS.Core.Seidel

@[expose] public section

open Matrix Polynomial Module

namespace DGS

variable {n : ℕ}

def signVec (b : Fin n → Bool) : Fin n → ℤ := fun i => if b i then 1 else -1

def signMat (b : Fin n → Bool) : Matrix (Fin n) (Fin n) ℤ := Matrix.diagonal (signVec b)

noncomputable def switched (G : SimpleGraph (Fin n)) (b : Fin n → Bool) : Matrix (Fin n) (Fin n) ℤ :=
  signMat b * seidelOfGraph G * signMat b

def modPVec (p : ℕ) (v : Fin n → ℤ) : Fin n → ZMod p := fun i => (v i : ZMod p)

def switchSigns (b : Fin n → Bool) (ω : Pairs n → Bool) : Pairs n → Bool :=
  fun q => (ω q == (b q.1.1 == b q.1.2))

theorem signVec_mul_self (b : Fin n → Bool) (i : Fin n) : signVec b i * signVec b i = 1 := by
  unfold signVec
  cases b i <;> simp

theorem signMat_mul_self (b : Fin n → Bool) : signMat b * signMat b = 1 := by
  rw [signMat, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact signVec_mul_self b i

theorem signMat_transpose (b : Fin n → Bool) : (signMat b)ᵀ = signMat b :=
  diagonal_transpose _

theorem signMat_mulVec_ones (b : Fin n → Bool) : signMat b *ᵥ ones n ℤ = signVec b := by
  funext i
  rw [signMat, mulVec_diagonal]
  simp [ones]

theorem switchSigns_switchSigns (b : Fin n → Bool) (ω : Pairs n → Bool) :
    switchSigns b (switchSigns b ω) = ω := by
  funext q
  unfold switchSigns
  cases ω q <;> cases b q.1.1 <;> cases b q.1.2 <;> rfl

theorem sign_mul_sign (x y z : Bool) :
    ((if x = true then (1 : ℤ) else -1) * if y = true then 1 else -1) * (if z = true then 1 else -1) =
      if (y == (x == z)) = true then 1 else -1 := by
  cases x <;> cases y <;> cases z <;> rfl

theorem sign_mul_sign' (x y z : Bool) :
    ((if x = true then (1 : ℤ) else -1) * if y = true then 1 else -1) * (if z = true then 1 else -1) =
      if (y == (z == x)) = true then 1 else -1 := by
  cases x <;> cases y <;> cases z <;> rfl

theorem signMat_mul_seidelOf_mul (b : Fin n → Bool) (ω : Pairs n → Bool) :
    signMat b * seidelOf ω * signMat b = seidelOf (switchSigns b ω) := by
  ext i j
  rw [signMat, mul_diagonal, diagonal_mul]
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [seidelOf, symOf_apply_lt _ _ _ h, switchSigns, signVec]
    exact sign_mul_sign _ _ _
  · simp [seidelOf]
  · simp only [seidelOf, symOf_apply_gt _ _ _ h, switchSigns, signVec]
    exact sign_mul_sign' _ _ _

theorem lem_switch (n : ℕ) (P : Matrix (Fin n) (Fin n) ℤ → (Fin n → ℤ) → Prop) :
    prob (fun x : SimpleGraph (Fin n) × (Fin n → Bool) =>
        P (switched x.1 x.2) (signMat x.2 *ᵥ ones n ℤ)) =
      prob (fun x : (Pairs n → Bool) × (Fin n → Bool) => P (seidelOf x.1) (signVec x.2)) := by
  let e1 : (Pairs n → Bool) × (Fin n → Bool) ≃ SimpleGraph (Fin n) × (Fin n → Bool) :=
    (Equiv.ofBijective _ graphOf_bijective).prodCongr (Equiv.refl _)
  let e2 : (Pairs n → Bool) × (Fin n → Bool) ≃ (Pairs n → Bool) × (Fin n → Bool) :=
    { toFun := fun x => (switchSigns x.2 (fun q => !x.1 q), x.2)
      invFun := fun x => (fun q => !(switchSigns x.2 x.1 q), x.2)
      left_inv := fun x => by
        ext q
        · simp [switchSigns_switchSigns]
        · rfl
      right_inv := fun x => by
        ext q
        · simp only [Bool.not_not]
          exact congrFun (switchSigns_switchSigns x.2 x.1) q
        · rfl }
  rw [← prob_equiv e1, ← prob_equiv e2 (fun x => P (seidelOf x.1) (signVec x.2))]
  congr 1
  funext x
  simp only [e1, e2, Equiv.prodCongr_apply, Equiv.ofBijective_apply, Equiv.coe_refl, Prod.map,
    id, Equiv.coe_fn_mk, switched, seidelOfGraph_graphOf, signMat_mul_seidelOf_mul,
    signMat_mulVec_ones]

section Transport

variable {F : Type*} [Field F] {T M M' : Matrix (Fin n) (Fin n) F}

theorem map_map_of_mul_self (hT : T * T = 1) (W : Submodule F (Fin n → F)) :
    (W.map T.mulVecLin).map T.mulVecLin = W := by
  rw [← Submodule.map_comp, ← mulVecLin_mul, hT, mulVecLin_one, Submodule.map_id]

theorem isInvariant_map (hTM : T * M = M' * T) {U : Submodule F (Fin n → F)} (hU : IsInvariant M U) :
    IsInvariant M' (U.map T.mulVecLin) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨M *ᵥ x, hU x hx, ?_⟩
  simp only [mulVecLin_apply]
  rw [mulVec_mulVec, hTM, ← mulVec_mulVec]

theorem mul_comm_of_mul_self (hT : T * T = 1) (hTM : T * M = M' * T) : T * M' = M * T := by
  calc T * M' = T * M' * (T * T) := by rw [hT, Matrix.mul_one]
    _ = T * (M' * T) * T := by simp only [Matrix.mul_assoc]
    _ = T * (T * M) * T := by rw [hTM]
    _ = (T * T) * M * T := by simp only [Matrix.mul_assoc]
    _ = M * T := by rw [hT, Matrix.one_mul]

theorem isSimpleInvariant_map (hT : T * T = 1) (hTM : T * M = M' * T) {U : Submodule F (Fin n → F)}
    (hU : IsSimpleInvariant M U) : IsSimpleInvariant M' (U.map T.mulVecLin) := by
  have hTM' := mul_comm_of_mul_self hT hTM
  refine ⟨isInvariant_map hTM hU.1, ?_, ?_⟩
  · intro hb
    apply hU.2.1
    rw [← map_map_of_mul_self hT U, hb, Submodule.map_bot]
  · intro W hW hWU
    have h1 : W.map T.mulVecLin ≤ U := by
      rw [← map_map_of_mul_self hT U]
      exact Submodule.map_mono hWU
    rcases hU.2.2 _ (isInvariant_map hTM' hW) h1 with h | h
    · left
      rw [← map_map_of_mul_self hT W, h, Submodule.map_bot]
    · right
      rw [← map_map_of_mul_self hT W, h]

theorem pow_intertwine (hTM : T * M = M' * T) (k : ℕ) : T * M ^ k = M' ^ k * T := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hTM, ← Matrix.mul_assoc, ← pow_succ]

theorem aeval_intertwine (hTM : T * M = M' * T) (f : F[X]) : T * aeval M f = aeval M' f * T := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, smul_mul_assoc, Matrix.one_mul,
      Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, pow_intertwine hTM]

theorem hasType_map (hTM : T * M = M' * T) {U : Submodule F (Fin n → F)}
    {β : F[X]} (hβ : HasType M U β) : HasType M' (U.map T.mulVecLin) β := by
  refine ⟨hβ.1, hβ.2.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  simp only [mulVecLin_apply]
  rw [mulVec_mulVec, ← aeval_intertwine hTM, ← mulVec_mulVec, hβ.2.2 x hx, mulVec_zero]

theorem dotProduct_mulVec_mulVec (hTT : Tᵀ * T = 1) (x y : Fin n → F) :
    (T *ᵥ x) ⬝ᵥ (T *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hTT, one_mulVec]

theorem isTotallyIsotropic_map (hTT : Tᵀ * T = 1) {U : Submodule F (Fin n → F)}
    (hU : IsTotallyIsotropic U) : IsTotallyIsotropic (U.map T.mulVecLin) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  simp only [mulVecLin_apply]
  rw [dotProduct_mulVec_mulVec hTT]
  exact hU x hx y hy

theorem orth_map (hTT : Tᵀ * T = 1) {U : Submodule F (Fin n → F)} {e : Fin n → F}
    (h : ∀ x ∈ U, e ⬝ᵥ x = 0) : ∀ y ∈ U.map T.mulVecLin, (T *ᵥ e) ⬝ᵥ y = 0 := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [mulVecLin_apply]
  rw [dotProduct_mulVec_mulVec hTT]
  exact h x hx

end Transport

section Perp

variable {F : Type*} [Field F] {A S : Matrix (Fin n) (Fin n) F}

theorem isInvariant_iff_of_perp (h2 : (2 : F) ≠ 0)
    (hrel : ∀ x, ones n F ⬝ᵥ x = 0 → S *ᵥ x = -x - (2 : F) • (A *ᵥ x))
    {U : Submodule F (Fin n → F)} (hU : ∀ x ∈ U, ones n F ⬝ᵥ x = 0) :
    IsInvariant A U ↔ IsInvariant S U := by
  constructor
  · intro hA x hx
    rw [hrel x (hU x hx)]
    exact U.sub_mem (U.neg_mem hx) (U.smul_mem _ (hA x hx))
  · intro hS x hx
    have h1 : A *ᵥ x = (2 : F)⁻¹ • (-x - S *ᵥ x) := by
      rw [hrel x (hU x hx), sub_sub_cancel, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [h1]
    exact U.smul_mem _ (U.sub_mem (U.neg_mem hx) (hS x hx))

theorem isSimpleInvariant_iff_of_perp (h2 : (2 : F) ≠ 0)
    (hrel : ∀ x, ones n F ⬝ᵥ x = 0 → S *ᵥ x = -x - (2 : F) • (A *ᵥ x))
    {U : Submodule F (Fin n → F)} (hU : ∀ x ∈ U, ones n F ⬝ᵥ x = 0) :
    IsSimpleInvariant A U ↔ IsSimpleInvariant S U := by
  have hW : ∀ W : Submodule F (Fin n → F), W ≤ U → (IsInvariant A W ↔ IsInvariant S W) :=
    fun W hWU => isInvariant_iff_of_perp h2 hrel (fun x hx => hU x (hWU hx))
  constructor
  · rintro ⟨hinv, hne, hmin⟩
    exact ⟨(hW U le_rfl).1 hinv, hne, fun W hWinv hWU => hmin W ((hW W hWU).2 hWinv) hWU⟩
  · rintro ⟨hinv, hne, hmin⟩
    exact ⟨(hW U le_rfl).2 hinv, hne, fun W hWinv hWU => hmin W ((hW W hWU).1 hWinv) hWU⟩

end Perp

theorem modP_one (p : ℕ) : modP p (1 : Matrix (Fin n) (Fin n) ℤ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [modP]
  · simp [modP, h]

theorem isSymm_switched (G : SimpleGraph (Fin n)) (b : Fin n → Bool) : (switched G b).IsSymm := by
  have hS : (seidelOfGraph G)ᵀ = seidelOfGraph G := (isSeidel_seidelOfGraph G).1.eq
  unfold switched
  rw [IsSymm, transpose_mul, transpose_mul, signMat_transpose, hS, Matrix.mul_assoc]

theorem modP_isSymm (p : ℕ) {M : Matrix (Fin n) (Fin n) ℤ} (hM : M.IsSymm) : (modP p M).IsSymm := by
  rw [IsSymm, ← modP_transpose, hM.eq]

theorem seidel_mulVec_of_perp (p : ℕ) (G : SimpleGraph (Fin n)) {x : Fin n → ZMod p}
    (hx : ones n (ZMod p) ⬝ᵥ x = 0) :
    modP p (seidelOfGraph G) *ᵥ x = -x - (2 : ZMod p) • (modP p (adj G) *ᵥ x) := by
  classical
  have hentry : ∀ i j, modP p (seidelOfGraph G) i j =
      1 - (1 : Matrix (Fin n) (Fin n) (ZMod p)) i j - 2 * modP p (adj G) i j := by
    intro i j
    by_cases h : i = j
    · subst h
      simp [modP, seidelOfGraph, adj]
    · simp [modP, seidelOfGraph, adj, h]
  have hmat : modP p (seidelOfGraph G) =
      (Matrix.of (fun _ _ => (1 : ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) - 1 -
        (2 : ZMod p) • modP p (adj G) := by
    ext i j
    rw [hentry]
    simp
  have hJ : (Matrix.of (fun _ _ => (1 : ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ x = 0 := by
    funext i
    simpa [mulVec, dotProduct, ones] using hx
  rw [hmat, sub_mulVec, sub_mulVec, hJ, one_mulVec, smul_mulVec, zero_sub]

theorem two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h1
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h1)

theorem lem_Epswitch {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (G : SimpleGraph (Fin n))
    (b : Fin n → Bool) (d : ℕ) :
    (E p d G ↔ ∃ (U : Submodule (ZMod p) (Fin n → ZMod p)) (β : (ZMod p)[X]),
        IsSimpleInvariant (modP p (switched G b)) U ∧ HasType (modP p (switched G b)) U β ∧
          β.natDegree = d ∧ IsTotallyIsotropic U ∧ ∀ x ∈ U, modPVec p (signVec b) ⬝ᵥ x = 0) ∧
      (∀ (U : Submodule (ZMod p) (Fin n → ZMod p)) (β : (ZMod p)[X]),
        IsSimpleInvariant (modP p (switched G b)) U → HasType (modP p (switched G b)) U β →
          IsTotallyIsotropic U → IsRepeatedFactor p (switched G b) β) := by
  classical
  have hT : modP p (signMat b) * modP p (signMat b) = 1 := by
    rw [← modP_mul, signMat_mul_self, modP_one]
  have hTT : (modP p (signMat b))ᵀ * modP p (signMat b) = 1 := by
    rw [← modP_transpose, signMat_transpose, hT]
  have hS' : modP p (switched G b) =
      modP p (signMat b) * modP p (seidelOfGraph G) * modP p (signMat b) := by
    rw [switched, modP_mul, modP_mul]
  have hTS : modP p (signMat b) * modP p (seidelOfGraph G) =
      modP p (switched G b) * modP p (signMat b) := by
    rw [hS', Matrix.mul_assoc _ (modP p (signMat b)), hT, Matrix.mul_one]
  have hTS' : modP p (signMat b) * modP p (switched G b) =
      modP p (seidelOfGraph G) * modP p (signMat b) := by
    rw [hS', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hT, Matrix.one_mul]
  have hu : modP p (signMat b) *ᵥ ones n (ZMod p) = modPVec p (signVec b) := by
    funext i
    simp [modP, signMat, modPVec, mulVec, dotProduct, Matrix.diagonal_apply, ones]
  have hTu : modP p (signMat b) *ᵥ modPVec p (signVec b) = ones n (ZMod p) := by
    rw [← hu, mulVec_mulVec, hT, one_mulVec]
  have h2 := two_ne_zero_zmod hp
  have hrel : ∀ x, ones n (ZMod p) ⬝ᵥ x = 0 →
      modP p (seidelOfGraph G) *ᵥ x = -x - (2 : ZMod p) • (modP p (adj G) *ᵥ x) :=
    fun x hx => seidel_mulVec_of_perp p G hx
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨U, hU, hdim, hiso, horth⟩
    have hUS : IsSimpleInvariant (modP p (seidelOfGraph G)) U :=
      (isSimpleInvariant_iff_of_perp h2 hrel horth).1 hU
    obtain ⟨β, hβ, hβdim⟩ := exists_hasType _ U hUS
    refine ⟨U.map (modP p (signMat b)).mulVecLin, β, isSimpleInvariant_map hT hTS hUS,
      hasType_map hTS hβ, by rw [← hβdim, hdim], isTotallyIsotropic_map hTT hiso, ?_⟩
    rw [← hu]
    exact orth_map hTT horth
  · rintro ⟨V, β, hV, hβ, hdeg, hiso, horth⟩
    have horth' : ∀ x ∈ V.map (modP p (signMat b)).mulVecLin, ones n (ZMod p) ⬝ᵥ x = 0 := by
      rw [← hTu]
      exact orth_map hTT horth
    have hUS : IsSimpleInvariant (modP p (seidelOfGraph G)) (V.map (modP p (signMat b)).mulVecLin) :=
      isSimpleInvariant_map hT hTS' hV
    have hβU : HasType (modP p (seidelOfGraph G)) (V.map (modP p (signMat b)).mulVecLin) β :=
      hasType_map hTS' hβ
    obtain ⟨β', hβ', hβ'dim⟩ := exists_hasType _ _ hUS
    have hββ' := hasType_unique _ _ hUS hβ' hβU
    exact ⟨V.map (modP p (signMat b)).mulVecLin, (isSimpleInvariant_iff_of_perp h2 hrel horth').2 hUS,
      by rw [hβ'dim, hββ', hdeg], isTotallyIsotropic_map hTT hiso, horth'⟩
  · intro U β hU hβ hiso
    exact ⟨hβ.1, hβ.2.1, lem_simple_sq_dvd _ (modP_isSymm p (isSymm_switched G b)) U hU hβ hiso⟩

end DGS
