module

public import DGS.S05_Local.Disc
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

open Matrix Polynomial Module

namespace DGS

variable {n : ℕ}

section Lattices

def intVec (c : Fin n → ℤ) : Fin n → ℚ := fun i => (c i : ℚ)

theorem intVec_add (c d : Fin n → ℤ) : intVec (c + d) = intVec c + intVec d := by
  funext i; simp [intVec]

theorem intVec_smul (k : ℤ) (c : Fin n → ℤ) : intVec (k • c) = k • intVec c := by
  funext i; simp [intVec]

theorem intVec_injective : Function.Injective (intVec (n := n)) := by
  intro c d h
  funext i
  have := congrFun h i
  simp only [intVec] at this
  exact_mod_cast this

theorem mulVec_intVec (B : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℤ) :
    toQ B *ᵥ intVec c = intVec (B *ᵥ c) := by
  funext i
  simp [toQ, intVec, mulVec, dotProduct]

def latZ (n : ℕ) : Submodule ℤ (Fin n → ℚ) where
  carrier := {y | ∃ c : Fin n → ℤ, y = intVec c}
  add_mem' := by
    rintro a b ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨c + d, (intVec_add c d).symm⟩
  zero_mem' := ⟨0, by funext i; simp [intVec]⟩
  smul_mem' := by
    rintro k a ⟨c, rfl⟩
    exact ⟨k • c, (intVec_smul k c).symm⟩

theorem mem_latZ {y : Fin n → ℚ} : y ∈ latZ n ↔ ∃ c : Fin n → ℤ, y = intVec c := Iff.rfl

theorem mem_latZ_iff {y : Fin n → ℚ} : y ∈ latZ n ↔ ∀ i, ∃ k : ℤ, y i = k := by
  constructor
  · rintro ⟨c, rfl⟩ i
    exact ⟨c i, rfl⟩
  · intro h
    choose c hc using h
    exact ⟨c, funext hc⟩

def latOf (M : Matrix (Fin n) (Fin n) ℚ) : Submodule ℤ (Fin n → ℚ) :=
  (latZ n).map (M.mulVecLin.restrictScalars ℤ)

theorem mem_latOf {M : Matrix (Fin n) (Fin n) ℚ} {y : Fin n → ℚ} :
    y ∈ latOf M ↔ ∃ c : Fin n → ℤ, y = M *ᵥ intVec c := by
  constructor
  · rintro ⟨z, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨intVec c, ⟨c, rfl⟩, rfl⟩

def latC (A : Matrix (Fin n) (Fin n) ℤ) : Submodule ℤ (Fin n → ℚ) := latOf (toQ (walkMatrix A))

def latDual (L : Submodule ℤ (Fin n → ℚ)) : Submodule ℤ (Fin n → ℚ) where
  carrier := {y | ∀ z ∈ L, ∃ k : ℤ, y ⬝ᵥ z = k}
  add_mem' := by
    intro a b ha hb z hz
    obtain ⟨k, hk⟩ := ha z hz
    obtain ⟨l, hl⟩ := hb z hz
    exact ⟨k + l, by rw [add_dotProduct, hk, hl]; push_cast; ring⟩
  zero_mem' := fun z _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha z hz
    obtain ⟨k, hk⟩ := ha z hz
    exact ⟨c * k, by rw [smul_dotProduct, hk]; simp⟩

theorem mem_latDual {L : Submodule ℤ (Fin n → ℚ)} {y : Fin n → ℚ} :
    y ∈ latDual L ↔ ∀ z ∈ L, ∃ k : ℤ, y ⬝ᵥ z = k := Iff.rfl

theorem latDual_anti {L L' : Submodule ℤ (Fin n → ℚ)} (h : L ≤ L') : latDual L' ≤ latDual L :=
  fun _ hy z hz => hy z (h hz)

theorem dotProduct_intVec_intVec (c d : Fin n → ℤ) :
    intVec c ⬝ᵥ intVec d = ((c ⬝ᵥ d : ℤ) : ℚ) := by
  simp [intVec, dotProduct]

theorem mem_latDual_latOf {M : Matrix (Fin n) (Fin n) ℚ} {y : Fin n → ℚ} :
    y ∈ latDual (latOf M) ↔ Mᵀ *ᵥ y ∈ latZ n := by
  rw [mem_latZ_iff]
  constructor
  · intro h i
    obtain ⟨k, hk⟩ := h (M *ᵥ intVec (Pi.single i 1)) (mem_latOf.2 ⟨_, rfl⟩)
    refine ⟨k, ?_⟩
    rw [← hk, dotProduct_mulVec, ← mulVec_transpose]
    simp [dotProduct, intVec, Pi.single_apply]
  · intro h z hz
    obtain ⟨c, rfl⟩ := mem_latOf.1 hz
    obtain ⟨d, hd⟩ := mem_latZ_iff.2 h
    refine ⟨d ⬝ᵥ c, ?_⟩
    rw [dotProduct_mulVec, ← mulVec_transpose, hd, dotProduct_intVec_intVec]

theorem latDual_latZ : latDual (latZ n) = latZ n := by
  ext y
  constructor
  · intro h
    rw [mem_latZ_iff]
    intro i
    obtain ⟨k, hk⟩ := h (intVec (Pi.single i 1)) ⟨_, rfl⟩
    exact ⟨k, by rw [← hk]; simp [dotProduct, intVec, Pi.single_apply]⟩
  · rintro ⟨c, rfl⟩ z ⟨d, rfl⟩
    exact ⟨c ⬝ᵥ d, dotProduct_intVec_intVec c d⟩

end Lattices

section IotaQ

variable (A : Matrix (Fin n) (Fin n) ℤ)

noncomputable def iotaQ (u : ℚ[X]) : Fin n → ℚ := aeval (toQ A) u *ᵥ ones n ℚ

theorem iotaQ_add (u v : ℚ[X]) : iotaQ A (u + v) = iotaQ A u + iotaQ A v := by
  simp [iotaQ, map_add, add_mulVec]

theorem iotaQ_sub (u v : ℚ[X]) : iotaQ A (u - v) = iotaQ A u - iotaQ A v := by
  simp [iotaQ, map_sub, sub_mulVec]

theorem iotaQ_mul (g u : ℚ[X]) : iotaQ A (g * u) = aeval (toQ A) g *ᵥ iotaQ A u := by
  simp [iotaQ, map_mul, mulVec_mulVec]

theorem iotaQ_smul (k : ℤ) (u : ℚ[X]) : iotaQ A (k • u) = k • iotaQ A u := by
  rw [iotaQ, iotaQ, map_zsmul, smul_mulVec]

theorem toQ_charpoly : (toQ A).charpoly = A.charpoly.map (Int.castRingHom ℚ) :=
  charpoly_map A (Int.castRingHom ℚ)

theorem toQ_psiPoly : psiPoly (toQ A) = (psiPoly A).map (Int.castRingHom ℚ) :=
  psiPoly_map A (Int.castRingHom ℚ)

theorem toQ_walkMatrix : toQ (walkMatrix A) = walkMatrix (toQ A) :=
  walkMatrix_map A (Int.castRingHom ℚ)

theorem det_toQ (B : Matrix (Fin n) (Fin n) ℤ) : (toQ B).det = (B.det : ℚ) :=
  ((Int.castRingHom ℚ).map_det B).symm

theorem toQ_isSymm {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) : (toQ A).IsSymm := hA.map _

theorem iotaQ_eq_walk (hn : 1 ≤ n) (u : ℚ[X]) :
    iotaQ A u = toQ (walkMatrix A) *ᵥ (fun j => (u %ₘ (toQ A).charpoly).coeff j) := by
  rw [iotaQ, aeval_mulVec_ones_eq (toQ A) hn u, toQ_walkMatrix]

variable {A}

theorem iotaQ_eq_zero_iff (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) (u : ℚ[X]) :
    iotaQ A u = 0 ↔ (toQ A).charpoly ∣ u := by
  have hWq : (toQ (walkMatrix A)).det ≠ 0 := by
    rw [det_toQ]; exact_mod_cast hW
  rw [← modByMonic_eq_zero_iff_dvd (charpoly_monic _), iotaQ_eq_walk A hn]
  constructor
  · intro h
    have h0 := eq_zero_of_mulVec_eq_zero hWq h
    have hdeg := natDegree_modByMonic_charpoly_lt (toQ A) hn u
    ext j
    rw [coeff_zero]
    by_cases hj : j < n
    · exact congrFun h0 ⟨j, hj⟩
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  · intro h
    rw [h]
    have : (fun j : Fin n => (0 : ℚ[X]).coeff j) = 0 := by funext j; simp
    rw [this, mulVec_zero]

theorem iotaQ_eq_iff (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) (u v : ℚ[X]) :
    iotaQ A u = iotaQ A v ↔ (toQ A).charpoly ∣ u - v := by
  rw [← iotaQ_eq_zero_iff hn hW, iotaQ_sub, sub_eq_zero]

theorem iotaQ_surjective (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) (y : Fin n → ℚ) :
    ∃ u : ℚ[X], u.natDegree < n ∧ iotaQ A u = y := by
  have hWq : IsUnit (toQ (walkMatrix A)).det := by
    rw [det_toQ, isUnit_iff_ne_zero]; exact_mod_cast hW
  set c : Fin n → ℚ := (toQ (walkMatrix A))⁻¹ *ᵥ y
  set u : ℚ[X] := ((degreeLTEquiv ℚ n).symm c : ℚ[X])
  have hu : u ∈ degreeLT ℚ n := ((degreeLTEquiv ℚ n).symm c).2
  have hcoeff : ∀ j : Fin n, u.coeff j = c j := by
    intro j
    have := congrFun ((degreeLTEquiv ℚ n).apply_symm_apply c) j
    rw [← this]
    rfl
  have hdeg : u.natDegree < n := by
    rw [mem_degreeLT] at hu
    by_cases h0 : u = 0
    · rw [h0, natDegree_zero]; omega
    · rw [degree_eq_natDegree h0] at hu; exact_mod_cast hu
  refine ⟨u, hdeg, ?_⟩
  rw [iotaQ, aeval_mulVec_ones_of_natDegree_lt (toQ A) hdeg, ← toQ_walkMatrix]
  have : (fun j : Fin n => u.coeff j) = c := funext hcoeff
  rw [this, mulVec_mulVec, mul_nonsing_inv _ hWq, one_mulVec]

theorem mem_latC_iff (hn : 1 ≤ n) {y : Fin n → ℚ} :
    y ∈ latC A ↔ ∃ g : ℤ[X], y = iotaQ A (g.map (Int.castRingHom ℚ)) := by
  rw [latC, mem_latOf]
  constructor
  · rintro ⟨c, rfl⟩
    set g : ℤ[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)
    have hcoeff : ∀ j : Fin n, (g.map (Int.castRingHom ℚ)).coeff j = intVec c j := by
      intro j
      rw [coeff_map, finsetSum_coeff]
      rw [Finset.sum_eq_single j]
      · simp [intVec]
      · intro b _ hb
        rw [coeff_monomial, ite_eq_right (fun h => hb (Fin.ext h))]
      · simp
    have hdeg : (g.map (Int.castRingHom ℚ)).natDegree < n := by
      refine lt_of_le_of_lt (natDegree_map_le) ?_
      have h1 : g.natDegree ≤ n - 1 := by
        refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
        refine (natDegree_monomial_le _).trans ?_
        omega
      omega
    refine ⟨g, ?_⟩
    rw [iotaQ, aeval_mulVec_ones_of_natDegree_lt (toQ A) hdeg, ← toQ_walkMatrix]
    congr 1
    exact (funext hcoeff).symm
  · rintro ⟨g, rfl⟩
    refine ⟨fun j => (g %ₘ A.charpoly).coeff j, ?_⟩
    rw [iotaQ_eq_walk A hn, toQ_charpoly, ← map_modByMonic _ (charpoly_monic A)]
    congr 1
    funext j
    simp [intVec, coeff_map]

theorem mem_latDual_latC_iff (hn : 1 ≤ n) {y : Fin n → ℚ} :
    y ∈ latDual (latC A) ↔ ∀ g : ℤ[X], ∃ k : ℤ, y ⬝ᵥ iotaQ A (g.map (Int.castRingHom ℚ)) = k := by
  constructor
  · intro h g
    exact h _ ((mem_latC_iff hn).2 ⟨g, rfl⟩)
  · intro h z hz
    obtain ⟨g, rfl⟩ := (mem_latC_iff hn).1 hz
    exact h g

end IotaQ

section TauMod

variable {K : Type*} [Field K]

theorem tauF_charpoly_mul (A : Matrix (Fin n) (Fin n) K) (g : K[X]) :
    tauF A (A.charpoly * g) = 0 := by
  rw [tauF, (modByMonic_eq_zero_iff_dvd (charpoly_monic A)).2 (dvd_mul_right _ _), coeff_zero]

theorem tauF_eq_of_dvd_sub (A : Matrix (Fin n) (Fin n) K) {u v : K[X]} (h : A.charpoly ∣ u - v) :
    tauF A u = tauF A v := by
  rw [tauF, tauF, modByMonic_eq_of_dvd_sub (charpoly_monic A) h]

theorem tauF_int (A : Matrix (Fin n) (Fin n) ℤ) (r : ℤ[X]) :
    tauF (toQ A) (r.map (Int.castRingHom ℚ)) = ((tauF A r : ℤ) : ℚ) :=
  tauF_map A (Int.castRingHom ℚ) r

end TauMod

section PsiInv

variable {A : Matrix (Fin n) (Fin n) ℤ}

theorem isCoprime_psiPoly (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) :
    IsCoprime (psiPoly (toQ A)) (toQ A).charpoly := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff]
  by_contra hu
  set φ := (toQ A).charpoly with hφdef
  set ψ := psiPoly (toQ A)
  set d := EuclideanDomain.gcd ψ φ
  obtain ⟨f, hf⟩ : d ∣ φ := EuclideanDomain.gcd_dvd_right ψ φ
  obtain ⟨g, hg⟩ : d ∣ ψ := EuclideanDomain.gcd_dvd_left ψ φ
  have hφ0 : φ ≠ 0 := (charpoly_monic _).ne_zero
  have hφdeg : φ.natDegree = n := by rw [hφdef, charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hd0 : d ≠ 0 := by
    intro h; apply hφ0; rw [hf, h, zero_mul]
  have hf0 : f ≠ 0 := by
    intro h; apply hφ0; rw [hf, h, mul_zero]
  have hddeg : 0 < d.natDegree := by
    by_contra h
    push Not at h
    apply hu
    rw [isUnit_iff_degree_eq_zero, degree_eq_natDegree hd0]
    exact_mod_cast Nat.le_zero.1 h
  have hfdeg : f.natDegree < n := by
    have := congrArg natDegree hf
    rw [natDegree_mul hd0 hf0, hφdeg] at this
    omega
  have hdiv : φ ∣ f * f * ψ := ⟨f * g, by linear_combination (f * f) * hg - (f * g) * hf⟩
  have h1 : iotaQ A f ⬝ᵥ iotaQ A f = 0 := by
    rw [iotaQ, lem_form (toQ A) (toQ_isSymm hA) hn f f, tauF,
      (modByMonic_eq_zero_iff_dvd (charpoly_monic _)).2 hdiv, coeff_zero]
  have h2 : iotaQ A f = 0 := dotProduct_self_eq_zero.1 h1
  rw [iotaQ_eq_zero_iff hn hW] at h2
  have := natDegree_le_of_dvd h2 hf0
  rw [hφdeg] at this
  omega

open Classical in
noncomputable def psiInv (A : Matrix (Fin n) (Fin n) ℤ) : ℚ[X] :=
  if h : IsCoprime (psiPoly (toQ A)) (toQ A).charpoly then h.choose else 0

theorem psiInv_spec (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) :
    ∃ b : ℚ[X], psiInv A * psiPoly (toQ A) + b * (toQ A).charpoly = 1 := by
  have h := isCoprime_psiPoly hA hn hW
  rw [psiInv, dite_eq_left h]
  exact h.choose_spec

theorem charpoly_dvd_psiInv_mul_sub_one (hA : A.IsSymm) (hn : 1 ≤ n)
    (hW : (walkMatrix A).det ≠ 0) (u : ℚ[X]) :
    (toQ A).charpoly ∣ u * psiInv A * psiPoly (toQ A) - u := by
  obtain ⟨b, hb⟩ := psiInv_spec hA hn hW
  refine ⟨-(u * b), ?_⟩
  have : u * psiInv A * psiPoly (toQ A) - u = u * (psiInv A * psiPoly (toQ A) + b * (toQ A).charpoly)
      - u - u * b * (toQ A).charpoly := by ring
  rw [this, hb]
  ring

end PsiInv

section PropD

variable (A : Matrix (Fin n) (Fin n) ℤ)

noncomputable def PhiHat (f : ℤ[X]) : Fin n → ℚ :=
  iotaQ A (f.map (Int.castRingHom ℚ) * psiInv A)

theorem PhiHat_add (f g : ℤ[X]) : PhiHat A (f + g) = PhiHat A f + PhiHat A g := by
  rw [PhiHat, PhiHat, PhiHat, Polynomial.map_add, add_mul, iotaQ_add]

theorem PhiHat_smul (k : ℤ) (f : ℤ[X]) : PhiHat A (k • f) = k • PhiHat A f := by
  rw [PhiHat, PhiHat, Polynomial.map_smul, smul_mul_assoc]
  have : (Int.castRingHom ℚ) k • (f.map (Int.castRingHom ℚ) * psiInv A) =
      k • (f.map (Int.castRingHom ℚ) * psiInv A) := by
    rw [eq_intCast]; exact Int.cast_smul_eq_zsmul ℚ k _
  rw [this, iotaQ_smul]

theorem PhiHat_mul (g f : ℤ[X]) :
    PhiHat A (g * f) = aeval (toQ A) (g.map (Int.castRingHom ℚ)) *ᵥ PhiHat A f := by
  rw [PhiHat, PhiHat, Polynomial.map_mul, mul_assoc, iotaQ_mul]

theorem PhiHat_X_mul (f : ℤ[X]) : PhiHat A (X * f) = toQ A *ᵥ PhiHat A f := by
  rw [PhiHat_mul, Polynomial.map_X, aeval_X]

variable {A}

theorem mem_latDual_latC_iff_PhiHat (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0)
    (y : Fin n → ℚ) : y ∈ latDual (latC A) ↔ ∃ f : ℤ[X], y = PhiHat A f := by
  have hAq := toQ_isSymm hA
  rw [mem_latDual_latC_iff hn]
  constructor
  · intro h
    obtain ⟨u, -, rfl⟩ := iotaQ_surjective hn hW y
    obtain ⟨r, hrdeg, q, hq⟩ : ∃ r : ℚ[X], r.natDegree < n ∧ ∃ q : ℚ[X],
        u * psiPoly (toQ A) - r = (toQ A).charpoly * q := by
      refine ⟨(u * psiPoly (toQ A)) %ₘ (toQ A).charpoly,
        natDegree_modByMonic_charpoly_lt _ hn _, (u * psiPoly (toQ A)) /ₘ (toQ A).charpoly, ?_⟩
      have := modByMonic_add_div (u * psiPoly (toQ A)) (toQ A).charpoly
      linear_combination -this
    have hint : ∀ j < n, ∃ k : ℤ, tauF (A.map (Int.castRingHom ℚ)) (X ^ j * r) = k := by
      intro j _
      obtain ⟨k, hk⟩ := h (X ^ j)
      refine ⟨k, ?_⟩
      rw [← hk, iotaQ, iotaQ, lem_form (toQ A) hAq hn]
      refine tauF_eq_of_dvd_sub (toQ A) ?_
      rw [Polynomial.map_pow, Polynomial.map_X]
      exact ⟨-(X ^ j * q), by linear_combination (-(X ^ j)) * hq⟩
    have hcoeff := coeff_int_of_tauF_int A hn hrdeg hint
    have hlift : r ∈ lifts (Int.castRingHom ℚ) := by
      rw [lifts_iff_coeff_lifts]
      intro i
      obtain ⟨k, hk⟩ := hcoeff i
      exact ⟨k, by rw [hk]; rfl⟩
    obtain ⟨f, hf⟩ := (mem_lifts r).1 hlift
    refine ⟨f, ?_⟩
    rw [PhiHat, hf, iotaQ_eq_iff hn hW]
    obtain ⟨q1, hq1⟩ := charpoly_dvd_psiInv_mul_sub_one hA hn hW u
    exact ⟨q * psiInv A - q1, by linear_combination hq * psiInv A - hq1⟩
  · rintro ⟨f, rfl⟩ g
    refine ⟨tauF A (f * g), ?_⟩
    rw [PhiHat, iotaQ, iotaQ, lem_form (toQ A) hAq hn, ← tauF_int A]
    refine tauF_eq_of_dvd_sub (toQ A) ?_
    obtain ⟨q, hq⟩ := charpoly_dvd_psiInv_mul_sub_one hA hn hW
      (f.map (Int.castRingHom ℚ) * g.map (Int.castRingHom ℚ))
    rw [Polynomial.map_mul]
    exact ⟨q, by linear_combination hq⟩

theorem PhiHat_mem_latC_iff (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0)
    (f : ℤ[X]) : PhiHat A f ∈ latC A ↔ f ∈ Ideal.span {A.charpoly, psiPoly A} := by
  rw [mem_latC_iff hn, Ideal.mem_span_pair]
  constructor
  · rintro ⟨g, hg⟩
    rw [PhiHat, iotaQ_eq_iff hn hW] at hg
    have h2 : (toQ A).charpoly ∣ (f - g * psiPoly A).map (Int.castRingHom ℚ) := by
      obtain ⟨q1, hq1⟩ := hg
      obtain ⟨q2, hq2⟩ := charpoly_dvd_psiInv_mul_sub_one hA hn hW (f.map (Int.castRingHom ℚ))
      refine ⟨q1 * psiPoly (toQ A) - q2, ?_⟩
      rw [Polynomial.map_sub, Polynomial.map_mul, ← toQ_psiPoly]
      linear_combination hq1 * psiPoly (toQ A) - hq2
    rw [toQ_charpoly, Polynomial.map_dvd_map _ (Int.castRingHom ℚ).injective_int
      (charpoly_monic A)] at h2
    obtain ⟨q, hq⟩ := h2
    exact ⟨q, g, by linear_combination -hq⟩
  · rintro ⟨c, d, hcd⟩
    refine ⟨d, ?_⟩
    rw [PhiHat, iotaQ_eq_iff hn hW, ← hcd, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_mul, ← toQ_charpoly, ← toQ_psiPoly]
    obtain ⟨q, hq⟩ := charpoly_dvd_psiInv_mul_sub_one hA hn hW (d.map (Int.castRingHom ℚ))
    exact ⟨c.map (Int.castRingHom ℚ) * psiInv A + q, by linear_combination hq⟩

end PropD

section Quotients

variable (A : Matrix (Fin n) (Fin n) ℤ)

noncomputable def idealT : Ideal ℤ[X] := Ideal.span {A.charpoly, psiPoly A}

abbrev TT := ℤ[X] ⧸ idealT A

def latCinDual : Submodule ℤ (latDual (latC A)) := (latC A).comap (latDual (latC A)).subtype

abbrev DD := ↥(latDual (latC A)) ⧸ latCinDual A

variable {A}

noncomputable def PhiLin (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) :
    ℤ[X] →ₗ[ℤ] latDual (latC A) where
  toFun f := ⟨PhiHat A f, (mem_latDual_latC_iff_PhiHat hA hn hW _).2 ⟨f, rfl⟩⟩
  map_add' f g := Subtype.ext (PhiHat_add A f g)
  map_smul' k f := Subtype.ext (PhiHat_smul A k f)

theorem PhiLin_comp_surjective (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) :
    Function.Surjective ((latCinDual A).mkQ ∘ₗ PhiLin hA hn hW) := by
  intro d
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ d
  obtain ⟨f, rfl⟩ := (mem_latDual_latC_iff_PhiHat hA hn hW y).1 hy
  exact ⟨f, rfl⟩

theorem ker_PhiLin_comp (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) :
    LinearMap.ker ((latCinDual A).mkQ ∘ₗ PhiLin hA hn hW) = (idealT A).restrictScalars ℤ := by
  ext f
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.restrictScalars_mem, latCinDual, Submodule.mem_comap, Submodule.subtype_apply]
  exact PhiHat_mem_latC_iff hA hn hW f

noncomputable def TTequivDD (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) :
    TT A ≃+ DD A :=
  (((Submodule.Quotient.restrictScalarsEquiv ℤ (idealT A)).symm.trans
    (Submodule.quotEquivOfEq _ _ (ker_PhiLin_comp hA hn hW).symm)).trans
    (LinearMap.quotKerEquivOfSurjective _ (PhiLin_comp_surjective hA hn hW))).toAddEquiv

theorem TTequivDD_mk (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) (f : ℤ[X]) :
    TTequivDD hA hn hW (Ideal.Quotient.mk _ f) = Submodule.Quotient.mk (PhiLin hA hn hW f) :=
  rfl

theorem TTequivDD_X_mul (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) (f : ℤ[X]) :
    ((PhiLin hA hn hW (X * f) : latDual (latC A)) : Fin n → ℚ) =
      toQ A *ᵥ (PhiLin hA hn hW f : Fin n → ℚ) :=
  PhiHat_X_mul A f

theorem card_quotient_range_mulVecLin (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.det ≠ 0) :
    Nat.card ((Fin n → ℤ) ⧸ LinearMap.range G.mulVecLin) = G.det.natAbs := by
  have hinj : Function.Injective G.mulVecLin := by
    intro c d h
    have h1 : G *ᵥ (c - d) = 0 := by
      rw [mulVec_sub]; exact sub_eq_zero.2 h
    exact sub_eq_zero.1 (eq_zero_of_mulVec_eq_zero hG h1)
  let e := LinearEquiv.ofInjective G.mulVecLin hinj
  rw [← Submodule.natAbs_det_equiv (LinearMap.range G.mulVecLin) e]
  have : (LinearMap.range G.mulVecLin).subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : _ →+ _) =
      Matrix.toLin' G := by
    ext x : 1
    rfl
  rw [this, LinearMap.det_toLin']

theorem card_DD (_hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) :
    Nat.card (DD A) = (walkMatrix A).det.natAbs ^ 2 := by
  set Wq := toQ (walkMatrix A)
  have hWq : IsUnit Wq.det := by
    rw [det_toQ, isUnit_iff_ne_zero]; exact_mod_cast hW
  have hWqT : IsUnit Wqᵀ.det := by rwa [det_transpose]
  set G : Matrix (Fin n) (Fin n) ℤ := (walkMatrix A)ᵀ * walkMatrix A
  have hG : G.det ≠ 0 := by
    rw [det_mul, det_transpose]; exact mul_ne_zero hW hW
  have htoQG : toQ G = Wqᵀ * Wq := by
    simp only [G, Wq, toQ, Matrix.map_mul, Matrix.transpose_map]
  have hmem : ∀ c : Fin n → ℤ, Wqᵀ⁻¹ *ᵥ intVec c ∈ latDual (latC A) := by
    intro c
    show Wqᵀ⁻¹ *ᵥ intVec c ∈ latDual (latOf Wq)
    rw [mem_latDual_latOf, mulVec_mulVec, mul_nonsing_inv _ hWqT, one_mulVec]
    exact ⟨c, rfl⟩
  let e0 : (Fin n → ℤ) →ₗ[ℤ] latDual (latC A) :=
    { toFun := fun c => ⟨Wqᵀ⁻¹ *ᵥ intVec c, hmem c⟩
      map_add' := fun c d => Subtype.ext (by
        change Wqᵀ⁻¹ *ᵥ intVec (c + d) = Wqᵀ⁻¹ *ᵥ intVec c + Wqᵀ⁻¹ *ᵥ intVec d
        rw [intVec_add, mulVec_add])
      map_smul' := fun k c => Subtype.ext (by
        change Wqᵀ⁻¹ *ᵥ intVec (k • c) = k • (Wqᵀ⁻¹ *ᵥ intVec c)
        rw [intVec_smul, mulVec_smul]) }
  have he0 : ∀ c, (e0 c : Fin n → ℚ) = Wqᵀ⁻¹ *ᵥ intVec c := fun c => rfl
  have hbij : Function.Bijective e0 := by
    constructor
    · intro c d h
      have h1 := congrArg (fun y : latDual (latC A) => Wqᵀ *ᵥ (y : Fin n → ℚ)) h
      simp only [he0, mulVec_mulVec, mul_nonsing_inv _ hWqT, one_mulVec] at h1
      exact intVec_injective h1
    · rintro ⟨y, hy⟩
      change y ∈ latDual (latOf Wq) at hy
      rw [mem_latDual_latOf] at hy
      obtain ⟨c, hc⟩ := hy
      refine ⟨c, Subtype.ext ?_⟩
      rw [he0, ← hc, mulVec_mulVec, nonsing_inv_mul _ hWqT, one_mulVec]
  let e := LinearEquiv.ofBijective e0 hbij
  have he : ∀ c, ((e c : latDual (latC A)) : Fin n → ℚ) = Wqᵀ⁻¹ *ᵥ intVec c := fun c => rfl
  have hkey : ∀ d : Fin n → ℤ, Wqᵀ⁻¹ *ᵥ intVec (G *ᵥ d) = Wq *ᵥ intVec d := by
    intro d
    rw [← mulVec_intVec, htoQG, mulVec_mulVec, ← mul_assoc, nonsing_inv_mul _ hWqT, one_mul]
  have hmap : (LinearMap.range G.mulVecLin).map (e : (Fin n → ℤ) →ₗ[ℤ] latDual (latC A)) =
      latCinDual A := by
    ext ⟨y, hy⟩
    rw [Submodule.mem_map, latCinDual, Submodule.mem_comap, Submodule.subtype_apply]
    change _ ↔ y ∈ latOf Wq
    rw [mem_latOf]
    constructor
    · rintro ⟨c, ⟨d, rfl⟩, hcd⟩
      refine ⟨d, ?_⟩
      have := congrArg Subtype.val hcd
      rw [LinearEquiv.coe_coe, he, Matrix.mulVecLin_apply, hkey] at this
      exact this.symm
    · rintro ⟨d, hd⟩
      refine ⟨G *ᵥ d, ⟨d, rfl⟩, Subtype.ext ?_⟩
      rw [LinearEquiv.coe_coe, he, hkey]
      exact hd.symm
  have hq := Submodule.Quotient.equiv _ _ e hmap
  rw [← Nat.card_congr hq.toEquiv, card_quotient_range_mulVecLin G hG]
  simp only [G, det_mul, det_transpose, Int.natAbs_mul, sq]

theorem card_TT (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) :
    Nat.card (TT A) = (walkMatrix A).det.natAbs ^ 2 := by
  rw [Nat.card_congr (TTequivDD hA hn hW).toEquiv, card_DD hn hW]

end Quotients

section Mates

def IsMateMatrix (A : Matrix (Fin n) (Fin n) ℤ) (Q : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  Qᵀ * Q = 1 ∧ Q *ᵥ ones n ℚ = ones n ℚ ∧ ∃ B : Matrix (Fin n) (Fin n) ℤ, Qᵀ * toQ A * Q = toQ B

theorem isMateMatrix_of_mem_QG {G : SimpleGraph (Fin n)} {Q : Matrix (Fin n) (Fin n) ℚ}
    (hQ : Q ∈ QG G) : IsMateMatrix (adj G) Q := by
  obtain ⟨h1, h2, H, h3⟩ := hQ
  exact ⟨h1, h2, adj H, h3⟩

theorem isMateMatrix_one (A : Matrix (Fin n) (Fin n) ℤ) : IsMateMatrix A 1 :=
  ⟨by simp, one_mulVec _, A, by simp⟩

theorem adj_isSymm (G : SimpleGraph (Fin n)) : (adj G).IsSymm := by
  classical
  exact SimpleGraph.isSymm_adjMatrix (α := ℤ) G

def IsAStable (A : Matrix (Fin n) (Fin n) ℤ) (L : Submodule ℤ (Fin n → ℚ)) : Prop :=
  ∀ y ∈ L, toQ A *ᵥ y ∈ L

variable {A : Matrix (Fin n) (Fin n) ℤ}

theorem pow_mulVec_mem {L : Submodule ℤ (Fin n → ℚ)} (hL : IsAStable A L) (k : ℕ) {y : Fin n → ℚ}
    (hy : y ∈ L) : (toQ A) ^ k *ᵥ y ∈ L := by
  induction k with
  | zero => rw [pow_zero, one_mulVec]; exact hy
  | succ k ih => rw [pow_succ', ← mulVec_mulVec]; exact hL _ ih

theorem aeval_mulVec_mem {L : Submodule ℤ (Fin n → ℚ)} (hL : IsAStable A L) (g : ℤ[X])
    {y : Fin n → ℚ} (hy : y ∈ L) : aeval (toQ A) (g.map (Int.castRingHom ℚ)) *ᵥ y ∈ L := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, add_mulVec]; exact L.add_mem hp hq
  | monomial k a =>
    rw [Polynomial.map_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, smul_mulVec, eq_intCast, Int.cast_smul_eq_zsmul ℚ]
    exact L.smul_mem a (pow_mulVec_mem hL k hy)

theorem mem_latOf_ones {Q : Matrix (Fin n) (Fin n) ℚ} (hQe : Q *ᵥ ones n ℚ = ones n ℚ) :
    ones n ℚ ∈ latOf Q :=
  mem_latOf.2 ⟨fun _ => 1, by
    have : intVec (fun _ : Fin n => (1 : ℤ)) = ones n ℚ := by funext i; simp [intVec, ones]
    rw [this, hQe]⟩

theorem latOf_one : latOf (1 : Matrix (Fin n) (Fin n) ℚ) = latZ n := by
  ext y
  rw [mem_latOf, mem_latZ]
  simp only [one_mulVec]

theorem lem_ideals (hn : 1 ≤ n) {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : IsMateMatrix A Q) :
    IsAStable A (latOf Q) ∧ latDual (latOf Q) = latOf Q ∧ latC A ≤ latOf Q ∧
      latOf Q ≤ latDual (latC A) := by
  obtain ⟨hQQ, hQe, B, hB⟩ := hQ
  have hQQ' : Q * Qᵀ = 1 := mul_eq_one_comm.1 hQQ
  have hAQ : toQ A * Q = Q * toQ B := by
    rw [← hB, ← mul_assoc, ← mul_assoc, hQQ', one_mul]
  have hstab : IsAStable A (latOf Q) := by
    intro y hy
    obtain ⟨c, rfl⟩ := mem_latOf.1 hy
    refine mem_latOf.2 ⟨B *ᵥ c, ?_⟩
    rw [mulVec_mulVec, hAQ, ← mulVec_mulVec, mulVec_intVec]
  have hdual : latDual (latOf Q) = latOf Q := by
    ext y
    rw [mem_latDual_latOf, mem_latZ, mem_latOf]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← hc, mulVec_mulVec, hQQ', one_mulVec]
    · rintro ⟨c, rfl⟩
      refine ⟨c, ?_⟩
      rw [mulVec_mulVec, hQQ, one_mulVec]
  have hC : latC A ≤ latOf Q := by
    intro y hy
    obtain ⟨g, rfl⟩ := (mem_latC_iff hn).1 hy
    exact aeval_mulVec_mem hstab g (mem_latOf_ones hQe)
  refine ⟨hstab, hdual, hC, ?_⟩
  rw [← hdual]
  exact latDual_anti hC

end Mates

end DGS
