module

public import DGS.Core.Basic
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Polynomial.RationalRoot

@[expose] public section

open Matrix Finset Polynomial

namespace DGS

section Gram

variable {r c : Type*} [Fintype r] [Fintype c] [DecidableEq c]

theorem det_gram_ne_zero (A : Matrix r c ℤ)
    (hA : ∀ a : c → ℚ, A.map (Int.castRingHom ℚ) *ᵥ a = 0 → a = 0) : (Aᵀ * A).det ≠ 0 := by
  intro h0
  set Aq := A.map (Int.castRingHom ℚ) with hAq
  have h1 : (Aqᵀ * Aq).det = 0 := by
    have h2 : Aqᵀ * Aq = (Aᵀ * A).map (Int.castRingHom ℚ) := by
      rw [Matrix.map_mul, Matrix.transpose_map]
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h1
  apply ha0
  apply hA
  rw [← Matrix.mulVec_mulVec] at ha
  have h3 : (Aq *ᵥ a) ⬝ᵥ (Aq *ᵥ a) = 0 := by
    have h4 := congrArg (fun v => a ⬝ᵥ v) ha
    simp only [dotProduct_zero] at h4
    rwa [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at h4
  exact dotProduct_self_eq_zero.1 h3

theorem eq_zero_of_gram_det {F : Type*} [Field F] (A : Matrix r c ℤ) (φ : ℤ →+* F)
    (hdet : φ (Aᵀ * A).det ≠ 0) {a : c → F} (ha : A.map φ *ᵥ a = 0) : a = 0 := by
  have h1 : (Aᵀ * A).map φ *ᵥ a = 0 := by
    rw [Matrix.map_mul, Matrix.transpose_map, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_zero]
  by_contra hne
  apply hdet
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  exact Matrix.exists_mulVec_eq_zero_iff.1 ⟨a, hne, h1⟩

theorem intCast_zmod_ne_zero {p : ℕ} {z : ℤ} (hz : z ≠ 0) (hzp : |z| < p) : (z : ZMod p) ≠ 0 := by
  intro h
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).1 h
  have h1 := Int.le_of_dvd (abs_pos.2 hz) ((dvd_abs _ _).2 hdvd)
  linarith

end Gram

section Bounds

theorem abs_mul_apply_le_pow {l n k : Type*} [Fintype k] {A : Matrix l k ℤ} {B : Matrix k n ℤ}
    {m e₁ e₂ e₃ e : ℕ} (hm : 1 ≤ m) (hk : Fintype.card k ≤ m ^ e₃) (hA : ∀ i j, |A i j| ≤ (m : ℤ) ^ e₁)
    (hB : ∀ i j, |B i j| ≤ (m : ℤ) ^ e₂) (he : e₁ + e₂ + e₃ ≤ e) (i : l) (j : n) :
    |(A * B) i j| ≤ (m : ℤ) ^ e := by
  rw [Matrix.mul_apply]
  have hk' : (Fintype.card k : ℤ) ≤ (m : ℤ) ^ e₃ := by exact_mod_cast hk
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  calc |∑ x, A i x * B x j| ≤ ∑ x, |A i x * B x j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : k, (m : ℤ) ^ e₁ * (m : ℤ) ^ e₂ := sum_le_sum fun x _ => by
        rw [abs_mul]
        exact mul_le_mul (hA i x) (hB x j) (abs_nonneg _) (by positivity)
    _ = Fintype.card k * ((m : ℤ) ^ e₁ * (m : ℤ) ^ e₂) := by rw [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ (m : ℤ) ^ e₃ * ((m : ℤ) ^ e₁ * (m : ℤ) ^ e₂) := by gcongr
    _ = (m : ℤ) ^ (e₁ + e₂ + e₃) := by ring
    _ ≤ (m : ℤ) ^ e := pow_le_pow_right₀ hm' he

theorem abs_pow_apply_le {m : ℕ} (hm : 1 ≤ m) {T : Matrix (Fin m) (Fin m) ℤ} (hT : ∀ i j, |T i j| ≤ 1)
    (k : ℕ) (i j : Fin m) : |(T ^ k) i j| ≤ (m : ℤ) ^ k := by
  induction k generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ]
    exact abs_mul_apply_le_pow (e₁ := k) (e₂ := 0) (e₃ := 1) hm (by simp) ih
      (fun i j => by simpa using hT i j) (by omega) i j

theorem abs_det_le_pow {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℤ} {m e : ℕ}
    (hn : Fintype.card n ≤ m) (hA : ∀ i j, |A i j| ≤ (m : ℤ) ^ e) :
    |A.det| ≤ (m : ℤ) ^ (Fintype.card n * (e + 1)) := by
  have h : |A.det| ≤ (Fintype.card n).factorial • ((m : ℤ) ^ e) ^ Fintype.card n :=
    Matrix.det_le (abv := AbsoluteValue.abs) (fun i j => hA i j)
  rw [nsmul_eq_mul] at h
  refine h.trans ?_
  have h1 : ((Fintype.card n).factorial : ℤ) ≤ (m : ℤ) ^ Fintype.card n := by
    exact_mod_cast (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hn _)
  calc ((Fintype.card n).factorial : ℤ) * ((m : ℤ) ^ e) ^ Fintype.card n
      ≤ (m : ℤ) ^ Fintype.card n * ((m : ℤ) ^ e) ^ Fintype.card n := by gcongr
    _ = (m : ℤ) ^ (Fintype.card n * (e + 1)) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring

theorem abs_adjugate_apply_le_pow {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℤ} {m e : ℕ}
    (hm : 1 ≤ m) (hn : Fintype.card n ≤ m) (hA : ∀ i j, |A i j| ≤ (m : ℤ) ^ e) (i j : n) :
    |A.adjugate i j| ≤ (m : ℤ) ^ (Fintype.card n * (e + 1)) := by
  rw [Matrix.adjugate_apply]
  refine abs_det_le_pow hn fun k l => ?_
  rw [Matrix.updateRow_apply]
  have h1 : (1 : ℤ) ≤ (m : ℤ) ^ e := one_le_pow₀ (by exact_mod_cast hm)
  split_ifs with h
  · rcases eq_or_ne l i with rfl | hli
    · simpa using h1
    · rw [Pi.single_eq_of_ne hli]
      simp only [abs_zero]
      positivity
  · exact hA k l

end Bounds

section Krylov

variable {F : Type*} [Field F] {m : ℕ}

def krySpanLe (T : Matrix (Fin m) (Fin m) F) (y : Fin m → F) (j : ℕ) : Submodule F (Fin m → F) :=
  Submodule.span F ((fun i => (T ^ i) *ᵥ y) '' ↑(Finset.range (j + 1)))

theorem krySpanLe_succ (T : Matrix (Fin m) (Fin m) F) (y : Fin m → F) (j : ℕ) :
    krySpanLe T y (j + 1) = krySpanLe T y j ⊔ Submodule.span F {(T ^ (j + 1)) *ᵥ y} := by
  unfold krySpanLe
  rw [Finset.range_add_one (n := j + 1), Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert, sup_comm]

theorem pow_mulVec_mem_krySpanLe (T : Matrix (Fin m) (Fin m) F) (y : Fin m → F) {i j : ℕ} (hij : i ≤ j) :
    (T ^ i) *ᵥ y ∈ krySpanLe T y j :=
  Submodule.subset_span ⟨i, by simp; omega, rfl⟩

theorem finrank_krySpanLe_ge (T : Matrix (Fin m) (Fin m) F) {y : Fin m → F} (hy : y ≠ 0) {J : ℕ}
    (h : ∀ j < J, (T ^ (j + 1)) *ᵥ y ∉ krySpanLe T y j) :
    ∀ j ≤ J, j + 1 ≤ Module.finrank F (krySpanLe T y j) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : krySpanLe T y 0 = Submodule.span F {y} := by
      unfold krySpanLe
      simp
    rw [h0, finrank_span_singleton hy]
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have hlt : krySpanLe T y j < krySpanLe T y (j + 1) := by
      rw [krySpanLe_succ]
      refine lt_of_le_of_ne le_sup_left fun heq => h j (by omega) ?_
      rw [heq]
      exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    have h2 := Submodule.finrank_lt_finrank_of_lt hlt
    omega

theorem exists_invariant_of_krylov (T : Matrix (Fin m) (Fin m) F) (U : Submodule F (Fin m → F)) {J : ℕ}
    (hJ : Module.finrank F U ≤ J) {y : Fin m → F} (hy0 : y ≠ 0) (hyU : ∀ j ≤ J, (T ^ j) *ᵥ y ∈ U) :
    ∃ W : Submodule F (Fin m → F), W ≠ ⊥ ∧ W ≤ U ∧ IsInvariant T W := by
  have hK : ∀ j ≤ J, krySpanLe T y j ≤ U := fun j hj => by
    unfold krySpanLe
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    exact hyU i (by omega)
  by_cases hst : ∃ j < J, (T ^ (j + 1)) *ᵥ y ∈ krySpanLe T y j
  · obtain ⟨j, hjJ, hj⟩ := hst
    refine ⟨krySpanLe T y j, ?_, hK j hjJ.le, ?_⟩
    · intro h
      apply hy0
      have h1 : (T ^ 0) *ᵥ y ∈ krySpanLe T y j := pow_mulVec_mem_krySpanLe T y (Nat.zero_le j)
      rw [h, Submodule.mem_bot, pow_zero, one_mulVec] at h1
      exact h1
    · intro v hv
      have hv' : v ∈ Submodule.span F ((fun i => (T ^ i) *ᵥ y) '' ↑(Finset.range (j + 1))) := hv
      clear hv
      induction hv' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        simp only [Finset.coe_range, Set.mem_Iio] at hi
        rw [mulVec_mulVec, ← pow_succ']
        rcases Nat.lt_or_ge i j with hlt | hge
        · exact pow_mulVec_mem_krySpanLe T y (by omega)
        · have hij : i = j := by omega
          rw [hij]
          exact hj
      | zero =>
        rw [mulVec_zero]
        exact Submodule.zero_mem _
      | add x z _ _ hx hz =>
        rw [mulVec_add]
        exact Submodule.add_mem _ hx hz
      | smul a x _ hx =>
        rw [mulVec_smul]
        exact Submodule.smul_mem _ a hx
  · push Not at hst
    have h1 := finrank_krySpanLe_ge T hy0 hst J le_rfl
    have h2 := Submodule.finrank_mono (hK J le_rfl)
    omega

end Krylov

section NoFactor

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem restrict_pow_apply (f : V →ₗ[ℚ] V) {W : Submodule ℚ V} (h : ∀ x ∈ W, f x ∈ W) (n : ℕ) (x : W) :
    (((f.restrict h) ^ n) x : V) = (f ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, pow_succ', Module.End.mul_apply]

theorem aeval_restrict_apply (f : V →ₗ[ℚ] V) {W : Submodule ℚ V} (h : ∀ x ∈ W, f x ∈ W) (q : ℚ[X])
    (x : W) : ((aeval (f.restrict h) q) x : V) = (aeval f q) x := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a => simp [aeval_monomial, restrict_pow_apply, Module.algebraMap_end_apply]

theorem eq_bot_of_noFactor {m D : ℕ} (T : Matrix (Fin m) (Fin m) ℤ)
    (hχ : ∀ f : ℤ[X], f.Monic → 1 ≤ f.natDegree → f.natDegree ≤ D → ¬ f ∣ T.charpoly)
    (W : Submodule ℚ (Fin m → ℚ)) (hW : IsInvariant (T.map (Int.castRingHom ℚ)) W)
    (hWD : Module.finrank ℚ W ≤ D) : W = ⊥ := by
  by_contra hW0
  set Tq := T.map (Int.castRingHom ℚ) with hTq
  set f := Tq.mulVecLin with hf
  have hW' : ∀ x ∈ W, f x ∈ W := fun x hx => by
    rw [hf, Matrix.mulVecLin_apply]
    exact hW x hx
  set fW := f.restrict hW' with hfW
  have hint : IsIntegral ℚ fW := IsIntegral.of_finite ℚ fW
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW0
  set g := minpoly ℚ fW with hg
  have hgm : g.Monic := minpoly.monic hint
  have hg1 : 0 < g.natDegree := minpoly.natDegree_pos hint
  have hgW : g.natDegree ≤ Module.finrank ℚ W := by
    have h1 : g ∣ fW.charpoly := LinearMap.minpoly_dvd_charpoly fW
    rw [← LinearMap.charpoly_natDegree fW]
    exact natDegree_le_of_dvd h1 (LinearMap.charpoly_monic fW).ne_zero
  have hgχ : g ∣ T.charpoly.map (algebraMap ℤ ℚ) := by
    have h1 : aeval fW f.charpoly = 0 := by
      ext x
      rw [aeval_restrict_apply, LinearMap.aeval_self_charpoly]
      simp
    have h2 : f.charpoly = T.charpoly.map (algebraMap ℤ ℚ) := by
      rw [hf, ← Matrix.toLin'_apply', Matrix.charpoly_toLin', hTq, Matrix.charpoly_map, algebraMap_int_eq]
    rw [← h2]
    exact minpoly.dvd ℚ fW h1
  obtain ⟨g', hg'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ (Matrix.charpoly_monic T) hgχ
  rw [hgm.leadingCoeff, C_1, mul_one] at hg'
  have hinj : Function.Injective (algebraMap ℤ ℚ) := (algebraMap ℤ ℚ).injective_int
  have hg'm : g'.Monic := monic_of_injective hinj (by rw [hg']; exact hgm)
  have hdeg : g'.natDegree = g.natDegree := by rw [← hg', natDegree_map_eq_of_injective hinj]
  have hdvd : g' ∣ T.charpoly := (map_dvd_map (algebraMap ℤ ℚ) hinj hg'm).1 (by rw [hg']; exact hgχ)
  exact hχ g' hg'm (by omega) (by omega) hdvd

end NoFactor

end DGS
