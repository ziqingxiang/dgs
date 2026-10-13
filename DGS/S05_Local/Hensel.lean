module

public import DGS.S05_Local.ShortCol
public import DGS.S03_Prelim.Switching

@[expose] public section

open Matrix Polynomial

namespace DGS

variable {n : ℕ}

section PiQ

variable {A : Matrix (Fin n) (Fin n) ℤ} {p : ℕ} [hp : Fact p.Prime] {β : (ZMod p)[X]} {E : ℕ}

omit hp in
theorem aeval_modP_eq_zero_of_mem_idealJ {q : ℕ} (hq : q ∣ p ^ E) {g : ℤ[X]}
    (hg : g ∈ idealJ p E A.charpoly) : aeval (modP q A) (g.map (Int.castRingHom (ZMod q))) = 0 := by
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hg
  have h1 : (Int.castRingHom (ZMod q)) ((p : ℤ) ^ E) = 0 := by
    rw [eq_intCast]
    have : (((p ^ E : ℕ) : ℤ) : ZMod q) = 0 := by
      rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff]; exact hq
    exact_mod_cast this
  have h2 : aeval (modP q A) (A.charpoly.map (Int.castRingHom (ZMod q))) = 0 := by
    rw [modP, ← Matrix.charpoly_map, aeval_self_charpoly]
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C, map_add, map_mul, map_mul,
    aeval_C, h1, map_zero, mul_zero, zero_add, h2, mul_zero]

variable (A p β E) in
noncomputable def piQ (q : ℕ) : Matrix (Fin n) (Fin n) (ZMod q) :=
  aeval (modP q A) ((idemZ p A.charpoly β E).map (Int.castRingHom (ZMod q)))

theorem piQ_eq (q : ℕ) : piQ A p β E q = (aeval A (idemZ p A.charpoly β E)).map (Int.castRingHom (ZMod q)) :=
  aeval_map_map _ A _

variable (hβ : β ∈ factorsSet (redP p A.charpoly)) (hE : 1 ≤ E) {q : ℕ} (hq : q ∣ p ^ E)
include hβ hq

theorem piQ_mul_self : piQ A p β E q * piQ A p β E q = piQ A p β E q := by
  have h := aeval_modP_eq_zero_of_mem_idealJ hq (idemZ_sq (charpoly_monic A) hβ E)
  rw [Polynomial.map_sub, Polynomial.map_pow, map_sub, map_pow, sub_eq_zero, sq] at h
  exact h

omit hβ hq in
theorem piQ_comm : modP q A * piQ A p β E q = piQ A p β E q * modP q A :=
  (aeval_mul_comm _ _).symm

omit hβ hq in
theorem piQ_transpose (hA : A.IsSymm) : (piQ A p β E q)ᵀ = piQ A p β E q := by
  rw [piQ, aeval_eq_sum_range, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.transpose_smul, Matrix.transpose_pow, (modP_isSymm q hA).eq]

omit hq in
include hE in
theorem aeval_pow_mul_piQ (hq : q ∣ p ^ E) :
    aeval (modP q A) ((liftZ p β ^ (mult (redP p A.charpoly) β * E)).map (Int.castRingHom (ZMod q)))
      * piQ A p β E q = 0 := by
  have h := aeval_modP_eq_zero_of_mem_idealJ hq (liftZ_pow_mul_idemZ (charpoly_monic A) hβ hE)
  rw [Polynomial.map_mul, map_mul] at h
  exact h

theorem dotProduct_piQ_sub (hA : A.IsSymm) (x y : Fin n → ZMod q) :
    (piQ A p β E q *ᵥ x) ⬝ᵥ (y - piQ A p β E q *ᵥ y) = 0 := by
  have h : ∀ u v : Fin n → ZMod q, (piQ A p β E q *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (piQ A p β E q *ᵥ v) := by
    intro u v
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, piQ_transpose hA, dotProduct_comm]
  rw [h, mulVec_sub, mulVec_mulVec, piQ_mul_self hβ hq, sub_self, dotProduct_zero]

end PiQ

noncomputable def redE (p E : ℕ) (hE : 1 ≤ E) : ZMod (p ^ E) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)

section Red

variable {p : ℕ} [hp : Fact p.Prime] {E : ℕ} (hE : 1 ≤ E)

omit hp in
theorem redE_comp :
    (redE p E hE).comp (Int.castRingHom (ZMod (p ^ E))) = Int.castRingHom (ZMod p) :=
  RingHom.ext_int _ _

omit hp in
theorem map_redE_modP (M : Matrix (Fin n) (Fin n) ℤ) :
    (modP (p ^ E) M).map (redE p E hE) = modP p M := by
  rw [modP, modP, Matrix.map_map, ← RingHom.coe_comp, redE_comp]

theorem map_redE_piQ {A : Matrix (Fin n) (Fin n) ℤ} {β : (ZMod p)[X]} :
    (piQ A p β E (p ^ E)).map (redE p E hE) = piQ A p β E p := by
  rw [piQ_eq, piQ_eq, Matrix.map_map, ← RingHom.coe_comp, redE_comp]

noncomputable def redVecE (x : Fin n → ZMod (p ^ E)) : Fin n → ZMod p :=
  fun i => redE p E hE (x i)

theorem redVecE_mulVec (M : Matrix (Fin n) (Fin n) (ZMod (p ^ E)))
    (x : Fin n → ZMod (p ^ E)) :
    redVecE hE (M *ᵥ x) = M.map (redE p E hE) *ᵥ redVecE hE x := by
  funext i
  simp only [redVecE, mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

end Red

section NE

variable {A : Matrix (Fin n) (Fin n) ℤ} {p : ℕ} [hp : Fact p.Prime] {β : (ZMod p)[X]} {E : ℕ}

variable (A p β E) in
noncomputable def NE : Submodule (ZMod (p ^ E)) (Fin n → ZMod (p ^ E)) :=
  LinearMap.range (piQ A p β E (p ^ E)).mulVecLin

variable (hβ : β ∈ factorsSet (redP p A.charpoly)) (hE : 1 ≤ E)
include hβ

theorem mem_NE_iff {x : Fin n → ZMod (p ^ E)} : x ∈ NE A p β E ↔ piQ A p β E (p ^ E) *ᵥ x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [Matrix.mulVecLin_apply, mulVec_mulVec, piQ_mul_self hβ dvd_rfl]
  · intro h
    exact ⟨x, h⟩

omit hβ in
theorem piQ_mulVec_mem_NE (x : Fin n → ZMod (p ^ E)) : piQ A p β E (p ^ E) *ᵥ x ∈ NE A p β E :=
  ⟨x, rfl⟩

theorem NE_isInvariant {x : Fin n → ZMod (p ^ E)} (hx : x ∈ NE A p β E) :
    modP (p ^ E) A *ᵥ x ∈ NE A p β E := by
  rw [mem_NE_iff hβ] at hx ⊢
  rw [mulVec_mulVec, ← piQ_comm, ← mulVec_mulVec, hx]

noncomputable def annVec {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    Ideal ℤ[X] where
  carrier := {g | aeval M (g.map (Int.castRingHom R)) *ᵥ v = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Polynomial.map_add, map_add, add_mulVec] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c g hg
    simp only [Set.mem_ofPred_eq, smul_eq_mul, Polynomial.map_mul, map_mul, ← mulVec_mulVec] at *
    rw [hg, mulVec_zero]

omit hβ in
theorem charpoly_mem_annVec (q : ℕ) (v : Fin n → ZMod q) : A.charpoly ∈ annVec (modP q A) v := by
  show aeval (modP q A) (A.charpoly.map (Int.castRingHom (ZMod q))) *ᵥ v = 0
  rw [modP, ← Matrix.charpoly_map, aeval_self_charpoly, zero_mulVec]

theorem piQ_p_mulVec_of_ker (hE : 1 ≤ E) {v : Fin n → ZMod p}
    (hv : aeval (modP p A) (β ^ mult (redP p A.charpoly) β) *ᵥ v = 0) :
    piQ A p β E p *ᵥ v = v := by
  set a := mult (redP p A.charpoly) β
  have ha : 1 ≤ a := mult_pos hβ
  have hCp : C (p : ℤ) ∈ annVec (modP p A) v := by
    show aeval (modP p A) ((C (p : ℤ)).map (Int.castRingHom (ZMod p))) *ᵥ v = 0
    rw [map_C, eq_intCast, Int.cast_natCast, ZMod.natCast_self, map_zero, map_zero, zero_mulVec]
  have hJ : idealJ p E A.charpoly ≤ annVec (modP p A) v := by
    rw [idealJ, Ideal.span_le]
    rintro x (rfl | rfl)
    · rw [C_pow]; exact Ideal.pow_mem_of_mem _ hCp _ hE
    · exact charpoly_mem_annVec p v
  have hβa : liftZ p β ^ a ∈ annVec (modP p A) v := by
    show aeval (modP p A) ((liftZ p β ^ a).map (Int.castRingHom (ZMod p))) *ᵥ v = 0
    rw [Polynomial.map_pow, map_liftZ]; exact hv
  have h1 := one_sub_idemZ_mem (charpoly_monic A) hβ hE hJ ha
    (by rw [C_pow]; exact Ideal.pow_mem_of_mem _ hCp _ ha) hβa
  have h2 : aeval (modP p A) ((1 - idemZ p A.charpoly β E).map (Int.castRingHom (ZMod p))) *ᵥ v =
      0 := h1
  rw [Polynomial.map_sub, Polynomial.map_one, map_sub, map_one, sub_mulVec, one_mulVec,
    sub_eq_zero] at h2
  exact h2.symm

include hE in
theorem aeval_mulVec_piQ_p (v : Fin n → ZMod p) :
    aeval (modP p A) (β ^ mult (redP p A.charpoly) β) *ᵥ (piQ A p β E p *ᵥ v) = 0 := by
  set a := mult (redP p A.charpoly) β
  set u := piQ A p β E p *ᵥ v
  have hdvd : p ∣ p ^ E := dvd_pow_self p (by omega)
  have h1 : liftZ p β ^ (a * E) ∈ annVec (modP p A) u := by
    show aeval (modP p A) ((liftZ p β ^ (a * E)).map (Int.castRingHom (ZMod p))) *ᵥ
      (piQ A p β E p *ᵥ v) = 0
    rw [mulVec_mulVec, aeval_pow_mul_piQ hβ hE hdvd, zero_mulVec]
  have hCp : C (p : ℤ) ∈ annVec (modP p A) u := by
    show aeval (modP p A) ((C (p : ℤ)).map (Int.castRingHom (ZMod p))) *ᵥ u = 0
    rw [map_C, eq_intCast, Int.cast_natCast, ZMod.natCast_self, map_zero, map_zero, zero_mulVec]
  have h2 := liftZ_pow_mult_mem (charpoly_monic A) hβ (a * E) hCp (charpoly_mem_annVec p u) h1
  have h3 : aeval (modP p A) ((liftZ p β ^ a).map (Int.castRingHom (ZMod p))) *ᵥ u = 0 := h2
  rwa [Polynomial.map_pow, map_liftZ] at h3

theorem reduction_NE (hE : 1 ≤ E) :
    (∀ x ∈ NE A p β E, aeval (modP p A) (β ^ mult (redP p A.charpoly) β) *ᵥ redVecE hE x = 0) ∧
    ∀ v : Fin n → ZMod p, aeval (modP p A) (β ^ mult (redP p A.charpoly) β) *ᵥ v = 0 →
      ∃ x ∈ NE A p β E, redVecE hE x = v := by
  constructor
  · rintro x ⟨y, rfl⟩
    rw [Matrix.mulVecLin_apply, redVecE_mulVec, map_redE_piQ]
    exact aeval_mulVec_piQ_p hβ hE _
  · intro v hv
    have hsurj : Function.Surjective (redE p E hE) := ZMod.castHom_surjective _
    choose lift hlift using hsurj
    set x0 : Fin n → ZMod (p ^ E) := fun i => lift (v i)
    refine ⟨piQ A p β E (p ^ E) *ᵥ x0, piQ_mulVec_mem_NE _, ?_⟩
    rw [redVecE_mulVec, map_redE_piQ]
    have : redVecE hE x0 = v := funext fun i => hlift (v i)
    rw [this]
    exact piQ_p_mulVec_of_ker hβ hE hv

theorem dot_nondegenerate_ker (hA : A.IsSymm) (hE : 1 ≤ E) {u : Fin n → ZMod p}
    (hu : aeval (modP p A) (β ^ mult (redP p A.charpoly) β) *ᵥ u = 0)
    (h : ∀ v : Fin n → ZMod p, aeval (modP p A) (β ^ mult (redP p A.charpoly) β) *ᵥ v = 0 →
      u ⬝ᵥ v = 0) : u = 0 := by
  have hdvd : p ∣ p ^ E := dvd_pow_self p (by omega)
  have hpu := piQ_p_mulVec_of_ker hβ hE hu
  funext i
  have h1 : u ⬝ᵥ Pi.single i 1 = u ⬝ᵥ (piQ A p β E p *ᵥ Pi.single i 1) +
      (piQ A p β E p *ᵥ u) ⬝ᵥ (Pi.single i 1 - piQ A p β E p *ᵥ Pi.single i 1) := by
    rw [hpu, ← dotProduct_add, add_sub_cancel]
  rw [h _ (aeval_mulVec_piQ_p hβ hE _), dotProduct_piQ_sub hβ hdvd hA, add_zero] at h1
  simpa [dotProduct, Pi.single_apply] using h1

end NE

section Unique

variable {p : ℕ} [hp : Fact p.Prime] {φ : ℤ[X]} {β : (ZMod p)[X]}

theorem idemZ_sub_mem_idealJ (hφ : φ.Monic) (hβ : β ∈ factorsSet (redP p φ)) {E K : ℕ} (hE : 1 ≤ E)
    (hEK : E ≤ K) : idemZ p φ β K - idemZ p φ β E ∈ idealJ p E φ := by
  set a := idemZ p φ β K
  set b := idemZ p φ β E
  set x := a - b
  have hx1 : x ∈ idealJ p 1 φ := by
    have h1 := idemZ_sub_crtLift hφ hβ (show 1 ≤ K by omega)
    have h2 := idemZ_sub_crtLift hφ hβ hE
    have : x = (a - crtLift p φ β) - (b - crtLift p φ β) := by ring
    rw [this]; exact sub_mem h1 h2
  have ha : a ^ 2 - a ∈ idealJ p E φ := idealJ_mono hEK φ (idemZ_sq hφ hβ K)
  have hb : b ^ 2 - b ∈ idealJ p E φ := idemZ_sq hφ hβ E
  have hx3 : x ^ 3 - x ∈ idealJ p E φ := by
    have : x ^ 3 - x = (a ^ 2 - a) * (1 + a - 3 * b) + (b ^ 2 - b) * (3 * a - 1 - b) := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)
  have hiter : ∀ m : ℕ, x - x ^ (2 * m + 1) ∈ idealJ p E φ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have : x - x ^ (2 * (m + 1) + 1) = (x - x ^ (2 * m + 1)) - x ^ (2 * m) * (x ^ 3 - x) := by ring
      rw [this]
      exact sub_mem ih (Ideal.mul_mem_left _ _ hx3)
  have hpow : x ^ (2 * E + 1) ∈ idealJ p E φ :=
    idealJ_mono (show E ≤ 2 * E + 1 by omega) φ
      (idealJ_one_pow_le (2 * E + 1) φ (Ideal.pow_mem_pow hx1 _))
  have : x = (x - x ^ (2 * E + 1)) + x ^ (2 * E + 1) := by ring
  rw [this]
  exact add_mem (hiter E) hpow

end Unique

def krylov {R : Type*} [CommRing R] {r : ℕ} (B : Matrix (Fin r) (Fin r) R) (w : Fin r → R) :
    Matrix (Fin r) (Fin r) R :=
  Matrix.of fun i j => (B ^ (j : ℕ) *ᵥ w) i

theorem krylov_mulVec {R : Type*} [CommRing R] {r : ℕ} (B : Matrix (Fin r) (Fin r) R)
    (w z : Fin r → R) : krylov B w *ᵥ z = ∑ j, z j • (B ^ (j : ℕ) *ᵥ w) := by
  funext i
  simp only [krylov, mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

section Hensel

variable {A : Matrix (Fin n) (Fin n) ℤ} {p : ℕ} [hp : Fact p.Prime] {β : (ZMod p)[X]} {E : ℕ}

theorem zmod_pow_dvd_of_ne_zero (hE : 1 ≤ E) {x : ZMod (p ^ E)} (hx : x ≠ 0) :
    ∃ y : ZMod (p ^ E), (p : ZMod (p ^ E)) ^ (E - 1) = x * y := by
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  set v := x.val with hvdef
  have hxv : ((v : ℕ) : ZMod (p ^ E)) = x := ZMod.natCast_zmod_val x
  have hv0 : v ≠ 0 := by
    intro h; apply hx; rw [← hxv, h, Nat.cast_zero]
  have hvlt : v < p ^ E := ZMod.val_lt x
  set i := v.factorization p
  set m := ordCompl[p] v
  have hvm : p ^ i * m = v := Nat.ordProj_mul_ordCompl_eq_self v p
  have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp.out hv0
  have hiE : i < E := by
    have : p ^ i ≤ v := Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) ⟨m, hvm.symm⟩
    exact (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 (lt_of_le_of_lt this hvlt)
  have hmcop : Nat.Coprime m (p ^ E) := Nat.Coprime.pow_right E hcop.symm
  set u := ZMod.unitOfCoprime m hmcop
  have hu : (u : ZMod (p ^ E)) = (m : ZMod (p ^ E)) := ZMod.coe_unitOfCoprime m hmcop
  have hx' : x = (p : ZMod (p ^ E)) ^ i * (m : ZMod (p ^ E)) := by
    rw [← hxv, ← hvm]; push_cast; ring
  refine ⟨(p : ZMod (p ^ E)) ^ (E - 1 - i) * ((u⁻¹ : (ZMod (p ^ E))ˣ) : ZMod (p ^ E)), ?_⟩
  rw [hx', ← hu]
  have h1 : (u : ZMod (p ^ E)) * ((u⁻¹ : (ZMod (p ^ E))ˣ) : ZMod (p ^ E)) = 1 := Units.mul_inv u
  have h2 : (p : ZMod (p ^ E)) ^ (E - 1) = (p : ZMod (p ^ E)) ^ i * (p : ZMod (p ^ E)) ^ (E - 1 - i) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  rw [h2]
  linear_combination (-((p : ZMod (p ^ E)) ^ i * (p : ZMod (p ^ E)) ^ (E - 1 - i))) * h1

variable (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0)
  (hβ : β ∈ factorsSet (redP p A.charpoly)) (hE : 1 ≤ E)
include hA hn hW hβ hE

omit hA in
theorem pow_smul_mem_latC_of_NE
    (hNE : ∀ x ∈ NE A p β E, ∃ c : Fin n → ZMod (p ^ E),
      ((p : ZMod (p ^ E)) ^ (E - 1)) • x = walkMatrix (modP (p ^ E) A) *ᵥ c)
    {y : Fin n → ℚ} (hy : y ∈ mPart A p β (latZ n)) : ((p : ℤ) ^ (E - 1)) • y ∈ latC A := by
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  have hZ := lem_ideals hn (isMateMatrix_one A)
  rw [latOf_one] at hZ
  obtain ⟨hZst, hZu, hCZ, hZC⟩ := hZ
  have hK := one_le_Kexp hW
  set K := Kexp A
  have hφ := charpoly_monic A
  have hKE : E ≤ K ∨ K < E := le_or_gt E K
  have hπ : (aeval A (idemZ p A.charpoly β (max E K))).map (Int.castRingHom (ZMod (p ^ E))) =
      piQ A p β E (p ^ E) := by
    rw [piQ_eq, ← aeval_map_map, ← aeval_map_map, ← sub_eq_zero, ← map_sub, ← Polynomial.map_sub]
    exact aeval_modP_eq_zero_of_mem_idealJ dvd_rfl
      (idemZ_sub_mem_idealJ hφ hβ hE (le_max_left E K))
  set K' := max E K
  have hK' : 1 ≤ K' := le_trans hK (le_max_right E K)
  have step5 : ∀ y ∈ mPart A p β (latZ n), ∃ d z : Fin n → ℤ,
      ((p : ℤ) ^ (E - 1)) • y = toQ (walkMatrix A) *ᵥ intVec d + ((p : ℤ) ^ E) • intVec z := by
    intro y hy
    obtain ⟨c, rfl⟩ := hy.1
    have hyK' : C ((p : ℤ) ^ K') ∈ annC A (intVec c) := by
      have h := C_pow_card_mem_annC_of_mPart hn hW (mPart_mono hZC hy)
      rw [show K' = K + (K' - K) by omega, pow_add, C_mul]
      exact Ideal.mul_mem_right _ _ h
    have hL2 := actZ_idemZ_sub_mem hβ hK' hy hyK'
    obtain ⟨d0, hd0⟩ := mem_latOf.1 hL2
    rw [actZ_mulVec_intVec, mulVec_intVec] at hd0
    have hd0' : c - aeval A (idemZ p A.charpoly β K') *ᵥ c = walkMatrix A *ᵥ d0 := by
      apply intVec_injective
      rw [← hd0]
      funext i; simp [intVec]
    have hred := congrArg (redVec (p ^ E)) hd0'
    have hsubv : ∀ u v : Fin n → ℤ, redVec (p ^ E) (u - v) = redVec (p ^ E) u - redVec (p ^ E) v := by
      intro u v; funext i; simp [redVec]
    have e1 : modP (p ^ E) (aeval A (idemZ p A.charpoly β K')) = piQ A p β E (p ^ E) := hπ
    have e2 : modP (p ^ E) (walkMatrix A) = walkMatrix (modP (p ^ E) A) := walkMatrix_map A _
    rw [hsubv, redVec_mulVec, redVec_mulVec, e1, e2] at hred
    set cE := redVec (p ^ E) c
    obtain ⟨c1, hc1⟩ := hNE _ (piQ_mulVec_mem_NE (A := A) (β := β) cE)
    set D := ((p : ZMod (p ^ E)) ^ (E - 1)) • redVec (p ^ E) d0 + c1
    have hD : ((p : ZMod (p ^ E)) ^ (E - 1)) • cE = walkMatrix (modP (p ^ E) A) *ᵥ D := by
      have : cE = (cE - piQ A p β E (p ^ E) *ᵥ cE) + piQ A p β E (p ^ E) *ᵥ cE := by abel
      rw [this, smul_add, hred, hc1, mulVec_add, mulVec_smul]
    set Dint : Fin n → ℤ := fun i => ((D i).val : ℤ)
    have hDint : redVec (p ^ E) Dint = D := by
      funext i; simp [redVec, Dint]
    have hz : ∀ i, ((p : ℤ) ^ E) ∣ (((p : ℤ) ^ (E - 1)) • c - walkMatrix A *ᵥ Dint) i := by
      have h0 : redVec (p ^ E) (((p : ℤ) ^ (E - 1)) • c - walkMatrix A *ᵥ Dint) = 0 := by
        rw [hsubv, redVec_mulVec, hDint, e2, ← hD]
        funext i; simp [redVec, cE]
      intro i
      have := (redVec_eq_zero_iff _).1 h0 i
      exact_mod_cast this
    choose z hz using hz
    refine ⟨Dint, z, ?_⟩
    rw [mulVec_intVec, ← intVec_smul, ← intVec_smul, ← intVec_add]
    congr 1
    funext i
    have := hz i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this ⊢
    linear_combination this
  obtain ⟨c0, N', hcopN, hdec⟩ := exists_pPart_decomp hn hW (A := A) p
  set f := idemZ p A.charpoly β K
  have stepU : ∀ y ∈ mPart A p β (latZ n), ∃ y' ∈ mPart A p β (latZ n),
      ((p : ℤ) ^ (E - 1)) • y - ((p : ℤ) ^ E) • y' ∈ latC A := by
    intro y hy
    obtain ⟨d, z, hdz⟩ := step5 y hy
    have hyC : y ∈ latDual (latC A) := hZC hy.1
    have hzC : intVec z ∈ latDual (latC A) := hZC ⟨z, rfl⟩
    refine ⟨c0 • (actZ A f *ᵥ intVec z), ?_, ?_⟩
    · rw [← mulVec_smul]
      exact actZ_idemZ_mem_mPart hβ hK hZst (Submodule.smul_mem _ _ ⟨z, rfl⟩) (hdec _ hzC).1
    ·
      have hyf := actZ_idemZ_sub_mem hβ hK hy (C_pow_card_mem_annC_of_mPart hn hW (mPart_mono hZC hy))
      obtain ⟨-, k, hk1, -⟩ := hy
      have h1c : C (1 - c0) ∈ annC A y := by
        obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left k hcopN)
        have hN'c : C ((N' : ℤ) * (1 - c0)) ∈ annC A y := C_mem_annC.2 (hdec y hyC).2
        have : C (1 - c0) = C (u * (1 - c0)) * C ((p : ℤ) ^ k) + C v * C ((N' : ℤ) * (1 - c0)) := by
          rw [← C_mul, ← C_mul, ← C_add]
          congr 1
          push_cast at huv
          linear_combination (-(1 - c0)) * huv
        rw [this]
        exact add_mem (Ideal.mul_mem_left _ _ hk1) (Ideal.mul_mem_left _ _ hN'c)
      have hP : y - c0 • (actZ A f *ᵥ y) ∈ latC A := by
        have : y - c0 • (actZ A f *ᵥ y) = (y - actZ A f *ᵥ y) + actZ A f *ᵥ ((1 - c0) • y) := by
          rw [mulVec_smul, sub_smul, one_smul]; abel
        rw [this]
        exact add_mem hyf (actZ_mulVec_mem (latC_isAStable A) _ (C_mem_annC.1 h1c))
      have hWd : toQ (walkMatrix A) *ᵥ intVec d ∈ latC A := mem_latOf.2 ⟨d, rfl⟩
      have : ((p : ℤ) ^ (E - 1)) • y - ((p : ℤ) ^ E) • (c0 • (actZ A f *ᵥ intVec z)) =
          ((p : ℤ) ^ (E - 1)) • (y - c0 • (actZ A f *ᵥ y)) +
            c0 • (actZ A f *ᵥ (toQ (walkMatrix A) *ᵥ intVec d)) := by
        have h2 : toQ (walkMatrix A) *ᵥ intVec d = ((p : ℤ) ^ (E - 1)) • y - ((p : ℤ) ^ E) • intVec z := by
          rw [hdz]; abel
        rw [h2, mulVec_sub, mulVec_smul, mulVec_smul, smul_sub, smul_sub, smul_comm c0 ((p : ℤ) ^ (E - 1)),
          smul_comm c0 ((p : ℤ) ^ E)]
        abel
      rw [this]
      exact add_mem (Submodule.smul_mem _ _ hP)
        (Submodule.smul_mem _ _ (actZ_mulVec_mem (latC_isAStable A) _ hWd))
  have stepIter : ∀ t : ℕ, ∀ y ∈ mPart A p β (latZ n), ∃ y' ∈ mPart A p β (latZ n),
      ((p : ℤ) ^ (E - 1)) • y - ((p : ℤ) ^ (E + t)) • y' ∈ latC A := by
    intro t
    induction t with
    | zero => intro y hy; simpa using stepU y hy
    | succ t ih =>
      intro y hy
      obtain ⟨y1, hy1, h1⟩ := ih y hy
      obtain ⟨y2, hy2, h2⟩ := stepU y1 hy1
      refine ⟨y2, hy2, ?_⟩
      have : ((p : ℤ) ^ (E - 1)) • y - ((p : ℤ) ^ (E + (t + 1))) • y2 =
          (((p : ℤ) ^ (E - 1)) • y - ((p : ℤ) ^ (E + t)) • y1) +
            ((p : ℤ) ^ (t + 1)) • (((p : ℤ) ^ (E - 1)) • y1 - ((p : ℤ) ^ E) • y2) := by
        rw [smul_sub, smul_smul, smul_smul, ← pow_add, ← pow_add]
        rw [show t + 1 + (E - 1) = E + t by omega, show t + 1 + E = E + (t + 1) by omega]
        abel
      rw [this]
      exact add_mem h1 (Submodule.smul_mem _ _ h2)
  obtain ⟨y', hy', h'⟩ := stepIter K y hy
  have hy'K : ((p : ℤ) ^ (E + K)) • y' ∈ latC A := by
    rw [pow_add, ← smul_smul]
    exact Submodule.smul_mem _ _
      (C_mem_annC.1 (C_pow_card_mem_annC_of_mPart hn hW (mPart_mono hZC hy')))
  have : ((p : ℤ) ^ (E - 1)) • y = (((p : ℤ) ^ (E - 1)) • y - ((p : ℤ) ^ (E + K)) • y') +
      ((p : ℤ) ^ (E + K)) • y' := by abel
  rw [this]
  exact add_mem h' hy'K

theorem lem_hensel {r : ℕ} (V : Matrix (Fin n) (Fin r) (ZMod (p ^ E)))
    (hVN : ∀ j, (fun i => V i j) ∈ NE A p β E) (hspan : ∀ x ∈ NE A p β E, ∃ c, x = V *ᵥ c)
    (hΘ : IsUnit (Vᵀ * V).det) (B : Matrix (Fin r) (Fin r) (ZMod (p ^ E)))
    (hB : modP (p ^ E) A * V = V * B)
    (hexp : ∃ y ∈ mPart A p β (latZ n), ((p : ℤ) ^ (E - 1)) • y ∉ latC A) :
    (krylov B ((Vᵀ * V)⁻¹ *ᵥ (Vᵀ *ᵥ ones n (ZMod (p ^ E))))).det = 0 := by
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  have : Fact (1 < p ^ E) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  set AE := modP (p ^ E) A
  set π := piQ A p β E (p ^ E)
  set e := ones n (ZMod (p ^ E))
  set w := (Vᵀ * V)⁻¹ *ᵥ (Vᵀ *ᵥ e)
  by_contra hK
  obtain ⟨hy, hy1, hy2⟩ := hexp
  apply hy2
  refine pow_smul_mem_latC_of_NE hn hW hβ hE ?_ hy1
  obtain ⟨y0, hy0⟩ := zmod_pow_dvd_of_ne_zero hE hK
  have hKsurj : ∀ z : Fin r → ZMod (p ^ E), ∃ z',
      ((p : ZMod (p ^ E)) ^ (E - 1)) • z = krylov B w *ᵥ z' := by
    intro z
    refine ⟨y0 • ((krylov B w).adjugate *ᵥ z), ?_⟩
    rw [mulVec_smul, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec, smul_smul, hy0, mul_comm]
  have hπe : π *ᵥ e ∈ NE A p β E := piQ_mulVec_mem_NE _
  obtain ⟨u0, hu0⟩ := hspan _ hπe
  have hVt : Vᵀ *ᵥ (π *ᵥ e) = Vᵀ *ᵥ e := by
    funext j
    have hcol := (mem_NE_iff hβ).1 (hVN j)
    have h0 := dotProduct_piQ_sub hβ (dvd_rfl : p ^ E ∣ p ^ E) hA (fun i => V i j) e
    rw [hcol] at h0
    have h1 : (Vᵀ *ᵥ e) j - (Vᵀ *ᵥ (π *ᵥ e)) j = (fun i => V i j) ⬝ᵥ (e - π *ᵥ e) := by
      simp only [mulVec, dotProduct, transpose_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [h0, sub_eq_zero] at h1
    exact h1.symm
  have hVw : V *ᵥ w = π *ᵥ e := by
    have h1 : (Vᵀ * V) *ᵥ u0 = Vᵀ *ᵥ e := by rw [← mulVec_mulVec, ← hu0, hVt]
    have h2 : u0 = w := by
      show u0 = (Vᵀ * V)⁻¹ *ᵥ (Vᵀ *ᵥ e)
      rw [← h1, mulVec_mulVec, nonsing_inv_mul _ hΘ, one_mulVec]
    rw [← h2, hu0]
  have hpow : ∀ j : ℕ, V *ᵥ (B ^ j *ᵥ w) = AE ^ j *ᵥ (π *ᵥ e) := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_mulVec, pow_zero, one_mulVec, hVw]
    | succ j ih =>
      rw [pow_succ', ← mulVec_mulVec, mulVec_mulVec, ← hB, ← mulVec_mulVec, ih, mulVec_mulVec,
        ← pow_succ']
  intro x hx
  obtain ⟨c0, rfl⟩ := hspan x hx
  obtain ⟨z', hz'⟩ := hKsurj c0
  set g : (ZMod (p ^ E))[X] := ∑ j : Fin r, monomial (j : ℕ) (z' j)
  have haeval : aeval AE g = ∑ j : Fin r, z' j • AE ^ (j : ℕ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [aeval_monomial, Algebra.smul_def]
  have h1 : ((p : ZMod (p ^ E)) ^ (E - 1)) • (V *ᵥ c0) = aeval AE g *ᵥ (π *ᵥ e) := by
    rw [← mulVec_smul, hz', krylov_mulVec, mulVec_sum, haeval, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mulVec_smul, hpow, smul_mulVec]
  have h2 : aeval AE g *ᵥ (π *ᵥ e) =
      aeval AE (g * (idemZ p A.charpoly β E).map (Int.castRingHom (ZMod (p ^ E)))) *ᵥ e := by
    rw [mulVec_mulVec, map_mul]; rfl
  rw [h1, h2, aeval_mulVec_ones_eq AE hn]
  exact ⟨_, rfl⟩

end Hensel

end DGS
