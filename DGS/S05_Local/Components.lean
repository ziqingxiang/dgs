module

public import DGS.S05_Local.DiscModule
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

open Polynomial UniqueFactorizationMonoid

namespace DGS

section FieldCRT

open Classical

variable {F : Type*} [Field F]

noncomputable def factorsSet (φ : F[X]) : Finset F[X] := (normalizedFactors φ).toFinset

noncomputable def mult (φ β : F[X]) : ℕ := (normalizedFactors φ).count β

variable {φ : F[X]}

theorem irreducible_of_mem_factorsSet {β : F[X]} (h : β ∈ factorsSet φ) : Irreducible β :=
  irreducible_of_normalized_factor β (Multiset.mem_toFinset.1 h)

theorem monic_of_mem_factorsSet {β : F[X]} (h : β ∈ factorsSet φ) : β.Monic := by
  have hm := Multiset.mem_toFinset.1 h
  rw [← normalize_normalized_factor β hm]
  exact monic_normalize (irreducible_of_normalized_factor β hm).ne_zero

theorem mult_pos {β : F[X]} (h : β ∈ factorsSet φ) : 0 < mult φ β :=
  Multiset.count_pos.2 (Multiset.mem_toFinset.1 h)

theorem prod_factorsSet (hφ : φ.Monic) : ∏ β ∈ factorsSet φ, β ^ mult φ β = φ := by
  have hmon : (∏ β ∈ factorsSet φ, β ^ mult φ β).Monic :=
    monic_prod_of_monic _ _ fun β hβ => (monic_of_mem_factorsSet hβ).pow _
  refine eq_of_monic_of_associated hmon hφ ?_
  have := prod_normalizedFactors hφ.ne_zero
  rw [Finset.prod_multiset_count] at this
  exact this

theorem eq_of_mem_factorsSet_of_dvd {β β' : F[X]} (hβ : β ∈ factorsSet φ) (hβ' : β' ∈ factorsSet φ)
    (h : β ∣ β') : β = β' :=
  eq_of_monic_of_associated (monic_of_mem_factorsSet hβ) (monic_of_mem_factorsSet hβ')
    ((irreducible_of_mem_factorsSet hβ).associated_of_dvd (irreducible_of_mem_factorsSet hβ') h)

theorem isCoprime_of_mem_factorsSet {β β' : F[X]} (hβ : β ∈ factorsSet φ)
    (hβ' : β' ∈ factorsSet φ) (hne : β ≠ β') : IsCoprime β β' := by
  rw [(irreducible_of_mem_factorsSet hβ).coprime_iff_not_dvd]
  exact fun h => hne (eq_of_mem_factorsSet_of_dvd hβ hβ' h)

theorem mem_factorsSet_of_dvd (hφ : φ.Monic) {β : F[X]} (hβm : β.Monic) (hβi : Irreducible β)
    (h : β ∣ φ) : β ∈ factorsSet φ := by
  obtain ⟨q, hq, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hφ.ne_zero hβi h
  have hq' : q ∈ factorsSet φ := Multiset.mem_toFinset.2 hq
  rw [eq_of_monic_of_associated hβm (monic_of_mem_factorsSet hq') hassoc]
  exact hq'

theorem pow_mult_dvd {β : F[X]} (hφ : φ.Monic) (hβ : β ∈ factorsSet φ) : β ^ mult φ β ∣ φ := by
  conv_rhs => rw [← prod_factorsSet hφ]
  exact Finset.dvd_prod_of_mem _ hβ

theorem dvd_of_mem_factorsSet {β : F[X]} (hφ : φ.Monic) (hβ : β ∈ factorsSet φ) : β ∣ φ :=
  (dvd_pow_self β (mult_pos hβ).ne').trans (pow_mult_dvd hφ hβ)

theorem dvd_of_forall_pow_mult_dvd (hφ : φ.Monic) {z : F[X]}
    (h : ∀ β ∈ factorsSet φ, β ^ mult φ β ∣ z) : φ ∣ z := by
  rw [← prod_factorsSet hφ]
  refine Finset.prod_dvd_of_coprime ?_ h
  intro β hβ β' hβ' hne
  exact (isCoprime_of_mem_factorsSet hβ hβ' hne).pow

noncomputable def cofactor (φ β : F[X]) : F[X] := ∏ β' ∈ (factorsSet φ).erase β, β' ^ mult φ β'

theorem pow_mul_cofactor (hφ : φ.Monic) {β : F[X]} (hβ : β ∈ factorsSet φ) :
    β ^ mult φ β * cofactor φ β = φ := by
  rw [cofactor]
  exact (Finset.mul_prod_erase (factorsSet φ) (fun β => β ^ mult φ β) hβ).trans
    (prod_factorsSet hφ)

theorem isCoprime_pow_cofactor {β : F[X]} (hβ : β ∈ factorsSet φ) :
    IsCoprime (β ^ mult φ β) (cofactor φ β) := by
  rw [cofactor]
  refine IsCoprime.prod_right fun β' hβ' => ?_
  exact (isCoprime_of_mem_factorsSet hβ (Finset.mem_of_mem_erase hβ')
    (Finset.ne_of_mem_erase hβ').symm).pow

theorem pow_mult_dvd_cofactor {β β' : F[X]} (hβ' : β' ∈ factorsSet φ) (hne : β' ≠ β) :
    β' ^ mult φ β' ∣ cofactor φ β :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hne, hβ'⟩)

noncomputable def crtIdem (φ β : F[X]) : F[X] :=
  if h : IsCoprime (β ^ mult φ β) (cofactor φ β) then h.choose_spec.choose * cofactor φ β else 0

theorem crtIdem_sub_one {β : F[X]} (hβ : β ∈ factorsSet φ) : β ^ mult φ β ∣ crtIdem φ β - 1 := by
  have h := isCoprime_pow_cofactor hβ
  rw [crtIdem, dite_eq_left h]
  refine ⟨-h.choose, ?_⟩
  linear_combination h.choose_spec.choose_spec

theorem crtIdem_of_ne {β β' : F[X]} (hβ' : β' ∈ factorsSet φ) (hne : β' ≠ β) :
    β' ^ mult φ β' ∣ crtIdem φ β := by
  rw [crtIdem]
  split_ifs
  · exact Dvd.dvd.mul_left (pow_mult_dvd_cofactor hβ' hne) _
  · exact dvd_zero _

theorem crtIdem_sq (hφ : φ.Monic) {β : F[X]} (hβ : β ∈ factorsSet φ) :
    φ ∣ crtIdem φ β ^ 2 - crtIdem φ β := by
  refine dvd_of_forall_pow_mult_dvd hφ fun β' hβ' => ?_
  rw [sq, ← mul_sub_one]
  by_cases h : β' = β
  · subst h; exact Dvd.dvd.mul_left (crtIdem_sub_one hβ) _
  · exact Dvd.dvd.mul_right (crtIdem_of_ne hβ' h) _

theorem crtIdem_mul (hφ : φ.Monic) {β β' : F[X]} (hne : β ≠ β') :
    φ ∣ crtIdem φ β * crtIdem φ β' := by
  refine dvd_of_forall_pow_mult_dvd hφ fun β'' hβ'' => ?_
  by_cases h : β'' = β
  · subst h; exact Dvd.dvd.mul_left (crtIdem_of_ne hβ'' hne) _
  · exact Dvd.dvd.mul_right (crtIdem_of_ne hβ'' h) _

theorem crtIdem_sum (hφ : φ.Monic) : φ ∣ ∑ β ∈ factorsSet φ, crtIdem φ β - 1 := by
  refine dvd_of_forall_pow_mult_dvd hφ fun β hβ => ?_
  rw [← Finset.add_sum_erase _ _ hβ, add_sub_right_comm]
  refine dvd_add (crtIdem_sub_one hβ) (Finset.dvd_sum fun β' hβ' => ?_)
  exact crtIdem_of_ne hβ (Finset.ne_of_mem_erase hβ').symm

theorem pow_mult_mul_crtIdem (hφ : φ.Monic) (β : F[X]) : φ ∣ β ^ mult φ β * crtIdem φ β := by
  refine dvd_of_forall_pow_mult_dvd hφ fun β' hβ' => ?_
  by_cases h : β' = β
  · subst h; exact dvd_mul_right _ _
  · exact Dvd.dvd.mul_left (crtIdem_of_ne hβ' h) _

theorem dvd_crtIdem_sub_one {β : F[X]} (hβ : β ∈ factorsSet φ) : β ∣ crtIdem φ β - 1 :=
  (dvd_pow_self β (mult_pos hβ).ne').trans (crtIdem_sub_one hβ)

theorem dvd_crtIdem_of_ne {β β' : F[X]} (hβ : β ∈ factorsSet φ) (hne : β ≠ β') :
    β ∣ crtIdem φ β' :=
  (dvd_pow_self β (mult_pos hβ).ne').trans (crtIdem_of_ne hβ hne)

end FieldCRT

section IntLift

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def liftZ (β : (ZMod p)[X]) : ℤ[X] :=
  (map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) β).choose

theorem map_liftZ (β : (ZMod p)[X]) : (liftZ p β).map (Int.castRingHom (ZMod p)) = β :=
  (map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) β).choose_spec

theorem map_eq_zero_iff_C_dvd (f : ℤ[X]) :
    f.map (Int.castRingHom (ZMod p)) = 0 ↔ C (p : ℤ) ∣ f := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    have := congrArg (coeff · i) h
    simp only [coeff_map, eq_intCast, coeff_zero] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  · intro h
    ext i
    simp [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (h i)]

noncomputable def idealJ (K : ℕ) (φ : ℤ[X]) : Ideal ℤ[X] := Ideal.span {C ((p : ℤ) ^ K), φ}

noncomputable def idealM (β : (ZMod p)[X]) : Ideal ℤ[X] := Ideal.span {C (p : ℤ), liftZ p β}

variable {p}

theorem mem_idealJ_one_iff (φ f : ℤ[X]) :
    f ∈ idealJ p 1 φ ↔ φ.map (Int.castRingHom (ZMod p)) ∣ f.map (Int.castRingHom (ZMod p)) := by
  rw [idealJ, pow_one, Ideal.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨b.map (Int.castRingHom (ZMod p)), ?_⟩
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C]
    simp [mul_comm]
  · rintro ⟨h, hh⟩
    have h0 : (f - φ * liftZ p h).map (Int.castRingHom (ZMod p)) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, map_liftZ, hh, sub_self]
    obtain ⟨q, hq⟩ := (map_eq_zero_iff_C_dvd p _).1 h0
    exact ⟨q, liftZ p h, by linear_combination -hq⟩

theorem mem_idealM_iff (β : (ZMod p)[X]) (f : ℤ[X]) :
    f ∈ idealM p β ↔ β ∣ f.map (Int.castRingHom (ZMod p)) := by
  rw [idealM, Ideal.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨b.map (Int.castRingHom (ZMod p)), ?_⟩
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C, map_liftZ]
    simp [mul_comm]
  · rintro ⟨h, hh⟩
    have h0 : (f - liftZ p β * liftZ p h).map (Int.castRingHom (ZMod p)) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, map_liftZ, map_liftZ, hh, sub_self]
    obtain ⟨q, hq⟩ := (map_eq_zero_iff_C_dvd p _).1 h0
    exact ⟨q, liftZ p h, by linear_combination -hq⟩

theorem idealJ_one_le_idealM {φ : ℤ[X]} {β : (ZMod p)[X]}
    (hβ : β ∣ φ.map (Int.castRingHom (ZMod p))) : idealJ p 1 φ ≤ idealM p β := by
  intro f hf
  rw [mem_idealJ_one_iff] at hf
  rw [mem_idealM_iff]
  exact hβ.trans hf

theorem span_pair_pow_le (a b : ℤ[X]) (K : ℕ) :
    Ideal.span {a, b} ^ K ≤ Ideal.span {a ^ K, b} := by
  induction K with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one, pow_zero]
    exact Ideal.subset_span (Set.mem_insert _ _)
  | succ K ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [Ideal.mul_le]
    intro r hr s hs
    obtain ⟨x, y, rfl⟩ := Ideal.mem_span_pair.1 hr
    obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.1 hs
    refine Ideal.mem_span_pair.2 ⟨x * u, x * a ^ K * v + y * (u * a + v * b), ?_⟩
    ring

omit hp in
theorem idealJ_one_pow_le (K : ℕ) (φ : ℤ[X]) : idealJ p 1 φ ^ K ≤ idealJ p K φ := by
  have := span_pair_pow_le (C (p : ℤ)) φ K
  rw [idealJ, idealJ, pow_one, C_pow]
  exact this

omit hp in
theorem idealJ_mono {K K' : ℕ} (h : K ≤ K') (φ : ℤ[X]) : idealJ p K' φ ≤ idealJ p K φ := by
  rw [idealJ, Ideal.span_le]
  rintro x (rfl | rfl)
  · rw [← Nat.add_sub_cancel' h, pow_add, C_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

theorem pow_sub_mem_of_sq_sub_mem {J : Ideal ℤ[X]} {x : ℤ[X]} (hx : x ^ 2 - x ∈ J) :
    ∀ m, 1 ≤ m → x ^ m - x ∈ J := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · simp
    · have := ih hm'
      have h2 : x ^ (m + 1) - x = x * (x ^ m - x) + (x ^ 2 - x) := by ring
      rw [h2]
      exact J.add_mem (J.mul_mem_left _ this) hx

omit hp in
theorem mem_idealJ_of_mem_one {K : ℕ} (hK : 1 ≤ K) {φ x : ℤ[X]} (hx1 : x ∈ idealJ p 1 φ)
    (hx : x ^ 2 - x ∈ idealJ p K φ) : x ∈ idealJ p K φ := by
  have h1 := pow_sub_mem_of_sq_sub_mem hx K hK
  have h2 : x ^ K ∈ idealJ p K φ := idealJ_one_pow_le K φ (Ideal.pow_mem_pow hx1 K)
  have : x = x ^ K - (x ^ K - x) := by ring
  rw [this]
  exact (idealJ p K φ).sub_mem h2 h1

theorem pow_mem_span_pow {a b x : ℤ[X]} (hx : x ∈ Ideal.span {a, b}) {k : ℕ} (hk : 1 ≤ k) :
    x ^ (2 * k - 1) ∈ Ideal.span {a ^ k, b ^ k} := by
  obtain ⟨r, s, rfl⟩ := Ideal.mem_span_pair.1 hx
  refine Ideal.add_pow_mem_of_pow_mem_of_le _ (m := k) (n := k) ?_ ?_ (by omega)
  · rw [mul_pow]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
  · rw [mul_pow]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

end IntLift

section Idem

variable {p : ℕ} [hp : Fact p.Prime]

noncomputable abbrev redP (p : ℕ) (f : ℤ[X]) : (ZMod p)[X] := f.map (Int.castRingHom (ZMod p))

noncomputable def crtLift (p : ℕ) [Fact p.Prime] (φ : ℤ[X]) (β : (ZMod p)[X]) : ℤ[X] :=
  liftZ p (crtIdem (redP p φ) β)

noncomputable def idemZ (p : ℕ) [Fact p.Prime] (φ : ℤ[X]) (β : (ZMod p)[X]) (K : ℕ) : ℤ[X] :=
  1 - (1 - crtLift p φ β ^ K) ^ K

variable {φ : ℤ[X]} (hφ : φ.Monic)
include hφ

omit hp in
theorem redP_monic : (redP p φ).Monic := hφ.map _

theorem crtLift_sq {β : (ZMod p)[X]} (hβ : β ∈ factorsSet (redP p φ)) :
    crtLift p φ β - crtLift p φ β ^ 2 ∈ idealJ p 1 φ := by
  rw [mem_idealJ_one_iff, crtLift, Polynomial.map_sub, Polynomial.map_pow, map_liftZ, ← dvd_neg,
    neg_sub]
  exact crtIdem_sq (redP_monic hφ) hβ

theorem idemZ_sq {β : (ZMod p)[X]} (hβ : β ∈ factorsSet (redP p φ)) (K : ℕ) :
    idemZ p φ β K ^ 2 - idemZ p φ β K ∈ idealJ p K φ := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hx : (Ideal.Quotient.mk (idealJ p K φ) (crtLift p φ β) -
      Ideal.Quotient.mk (idealJ p K φ) (crtLift p φ β) ^ 2) ^ K = 0 := by
    rw [← map_pow, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact idealJ_one_pow_le K φ (Ideal.pow_mem_pow (crtLift_sq hφ hβ) K)
  have := isIdempotentElem_one_sub_one_sub_pow_pow _ K hx
  simp only [idemZ, map_sub, map_one, map_pow]
  rw [sq, this.eq, sub_self]

theorem idemZ_sub_crtLift {β : (ZMod p)[X]} (hβ : β ∈ factorsSet (redP p φ)) {K : ℕ}
    (hK : 1 ≤ K) : idemZ p φ β K - crtLift p φ β ∈ idealJ p 1 φ := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hx : IsIdempotentElem (Ideal.Quotient.mk (idealJ p 1 φ) (crtLift p φ β)) := by
    rw [IsIdempotentElem, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have h2 : crtLift p φ β * crtLift p φ β - crtLift p φ β =
        -(crtLift p φ β - crtLift p φ β ^ 2) := by ring
    rw [h2]
    exact neg_mem (crtLift_sq hφ hβ)
  simp only [idemZ, map_sub, map_one, map_pow]
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  rw [hx.pow_succ_eq, hx.one_sub.pow_succ_eq]
  ring

theorem liftZ_pow_mul_idemZ {β : (ZMod p)[X]} (hβ : β ∈ factorsSet (redP p φ)) {K : ℕ}
    (hK : 1 ≤ K) :
    liftZ p β ^ (mult (redP p φ) β * K) * idemZ p φ β K ∈ idealJ p K φ := by
  set a := mult (redP p φ) β
  have h1 : liftZ p β ^ a * idemZ p φ β K ∈ idealJ p 1 φ := by
    have h2 : liftZ p β ^ a * crtLift p φ β ∈ idealJ p 1 φ := by
      rw [mem_idealJ_one_iff, Polynomial.map_mul, Polynomial.map_pow, map_liftZ, crtLift,
        map_liftZ]
      exact pow_mult_mul_crtIdem (redP_monic hφ) β
    have h3 := Ideal.mul_mem_left _ (liftZ p β ^ a) (idemZ_sub_crtLift hφ hβ hK)
    have : liftZ p β ^ a * idemZ p φ β K =
        liftZ p β ^ a * crtLift p φ β + liftZ p β ^ a * (idemZ p φ β K - crtLift p φ β) := by ring
    rw [this]
    exact add_mem h2 h3
  have hpow := pow_sub_mem_of_sq_sub_mem (idemZ_sq hφ hβ K) K hK
  have h4 : (liftZ p β ^ a * idemZ p φ β K) ^ K ∈ idealJ p K φ :=
    idealJ_one_pow_le K φ (Ideal.pow_mem_pow h1 K)
  have : liftZ p β ^ (a * K) * idemZ p φ β K = (liftZ p β ^ a * idemZ p φ β K) ^ K -
      liftZ p β ^ (a * K) * (idemZ p φ β K ^ K - idemZ p φ β K) := by
    rw [mul_pow, ← pow_mul]; ring
  rw [this]
  exact sub_mem h4 (Ideal.mul_mem_left _ _ hpow)

theorem idemZ_mul_mem {β β' : (ZMod p)[X]} (hβ : β ∈ factorsSet (redP p φ))
    (hβ' : β' ∈ factorsSet (redP p φ)) (hne : β ≠ β') {K : ℕ} (hK : 1 ≤ K) :
    idemZ p φ β K * idemZ p φ β' K ∈ idealJ p K φ := by
  apply mem_idealJ_of_mem_one hK
  · have h1 : crtLift p φ β * crtLift p φ β' ∈ idealJ p 1 φ := by
      rw [mem_idealJ_one_iff, Polynomial.map_mul, crtLift, crtLift, map_liftZ, map_liftZ]
      exact crtIdem_mul (redP_monic hφ) hne
    have : idemZ p φ β K * idemZ p φ β' K = crtLift p φ β * crtLift p φ β' +
        (idemZ p φ β K - crtLift p φ β) * idemZ p φ β' K +
        crtLift p φ β * (idemZ p φ β' K - crtLift p φ β') := by ring
    rw [this]
    exact add_mem (add_mem h1 (Ideal.mul_mem_right _ _ (idemZ_sub_crtLift hφ hβ hK)))
      (Ideal.mul_mem_left _ _ (idemZ_sub_crtLift hφ hβ' hK))
  · have h1 := idemZ_sq hφ hβ K
    have h2 := idemZ_sq hφ hβ' K
    have : (idemZ p φ β K * idemZ p φ β' K) ^ 2 - idemZ p φ β K * idemZ p φ β' K =
        (idemZ p φ β K ^ 2 - idemZ p φ β K) * idemZ p φ β' K ^ 2 +
        idemZ p φ β K * (idemZ p φ β' K ^ 2 - idemZ p φ β' K) := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem idemZ_sum {K : ℕ} (hK : 1 ≤ K) :
    ∑ β ∈ factorsSet (redP p φ), idemZ p φ β K - 1 ∈ idealJ p K φ := by
  set B := factorsSet (redP p φ)
  let e : B → ℤ[X] ⧸ idealJ p K φ := fun β => Ideal.Quotient.mk _ (idemZ p φ β K)
  have horth : OrthogonalIdempotents e := by
    constructor
    · intro β
      rw [IsIdempotentElem, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
        ← sq]
      exact idemZ_sq hφ β.2 K
    · intro β β' hne
      change Ideal.Quotient.mk _ (idemZ p φ β K) * Ideal.Quotient.mk _ (idemZ p φ β' K) = 0
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact idemZ_mul_mem hφ β.2 β'.2 (fun h => hne (Subtype.ext h)) hK
  have hS := horth.isIdempotentElem_sum (s := Finset.univ)
  have h1 : 1 - ∑ β ∈ B, idemZ p φ β K ∈ idealJ p 1 φ := by
    have h2 : ∑ β ∈ B, crtLift p φ β - 1 ∈ idealJ p 1 φ := by
      rw [mem_idealJ_one_iff, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_one]
      simp only [crtLift, map_liftZ]
      exact crtIdem_sum (redP_monic hφ)
    have h3 : ∑ β ∈ B, (idemZ p φ β K - crtLift p φ β) ∈ idealJ p 1 φ :=
      sum_mem fun β hβ => idemZ_sub_crtLift hφ hβ hK
    have : 1 - ∑ β ∈ B, idemZ p φ β K =
        -(∑ β ∈ B, crtLift p φ β - 1) - ∑ β ∈ B, (idemZ p φ β K - crtLift p φ β) := by
      rw [Finset.sum_sub_distrib]; ring
    rw [this]
    exact sub_mem (neg_mem h2) h3
  have h4 : (1 - ∑ β ∈ B, idemZ p φ β K) ^ 2 - (1 - ∑ β ∈ B, idemZ p φ β K) ∈ idealJ p K φ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hsum : Ideal.Quotient.mk (idealJ p K φ) (∑ β ∈ B, idemZ p φ β K) = ∑ β : B, e β := by
      rw [map_sum]
      exact (Finset.sum_coe_sort B (fun β => Ideal.Quotient.mk (idealJ p K φ) (idemZ p φ β K))).symm
    simp only [map_sub, map_pow, map_one, hsum]
    rw [sq, hS.one_sub.eq, sub_self]
  have := mem_idealJ_of_mem_one hK h1 h4
  rw [← neg_sub]
  exact neg_mem this

theorem one_sub_idemZ_mem_idealM {β : (ZMod p)[X]} (hβ : β ∈ factorsSet (redP p φ)) {K : ℕ}
    (hK : 1 ≤ K) : 1 - idemZ p φ β K ∈ idealM p β := by
  have h1 : 1 - crtLift p φ β ∈ idealM p β := by
    rw [mem_idealM_iff, Polynomial.map_sub, Polynomial.map_one, crtLift, map_liftZ, ← dvd_neg,
      neg_sub]
    exact dvd_crtIdem_sub_one hβ
  have h2 := idealJ_one_le_idealM (dvd_of_mem_factorsSet (redP_monic hφ) hβ)
    (idemZ_sub_crtLift hφ hβ hK)
  have : 1 - idemZ p φ β K = (1 - crtLift p φ β) - (idemZ p φ β K - crtLift p φ β) := by ring
  rw [this]
  exact sub_mem h1 h2

theorem idemZ_mem_idealM_of_ne {β β' : (ZMod p)[X]} (hβ : β ∈ factorsSet (redP p φ))
    (hβ' : β' ∈ factorsSet (redP p φ)) (hne : β ≠ β') {K : ℕ} (hK : 1 ≤ K) :
    idemZ p φ β' K ∈ idealM p β := by
  have h1 : crtLift p φ β' ∈ idealM p β := by
    rw [mem_idealM_iff, crtLift, map_liftZ]
    exact dvd_crtIdem_of_ne hβ hne
  have h2 := idealJ_one_le_idealM (dvd_of_mem_factorsSet (redP_monic hφ) hβ)
    (idemZ_sub_crtLift hφ hβ' hK)
  have : idemZ p φ β' K = crtLift p φ β' + (idemZ p φ β' K - crtLift p φ β') := by ring
  rw [this]
  exact add_mem h1 h2

omit hφ in
theorem mem_of_idem_of_mem_idealM {K : ℕ} {β : (ZMod p)[X]} {x : ℤ[X]}
    (hx : x ^ 2 - x ∈ idealJ p K φ) (hxm : x ∈ idealM p β) {𝔞 : Ideal ℤ[X]}
    (hJ : idealJ p K φ ≤ 𝔞) {k : ℕ} (hk : 1 ≤ k) (hpk : C ((p : ℤ) ^ k) ∈ 𝔞)
    (hβk : liftZ p β ^ k ∈ 𝔞) : x ∈ 𝔞 := by
  have h1 : x ^ (2 * k - 1) ∈ 𝔞 := by
    have := pow_mem_span_pow (a := C (p : ℤ)) (b := liftZ p β) hxm hk
    refine (Ideal.span_le.2 ?_) this
    rintro y (rfl | rfl)
    · rw [← C_pow]; exact hpk
    · exact hβk
  have h2 := pow_sub_mem_of_sq_sub_mem hx (2 * k - 1) (by omega)
  have : x = x ^ (2 * k - 1) - (x ^ (2 * k - 1) - x) := by ring
  rw [this]
  exact sub_mem h1 (hJ h2)

theorem one_sub_idemZ_mem {β : (ZMod p)[X]} (hβ : β ∈ factorsSet (redP p φ)) {K : ℕ}
    (hK : 1 ≤ K) {𝔞 : Ideal ℤ[X]} (hJ : idealJ p K φ ≤ 𝔞) {k : ℕ} (hk : 1 ≤ k)
    (hpk : C ((p : ℤ) ^ k) ∈ 𝔞) (hβk : liftZ p β ^ k ∈ 𝔞) : 1 - idemZ p φ β K ∈ 𝔞 := by
  refine mem_of_idem_of_mem_idealM ?_ (one_sub_idemZ_mem_idealM hφ hβ hK) hJ hk hpk hβk
  have h := idemZ_sq hφ hβ K
  have : (1 - idemZ p φ β K) ^ 2 - (1 - idemZ p φ β K) = idemZ p φ β K ^ 2 - idemZ p φ β K := by
    ring
  rw [this]
  exact h

theorem idemZ_mem_of_ne {β β' : (ZMod p)[X]} (hβ : β ∈ factorsSet (redP p φ))
    (hβ' : β' ∈ factorsSet (redP p φ)) (hne : β ≠ β') {K : ℕ} (hK : 1 ≤ K) {𝔞 : Ideal ℤ[X]}
    (hJ : idealJ p K φ ≤ 𝔞) {k : ℕ} (hk : 1 ≤ k) (hpk : C ((p : ℤ) ^ k) ∈ 𝔞)
    (hβk : liftZ p β ^ k ∈ 𝔞) : idemZ p φ β' K ∈ 𝔞 :=
  mem_of_idem_of_mem_idealM (idemZ_sq hφ hβ' K) (idemZ_mem_idealM_of_ne hφ hβ hβ' hne hK) hJ hk
    hpk hβk

end Idem

end DGS
