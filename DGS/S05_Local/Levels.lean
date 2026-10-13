module

public import DGS.S05_Local.LocalParts
public import DGS.S03_Prelim.LocalFailures
public import DGS.S03_Prelim.SimpleSubmodules

@[expose] public section

open Matrix Polynomial

namespace DGS

variable {n : ℕ}

theorem isIntegralMul_iff_smul_le {ℓ : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} :
    IsIntegralMul ℓ Q ↔ ∀ y ∈ latOf Q, (ℓ : ℤ) • y ∈ latZ n := by
  constructor
  · intro h y hy
    obtain ⟨c, rfl⟩ := mem_latOf.1 hy
    rw [mem_latZ_iff]
    intro i
    choose z hz using h
    refine ⟨∑ j, z i j * c j, ?_⟩
    simp only [Pi.smul_apply, mulVec, dotProduct, intVec, zsmul_eq_mul, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hz i j]; ring
  · intro h i j
    have := h (Q *ᵥ intVec (Pi.single j 1)) (mem_latOf.2 ⟨_, rfl⟩)
    obtain ⟨k, hk⟩ := (mem_latZ_iff.1 this) i
    refine ⟨k, ?_⟩
    rw [← hk]
    simp [mulVec, dotProduct, intVec, Pi.single_apply, zsmul_eq_mul]

theorem level_dvd {Q : Matrix (Fin n) (Fin n) ℚ} {ℓ : ℕ} (hℓ : 0 < ℓ) (h : IsIntegralMul ℓ Q) :
    level Q ∣ ℓ := by
  have hg : 0 < Nat.gcd (level Q) ℓ := Nat.gcd_pos_of_pos_right _ hℓ
  have hgI : IsIntegralMul (Nat.gcd (level Q) ℓ) Q := by
    intro i j
    obtain ⟨a, ha⟩ := isIntegralMul_level Q i j
    obtain ⟨b, hb⟩ := h i j
    refine ⟨Nat.gcdA (level Q) ℓ * a + Nat.gcdB (level Q) ℓ * b, ?_⟩
    have h1 := Nat.gcd_eq_gcd_ab (level Q) ℓ
    have hq : ((Nat.gcd (level Q) ℓ : ℕ) : ℚ) = (level Q : ℚ) * (Nat.gcdA (level Q) ℓ : ℚ) +
        (ℓ : ℚ) * (Nat.gcdB (level Q) ℓ : ℚ) := by exact_mod_cast h1
    rw [hq]; push_cast; rw [← ha, ← hb]; ring
  have hle : level Q ≤ Nat.gcd (level Q) ℓ := level_le hg hgI
  have hge : Nat.gcd (level Q) ℓ ≤ level Q := Nat.le_of_dvd (level_pos Q) (Nat.gcd_dvd_left _ _)
  have : Nat.gcd (level Q) ℓ = level Q := le_antisymm hge hle
  rw [← this]; exact Nat.gcd_dvd_right _ _

theorem mem_of_isCoprime_smul_mem {L : Submodule ℤ (Fin n → ℚ)} {v : Fin n → ℚ} {a b : ℤ}
    (hab : IsCoprime a b) (ha : a • v ∈ L) (hb : b • v ∈ L) : v ∈ L := by
  obtain ⟨u, w, huw⟩ := hab
  have : v = u • (a • v) + w • (b • v) := by
    rw [smul_smul, smul_smul, ← add_smul, huw, one_smul]
  rw [this]
  exact add_mem (L.smul_mem u ha) (L.smul_mem w hb)

open Classical in
noncomputable def Fset (A : Matrix (Fin n) (Fin n) ℤ) (Q : Matrix (Fin n) (Fin n) ℚ) (p : ℕ)
    [Fact p.Prime] : Finset (ZMod p)[X] :=
  (factorsSet (redP p A.charpoly)).filter fun β => mPart A p β (latOf Q) ≠ mPart A p β (latZ n)

theorem mem_Fset {A : Matrix (Fin n) (Fin n) ℤ} {Q : Matrix (Fin n) (Fin n) ℚ} {p : ℕ}
    [Fact p.Prime] {β : (ZMod p)[X]} :
    β ∈ Fset A Q p ↔ β ∈ factorsSet (redP p A.charpoly) ∧
      mPart A p β (latOf Q) ≠ mPart A p β (latZ n) := by
  classical
  rw [Fset, Finset.mem_filter]

noncomputable def lastInvFactor (A : Matrix (Fin n) (Fin n) ℤ) : ℕ := level (toQ (walkMatrix A))⁻¹

section PropI

variable {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0)
  {p : ℕ} [hp : Fact p.Prime]

include hn hW in
theorem exists_pPart_decomp (p : ℕ) [Fact p.Prime] :
    ∃ (c : ℤ) (N' : ℕ), Nat.Coprime p N' ∧ ∀ w ∈ latDual (latC A),
      C ((p : ℤ) ^ Kexp A) ∈ annC A (c • w) ∧ ((N' : ℤ) * (1 - c)) • w ∈ latC A := by
  have hN0 : Kexp A ≠ 0 := pow_ne_zero 2 (Int.natAbs_ne_zero.2 hW)
  obtain ⟨j, N', c, hjN, hcop, ⟨s, hs⟩, ⟨t, ht⟩⟩ := exists_split p hN0
  refine ⟨c, N', hcop, fun w hw => ⟨?_, ?_⟩⟩
  · have hNw := card_smul_mem_latC hn hW hw
    have hcw : c • w ∈ latDual (latC A) := Submodule.smul_mem _ c hw
    refine C_pow_card_mem_annC hn hW hcw (k := j) ?_
    rw [C_mem_annC, smul_smul, hs]
    have : (p : ℤ) ^ j * ((N' : ℤ) * s) = s * ((Kexp A : ℕ) : ℤ) := by rw [← hjN]; push_cast; ring
    rw [this, ← smul_smul]
    exact Submodule.smul_mem _ s hNw
  · rw [ht]
    have : (N' : ℤ) * ((p : ℤ) ^ j * t) = t * ((Kexp A : ℕ) : ℤ) := by rw [← hjN]; push_cast; ring
    rw [this, ← smul_smul]
    exact Submodule.smul_mem _ t (card_smul_mem_latC hn hW hw)

include hA hn hW in
theorem levellocal_i_b {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : IsMateMatrix A Q) (k : ℕ)
    (hk : ∀ β ∈ Fset A Q p, ∀ y ∈ mPart A p β (latZ n), ((p : ℤ) ^ k) • y ∈ latC A) :
    (level Q).factorization p ≤ k := by
  obtain ⟨hΛ, hΛu, hCΛ, hΛC⟩ := lem_ideals hn hQ
  have hZ := lem_ideals hn (isMateMatrix_one A)
  rw [latOf_one] at hZ
  obtain ⟨hZst, hZu, hCZ, hZC⟩ := hZ
  set ℓ := level Q with hℓ
  have hℓ0 : ℓ ≠ 0 := (level_pos Q).ne'
  set s := ℓ.factorization p
  set ℓ'' := ordCompl[p] ℓ
  have hℓfac : p ^ s * ℓ'' = ℓ := Nat.ordProj_mul_ordCompl_eq_self ℓ p
  have hcop'' : Nat.Coprime p ℓ'' := Nat.coprime_ordCompl hp.out hℓ0
  have hℓ''pos : 0 < ℓ'' := Nat.pos_of_ne_zero (fun h => hℓ0 (by rw [← hℓfac, h, mul_zero]))
  obtain ⟨c, N', hcopN, hdec⟩ := exists_pPart_decomp hn hW (A := A) p
  have hK := one_le_Kexp hW
  have hint : IsIntegralMul (p ^ k * ℓ'') Q := by
    rw [isIntegralMul_iff_smul_le]
    intro y hy
    set w := (ℓ'' : ℤ) • y with hwdef
    have hwΛ : w ∈ latOf Q := Submodule.smul_mem _ _ hy
    have hwC : w ∈ latDual (latC A) := hΛC hwΛ
    have hpw : ((p : ℤ) ^ s) • w ∈ latZ n := by
      rw [hwdef, smul_smul]
      have : ((p : ℤ) ^ s * (ℓ'' : ℤ)) = ((ℓ : ℕ) : ℤ) := by rw [← hℓfac]; push_cast; ring
      rw [this]
      exact isIntegralMul_iff_smul_le.1 (isIntegralMul_level Q) y hy
    obtain ⟨hwpK, hw'N⟩ := hdec w hwC
    have hw' : (1 - c) • w ∈ latZ n := by
      refine mem_of_isCoprime_smul_mem (a := (p : ℤ) ^ s) (b := (N' : ℤ)) ?_ ?_ ?_
      · exact Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left s hcopN) |>.of_isCoprime_of_dvd_left
          (by push_cast; exact dvd_rfl)
      · rw [smul_comm]; exact Submodule.smul_mem _ _ hpw
      · rw [smul_smul]; exact hCZ hw'N
    set wp := c • w
    have hwpΛ : wp ∈ latOf Q := Submodule.smul_mem _ c hwΛ
    have hsum := sum_actZ_idemZ_sub_mem (A := A) (p := p) hK hwpK
    have hparts : ∀ β ∈ factorsSet (redP p A.charpoly),
        ((p : ℤ) ^ k) • (actZ A (idemZ p A.charpoly β (Kexp A)) *ᵥ wp) ∈ latZ n := by
      intro β hβ
      have hu := actZ_idemZ_mem_mPart hβ hK hΛ hwpΛ hwpK
      by_cases hF : β ∈ Fset A Q p
      · refine mem_of_forall_dot_mPart hA hn hW hβ hZst hZu hCZ ?_ fun z hz => ?_
        · exact Submodule.smul_mem _ _ (mPart_mono hΛC hu)
        · rw [smul_dotProduct, ← dotProduct_smul]
          exact isIntQ_of_mem_latDual (hΛC hu.1) (hk β hF z hz)
      · have heq : mPart A p β (latOf Q) = mPart A p β (latZ n) := by
          by_contra hne; exact hF (mem_Fset.2 ⟨hβ, hne⟩)
        rw [heq] at hu
        exact Submodule.smul_mem _ _ hu.1
    have hsplit : (((p ^ k * ℓ'' : ℕ) : ℤ)) • y = ((p : ℤ) ^ k) • ((1 - c) • w) +
        (∑ β ∈ factorsSet (redP p A.charpoly),
          ((p : ℤ) ^ k) • (actZ A (idemZ p A.charpoly β (Kexp A)) *ᵥ wp) -
        ((p : ℤ) ^ k) • (∑ β ∈ factorsSet (redP p A.charpoly),
          actZ A (idemZ p A.charpoly β (Kexp A)) *ᵥ wp - wp)) := by
      rw [← Finset.smul_sum, ← smul_sub, sub_sub_cancel, ← smul_add, ← add_smul, sub_add_cancel,
        one_smul, hwdef, smul_smul]
      push_cast; ring_nf
    rw [hsplit]
    refine add_mem (Submodule.smul_mem _ _ hw') (sub_mem (sum_mem hparts) ?_)
    exact Submodule.smul_mem _ _ (hCZ hsum)
  have hdvd := level_dvd (Nat.mul_pos (pow_pos hp.out.pos k) hℓ''pos) hint
  have hps : p ^ s ∣ p ^ k * ℓ'' := (Dvd.intro _ hℓfac).trans hdvd
  have hps' : p ^ s ∣ p ^ k := (Nat.Coprime.pow_left s hcop'').dvd_of_dvd_mul_right hps
  exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 hps'

include hA hn hW in
theorem levellocal_i_a {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : IsMateMatrix A Q) :
    p ∣ level Q ↔ (Fset A Q p).Nonempty := by
  obtain ⟨hΛ, hΛu, hCΛ, hΛC⟩ := lem_ideals hn hQ
  have hZ := lem_ideals hn (isMateMatrix_one A)
  rw [latOf_one] at hZ
  obtain ⟨hZst, hZu, hCZ, hZC⟩ := hZ
  constructor
  · intro hdvd
    by_contra hF
    rw [Finset.not_nonempty_iff_eq_empty] at hF
    have h0 := levellocal_i_b hA hn hW (p := p) hQ 0 (by simp [hF])
    have := (hp.out.dvd_iff_one_le_factorization (level_pos Q).ne').1 hdvd
    omega
  · rintro ⟨β, hβ⟩
    obtain ⟨hβf, hne⟩ := mem_Fset.1 hβ
    have hnle : ¬ mPart A p β (latOf Q) ≤ mPart A p β (latZ n) := fun hle =>
      hne (mPart_eq_of_le hA hn hW hβf hΛ hΛu hCΛ hZu hCZ hle)
    obtain ⟨y, hy, hyn⟩ := Set.not_subset.1 hnle
    have hyZ : y ∉ latZ n := fun h => hyn ⟨h, hy.2⟩
    by_contra hpℓ
    apply hyZ
    obtain ⟨hyΛ, k, hk1, -⟩ := hy
    refine mem_of_isCoprime_smul_mem (a := ((level Q : ℕ) : ℤ)) (b := (p : ℤ) ^ k) ?_ ?_ ?_
    · refine Nat.isCoprime_iff_coprime.2 ?_ |>.of_isCoprime_of_dvd_right (by exact dvd_rfl)
      exact Nat.Coprime.pow_right k ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2
        hpℓ)))
    · exact isIntegralMul_iff_smul_le.1 (isIntegralMul_level Q) y hyΛ
    · exact hCZ (C_mem_annC.1 hk1)

theorem levellocal_i_c (β : (ZMod p)[X]) {y : Fin n → ℚ} (hy : y ∈ mPart A p β (latZ n))
    (hW : (walkMatrix A).det ≠ 0) :
    ((p : ℤ) ^ (lastInvFactor A).factorization p) • y ∈ latC A := by
  have hWq : (toQ (walkMatrix A)).det ≠ 0 := by rw [det_toQ]; exact_mod_cast hW
  have hWu : IsUnit (toQ (walkMatrix A)).det := isUnit_iff_ne_zero.2 hWq
  set d := lastInvFactor A
  have hd0 : 0 < d := level_pos _
  have hdy : C (d : ℤ) ∈ annC A y := by
    rw [C_mem_annC]
    have h1 := isIntegralMul_iff_smul_le.1 (isIntegralMul_level (toQ (walkMatrix A))⁻¹)
      ((toQ (walkMatrix A))⁻¹ *ᵥ y) (mem_latOf.2 ?_)
    · obtain ⟨c', hc'⟩ := h1
      rw [latC, mem_latOf]
      refine ⟨c', ?_⟩
      rw [← hc', mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ hWu, one_mulVec]
      rfl
    · obtain ⟨c, hc⟩ := hy.1
      exact ⟨c, by rw [hc]⟩
  obtain ⟨-, k, hk1, -⟩ := hy
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).1 (Nat.gcd_dvd_left (p ^ k) d)
  have hg : C (((Nat.gcd (p ^ k) d : ℕ) : ℤ)) ∈ annC A y := by
    rw [Nat.gcd_eq_gcd_ab, C_add, C_mul, C_mul]
    push_cast
    exact add_mem (Ideal.mul_mem_right _ _ hk1) (Ideal.mul_mem_right _ _ hdy)
  rw [hi] at hg
  have hile : i ≤ d.factorization p := by
    rw [← hp.out.pow_dvd_iff_le_factorization hd0.ne']
    rw [← hi]; exact Nat.gcd_dvd_right _ _
  rw [← C_mem_annC]
  have : (p : ℤ) ^ d.factorization p = (p : ℤ) ^ (d.factorization p - i) * ((p ^ i : ℕ) : ℤ) := by
    push_cast; rw [← pow_add, Nat.sub_add_cancel hile]
  rw [this, C_mul]
  exact Ideal.mul_mem_left _ _ hg

end PropI

section MaxIdeal

variable {p : ℕ} [hp : Fact p.Prime]

theorem idealM_eq_ker (β : (ZMod p)[X]) :
    idealM p β = RingHom.ker ((AdjoinRoot.mk β).comp (mapRingHom (Int.castRingHom (ZMod p)))) := by
  ext f
  rw [mem_idealM_iff, RingHom.mem_ker, RingHom.comp_apply, coe_mapRingHom, AdjoinRoot.mk_eq_zero]

theorem idealM_isMaximal {β : (ZMod p)[X]} (hβ : Irreducible β) : (idealM p β).IsMaximal := by
  have := Fact.mk hβ
  rw [idealM_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _
    (AdjoinRoot.mk_surjective.comp (map_surjective _ (ZMod.ringHom_surjective _)))

end MaxIdeal

section TTparts

variable (A : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) [hp : Fact p.Prime] (β : (ZMod p)[X])

noncomputable def JT : Ideal ℤ[X] where
  carrier := {f | ∃ k, C ((p : ℤ) ^ k) * f ∈ idealT A ∧ liftZ p β ^ k * f ∈ idealT A}
  add_mem' := by
    rintro f g ⟨k, hk1, hk2⟩ ⟨l, hl1, hl2⟩
    refine ⟨k + l, ?_, ?_⟩
    · rw [pow_add, C_mul, mul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm (C _) (C _), mul_assoc]; exact Ideal.mul_mem_left _ _ hk1
      · rw [mul_assoc]; exact Ideal.mul_mem_left _ _ hl1
    · rw [pow_add, mul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm (liftZ p β ^ k), mul_assoc]; exact Ideal.mul_mem_left _ _ hk2
      · rw [mul_assoc]; exact Ideal.mul_mem_left _ _ hl2
  zero_mem' := ⟨0, by simp, by simp⟩
  smul_mem' := by
    rintro c f ⟨k, hk1, hk2⟩
    refine ⟨k, ?_, ?_⟩
    · rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hk1
    · rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hk2

noncomputable def TTpart : Ideal (TT A) := (JT A p β).map (Ideal.Quotient.mk (idealT A))

def IsChainComponent : Prop :=
  ∀ 𝔄 𝔅 : Ideal (TT A), 𝔄 ≤ TTpart A p β → 𝔅 ≤ TTpart A p β → 𝔄 ≤ 𝔅 ∨ 𝔅 ≤ 𝔄

variable {A p β}

theorem idealT_le_JT : idealT A ≤ JT A p β := fun f hf => ⟨0, by simpa using hf, by simpa using hf⟩

variable (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0)
include hA hn hW

theorem PhiHat_mem_latC_iff' (f : ℤ[X]) : PhiHat A f ∈ latC A ↔ f ∈ idealT A :=
  PhiHat_mem_latC_iff hA hn hW f

theorem PhiHat_mem_mPart_iff (f : ℤ[X]) :
    PhiHat A f ∈ mPart A p β (latDual (latC A)) ↔ f ∈ JT A p β := by
  have hmem : PhiHat A f ∈ latDual (latC A) :=
    (mem_latDual_latC_iff_PhiHat hA hn hW _).2 ⟨f, rfl⟩
  constructor
  · rintro ⟨-, k, hk1, hk2⟩
    refine ⟨k, ?_, ?_⟩
    · rw [← PhiHat_mem_latC_iff' hA hn hW, PhiHat_mul]; exact hk1
    · rw [← PhiHat_mem_latC_iff' hA hn hW, PhiHat_mul]; exact hk2
  · rintro ⟨k, hk1, hk2⟩
    refine ⟨hmem, k, ?_, ?_⟩
    · rw [mem_annC]
      have := (PhiHat_mem_latC_iff' hA hn hW _).2 hk1
      rwa [PhiHat_mul] at this
    · rw [mem_annC]
      have := (PhiHat_mem_latC_iff' hA hn hW _).2 hk2
      rwa [PhiHat_mul] at this

omit hA hn hW in
noncomputable def idealOfLat {L : Submodule ℤ (Fin n → ℚ)} (hL : IsAStable A L) : Ideal ℤ[X] where
  carrier := {f | PhiHat A f ∈ mPart A p β L}
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_ofPred_eq, PhiHat_add] at *
    exact add_mem hf hg
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    have : PhiHat A 0 = 0 := by simp [PhiHat, iotaQ]
    rw [this]; exact zero_mem _
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_ofPred_eq, smul_eq_mul, PhiHat_mul] at *
    exact actZ_mulVec_mem_mPart hL c hf

theorem idealOfLat_le_JT {L : Submodule ℤ (Fin n → ℚ)} (hL : IsAStable A L)
    (hLC : L ≤ latDual (latC A)) : idealOfLat (p := p) (β := β) hL ≤ JT A p β := fun f hf =>
  (PhiHat_mem_mPart_iff hA hn hW f).1 (mPart_mono hLC hf)

theorem idealT_le_idealOfLat {L : Submodule ℤ (Fin n → ℚ)} (hL : IsAStable A L)
    (hCL : latC A ≤ L) : idealT A ≤ idealOfLat (p := p) (β := β) hL := fun f hf =>
  latC_le_mPart hCL ((PhiHat_mem_latC_iff' hA hn hW f).2 hf)

theorem idealOfLat_le_iff {L L' : Submodule ℤ (Fin n → ℚ)} (hL : IsAStable A L)
    (hL' : IsAStable A L') (hLC : L ≤ latDual (latC A)) :
    idealOfLat (p := p) (β := β) hL ≤ idealOfLat (p := p) (β := β) hL' ↔
      mPart A p β L ≤ mPart A p β L' := by
  constructor
  · intro h y hy
    obtain ⟨f, rfl⟩ := (mem_latDual_latC_iff_PhiHat hA hn hW y).1 (hLC hy.1)
    exact h hy
  · intro h f hf
    exact h hf

theorem levellocal_ii {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : IsMateMatrix A Q) (hβ : β ∈ Fset A Q p) :
    (¬ mPart A p β (latOf Q) ≤ mPart A p β (latZ n) ∧
      ¬ mPart A p β (latZ n) ≤ mPart A p β (latOf Q)) ∧
    ¬ IsChainComponent A p β ∧ ¬ mPart A p β (latZ n) ≤ latC A := by
  obtain ⟨hΛ, hΛu, hCΛ, hΛC⟩ := lem_ideals hn hQ
  have hZ := lem_ideals hn (isMateMatrix_one A)
  rw [latOf_one] at hZ
  obtain ⟨hZst, hZu, hCZ, hZC⟩ := hZ
  obtain ⟨hβf, hne⟩ := mem_Fset.1 hβ
  have h1 : ¬ mPart A p β (latOf Q) ≤ mPart A p β (latZ n) := fun hle =>
    hne (mPart_eq_of_le hA hn hW hβf hΛ hΛu hCΛ hZu hCZ hle)
  have h2 : ¬ mPart A p β (latZ n) ≤ mPart A p β (latOf Q) := fun hle =>
    hne (mPart_eq_of_le hA hn hW hβf hZst hZu hCZ hΛu hCΛ hle).symm
  refine ⟨⟨h1, h2⟩, ?_, ?_⟩
  · intro hchain
    have hle1 := Ideal.map_mono (f := Ideal.Quotient.mk (idealT A))
      (idealOfLat_le_JT hA hn hW (p := p) (β := β) hΛ hΛC)
    have hle2 := Ideal.map_mono (f := Ideal.Quotient.mk (idealT A))
      (idealOfLat_le_JT hA hn hW (p := p) (β := β) hZst hZC)
    rcases hchain _ _ hle1 hle2 with h | h
    · have h' := Ideal.comap_mono (f := Ideal.Quotient.mk (idealT A)) h
      rw [Ideal.comap_map_mk (idealT_le_idealOfLat hA hn hW hΛ hCΛ),
        Ideal.comap_map_mk (idealT_le_idealOfLat hA hn hW hZst hCZ)] at h'
      exact h1 ((idealOfLat_le_iff hA hn hW hΛ hZst hΛC).1 h')
    · have h' := Ideal.comap_mono (f := Ideal.Quotient.mk (idealT A)) h
      rw [Ideal.comap_map_mk (idealT_le_idealOfLat hA hn hW hΛ hCΛ),
        Ideal.comap_map_mk (idealT_le_idealOfLat hA hn hW hZst hCZ)] at h'
      exact h2 ((idealOfLat_le_iff hA hn hW hZst hΛ hZC).1 h')
  · intro hle
    exact h2 (hle.trans (latC_le_mPart hCΛ))

end TTparts

section Reduction

def redVec (p : ℕ) (c : Fin n → ℤ) : Fin n → ZMod p := fun i => (c i : ZMod p)

variable {p : ℕ}

theorem redVec_mulVec (M : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℤ) :
    redVec p (M *ᵥ c) = modP p M *ᵥ redVec p c := by
  funext i; simp [redVec, modP, mulVec, dotProduct]

theorem redVec_dotProduct (c d : Fin n → ℤ) :
    redVec p c ⬝ᵥ redVec p d = ((c ⬝ᵥ d : ℤ) : ZMod p) := by
  simp [redVec, dotProduct]

theorem ones_dotProduct_redVec (c : Fin n → ℤ) :
    ones n (ZMod p) ⬝ᵥ redVec p c = ((ones n ℤ ⬝ᵥ c : ℤ) : ZMod p) := by
  simp [redVec, dotProduct, ones]

theorem redVec_eq_zero_iff [NeZero p] (c : Fin n → ℤ) : redVec p c = 0 ↔ ∀ i, (p : ℤ) ∣ c i := by
  constructor
  · intro h i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun h i)
  · intro h
    funext i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (h i)

theorem aeval_map_map {S : Type*} [CommRing S] (f : ℤ →+* S) (A : Matrix (Fin n) (Fin n) ℤ)
    (g : ℤ[X]) : aeval (A.map f) (g.map f) = (aeval A g).map f := by
  have h1 : f = algebraMap ℤ S := RingHom.ext_int _ _
  have h2 : aeval (A.map f) (g.map f) = aeval (A.map f) g := by
    rw [h1, Polynomial.aeval_map_algebraMap]
  rw [h2]
  exact Polynomial.aeval_algHom_apply (f.mapMatrix.toIntAlgHom) A g

theorem actZ_mulVec_intVec (A : Matrix (Fin n) (Fin n) ℤ) (g : ℤ[X]) (c : Fin n → ℤ) :
    actZ A g *ᵥ intVec c = intVec (aeval A g *ᵥ c) := by
  rw [actZ, toQ, aeval_map_map, ← toQ, mulVec_intVec]

theorem redVec_aeval_mulVec (A : Matrix (Fin n) (Fin n) ℤ) (g : ℤ[X]) (c : Fin n → ℤ) :
    redVec p (aeval A g *ᵥ c) = aeval (modP p A) (g.map (Int.castRingHom (ZMod p))) *ᵥ redVec p c := by
  rw [redVec_mulVec, modP, modP, aeval_map_map]

end Reduction

section PropIII

variable {A : Matrix (Fin n) (Fin n) ℤ} {p : ℕ} [hp : Fact p.Prime] {β : (ZMod p)[X]}
  (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0)
include hA hn hW

omit hA hn hW in
theorem hasType_of_le_ker_pow {F : Type*} [Field F] {m : ℕ} {M : Matrix (Fin m) (Fin m) F}
    {U : Submodule F (Fin m → F)} (hU : IsSimpleInvariant M U) {γ : F[X]} (hγm : γ.Monic)
    (hγi : Irreducible γ) {R : ℕ} (hR : ∀ u ∈ U, aeval M (γ ^ R) *ᵥ u = 0) : HasType M U γ := by
  refine ⟨hγm, hγi, ?_⟩
  let W : Submodule F (Fin m → F) := U ⊓ LinearMap.ker (aeval M γ).mulVecLin
  have hWinv : IsInvariant M W := by
    intro x hx
    refine ⟨hU.1 x hx.1, ?_⟩
    have hx2 : aeval M γ *ᵥ x = 0 := hx.2
    show (aeval M γ).mulVecLin (M *ᵥ x) = 0
    rw [mulVecLin_apply, mulVec_mulVec, aeval_mul_comm, ← mulVec_mulVec, hx2, mulVec_zero]
  rcases hU.2.2 W hWinv inf_le_left with hW0 | hWU
  · exfalso
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.2.1
    have key : ∀ k, aeval M (γ ^ k) *ᵥ u ∈ U ∧ aeval M (γ ^ k) *ᵥ u ≠ 0 := by
      intro k
      induction k with
      | zero => simpa using ⟨huU, hu0⟩
      | succ k ih =>
        have hmem : aeval M (γ ^ (k + 1)) *ᵥ u = aeval M γ *ᵥ (aeval M (γ ^ k) *ᵥ u) := by
          rw [mulVec_mulVec, ← map_mul, pow_succ, mul_comm]
        rw [hmem]
        refine ⟨isInvariant_aeval hU.1 γ _ ih.1, fun h0 => ih.2 ?_⟩
        have : aeval M (γ ^ k) *ᵥ u ∈ W := ⟨ih.1, h0⟩
        rw [hW0] at this
        exact this
    exact (key R).2 (hR u huU)
  · intro x hx
    have : x ∈ W := hWU ▸ hx
    exact this.2

theorem levellocal_iii {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : IsMateMatrix A Q) (hβ : β ∈ Fset A Q p) :
    ∃ U : Submodule (ZMod p) (Fin n → ZMod p), IsSimpleInvariant (modP p A) U ∧
      HasType (modP p A) U β ∧ IsTotallyIsotropic U ∧ ∀ u ∈ U, ones n (ZMod p) ⬝ᵥ u = 0 := by
  classical
  obtain ⟨hΛ, hΛu, hCΛ, hΛC⟩ := lem_ideals hn hQ
  have hZ := lem_ideals hn (isMateMatrix_one A)
  rw [latOf_one] at hZ
  obtain ⟨hZst, hZu, hCZ, hZC⟩ := hZ
  obtain ⟨hβf, hne⟩ := mem_Fset.1 hβ
  have hK := one_le_Kexp hW
  set X := mPart A p β (latOf Q) with hXdef
  have hXK : ∀ y ∈ X, C ((p : ℤ) ^ Kexp A) ∈ annC A y := fun y hy =>
    C_pow_card_mem_annC_of_mPart hn hW (mPart_mono hΛC hy)
  set R := mult (redP p A.charpoly) β * Kexp A
  have hXR : ∀ y ∈ X, liftZ p β ^ R ∈ annC A y := by
    intro y hy
    have h1 := actZ_idemZ_sub_mem hβf hK hy (hXK y hy)
    have h2 : 1 - idemZ p A.charpoly β (Kexp A) ∈ annC A y := by
      rw [mem_annC, actZ_sub, actZ_one, sub_mulVec, one_mulVec]; exact h1
    have h3 := idealJ_le_annC (hXK y hy) (liftZ_pow_mul_idemZ (charpoly_monic A) hβf hK)
    have : liftZ p β ^ R = liftZ p β ^ R * (1 - idemZ p A.charpoly β (Kexp A)) +
        liftZ p β ^ R * idemZ p A.charpoly β (Kexp A) := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ h2) h3
  have hP : ∃ s, ∀ y ∈ X, ((p : ℤ) ^ s) • y ∈ latZ n :=
    ⟨Kexp A, fun y hy => hCZ (C_mem_annC.1 (hXK y hy))⟩
  set s := Nat.find hP with hsdef
  have hs : ∀ y ∈ X, ((p : ℤ) ^ s) • y ∈ latZ n := Nat.find_spec hP
  have hs0 : s ≠ 0 := by
    intro h0
    have hle : X ≤ mPart A p β (latZ n) := fun y hy => by
      have := hs y hy
      rw [h0, pow_zero, one_smul] at this
      exact ⟨this, hy.2⟩
    exact hne (mPart_eq_of_le hA hn hW hβf hΛ hΛu hCΛ hZu hCZ hle)
  set S : Set (Fin n → ZMod p) :=
    {u | ∃ y ∈ X, ∃ c : Fin n → ℤ, intVec c = ((p : ℤ) ^ s) • y ∧ u = redVec p c} with hSdef
  set U0 := Submodule.span (ZMod p) S
  have hpdvd : ∀ m : ℤ, (p : ℤ) ∣ (p : ℤ) ^ s * m := fun m =>
    Dvd.dvd.mul_right (dvd_pow_self _ hs0) m
  have hg1 : ∀ u ∈ S, modP p A *ᵥ u ∈ S := by
    rintro u ⟨y, hy, c, hc, rfl⟩
    refine ⟨toQ A *ᵥ y, mPart_isAStable hΛ y hy, A *ᵥ c, ?_, (redVec_mulVec A c).symm⟩
    rw [← mulVec_intVec, hc, mulVec_smul]
  have hg2 : ∀ u ∈ S, ∀ v ∈ S, u ⬝ᵥ v = 0 := by
    rintro u ⟨y, hy, c, hc, rfl⟩ v ⟨y', hy', d, hd, rfl⟩
    rw [redVec_dotProduct]
    obtain ⟨m, hm⟩ : IsIntQ (y ⬝ᵥ y') := by
      have : y ∈ latDual (latOf Q) := by rw [hΛu]; exact hy.1
      exact isIntQ_of_mem_latDual this hy'.1
    have hcd : ((c ⬝ᵥ d : ℤ) : ℚ) = (((p : ℤ) ^ s * ((p : ℤ) ^ s * m) : ℤ) : ℚ) := by
      rw [← dotProduct_intVec_intVec, hc, hd, smul_dotProduct, dotProduct_smul, hm, smul_smul,
        zsmul_eq_mul]
      push_cast
      ring
    have hcd' : (c ⬝ᵥ d : ℤ) = (p : ℤ) ^ s * ((p : ℤ) ^ s * m) := by exact_mod_cast hcd
    rw [hcd', (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (hpdvd _)]
  have hg3 : ∀ u ∈ S, ones n (ZMod p) ⬝ᵥ u = 0 := by
    rintro u ⟨y, hy, c, hc, rfl⟩
    rw [ones_dotProduct_redVec]
    obtain ⟨m, hm⟩ : IsIntQ (ones n ℚ ⬝ᵥ y) := by
      have : ones n ℚ ∈ latDual (latOf Q) := by rw [hΛu]; exact mem_latOf_ones hQ.2.1
      exact isIntQ_of_mem_latDual this hy.1
    have h1 : ((ones n ℤ ⬝ᵥ c : ℤ) : ℚ) = (((p : ℤ) ^ s * m : ℤ) : ℚ) := by
      have hones : intVec (ones n ℤ) = ones n ℚ := by funext i; simp [intVec, ones]
      rw [← dotProduct_intVec_intVec, hones, hc, dotProduct_smul, hm, zsmul_eq_mul]
      push_cast
      ring
    have h1' : (ones n ℤ ⬝ᵥ c : ℤ) = (p : ℤ) ^ s * m := by exact_mod_cast h1
    rw [h1', (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (hpdvd _)]
  have hg4 : ∀ u ∈ S, aeval (modP p A) (β ^ R) *ᵥ u = 0 := by
    rintro u ⟨y, hy, c, hc, rfl⟩
    have hβR : β ^ R = (liftZ p β ^ R).map (Int.castRingHom (ZMod p)) := by
      rw [Polynomial.map_pow, map_liftZ]
    rw [hβR, ← redVec_aeval_mulVec, redVec_eq_zero_iff]
    obtain ⟨c'', hc''⟩ := hCZ (hXR y hy)
    have h1 : intVec (aeval A (liftZ p β ^ R) *ᵥ c) = intVec (((p : ℤ) ^ s) • c'') := by
      rw [← actZ_mulVec_intVec, hc, mulVec_smul, hc'', intVec_smul]
    have h2 := intVec_injective h1
    intro i
    rw [h2, Pi.smul_apply, smul_eq_mul]
    exact hpdvd _
  have hg5 : ∃ u ∈ S, u ≠ 0 := by
    have hlt : s - 1 < s := by omega
    have hmin := Nat.find_min hP hlt
    push Not at hmin
    obtain ⟨y, hy, hyn⟩ := hmin
    obtain ⟨c, hc⟩ := hs y hy
    refine ⟨redVec p c, ⟨y, hy, c, hc.symm, rfl⟩, fun h0 => hyn ?_⟩
    rw [redVec_eq_zero_iff] at h0
    choose c' hc' using h0
    refine ⟨c', ?_⟩
    have hps : ((p : ℤ) ^ s) = (p : ℤ) * (p : ℤ) ^ (s - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hs0)]
    have h1 : (p : ℤ) • (((p : ℤ) ^ (s - 1)) • y) = (p : ℤ) • intVec c' := by
      rw [smul_smul, ← hps, hc]
      funext i
      simp [intVec, hc' i]
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    exact smul_right_injective (Fin n → ℚ) hp0 h1
  have hU0inv : IsInvariant (modP p A) U0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hg1 x hx)
    | zero => rw [mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
    | smul a x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ a hx
  have hU0ne : U0 ≠ ⊥ := by
    obtain ⟨u, hu, hu0⟩ := hg5
    intro h
    rw [Submodule.eq_bot_iff] at h
    exact hu0 (h u (Submodule.subset_span hu))
  have hU0iso : IsTotallyIsotropic U0 := by
    have h1 : ∀ u ∈ S, ∀ v ∈ U0, u ⬝ᵥ v = 0 := by
      intro u hu v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact hg2 u hu x hx
      | zero => exact dotProduct_zero _
      | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
      | smul a x _ hx => rw [dotProduct_smul, hx, smul_zero]
    intro u hu v hv
    induction hu using Submodule.span_induction with
    | mem x hx => exact h1 x hx v hv
    | zero => exact zero_dotProduct _
    | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_dotProduct, hx, smul_zero]
  have hU0e : ∀ u ∈ U0, ones n (ZMod p) ⬝ᵥ u = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => exact hg3 x hx
    | zero => exact dotProduct_zero _
    | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
    | smul a x _ hx => rw [dotProduct_smul, hx, smul_zero]
  have hU0R : ∀ u ∈ U0, aeval (modP p A) (β ^ R) *ᵥ u = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => exact hg4 x hx
    | zero => exact mulVec_zero _
    | add x y _ _ hx hy => rw [mulVec_add, hx, hy, add_zero]
    | smul a x _ hx => rw [mulVec_smul, hx, smul_zero]
  obtain ⟨U, hUle, hU⟩ := exists_simpleInvariant_le (modP p A) hU0inv hU0ne
  refine ⟨U, hU, ?_, fun u hu v hv => hU0iso u (hUle hu) v (hUle hv), fun u hu => hU0e u (hUle hu)⟩
  exact hasType_of_le_ker_pow hU (monic_of_mem_factorsSet hβf)
    (irreducible_of_mem_factorsSet hβf) fun u hu => hU0R u (hUle hu)

theorem levellocal_iii_failure {Q : Matrix (Fin n) (Fin n) ℚ} (hQ : IsMateMatrix A Q)
    (hβ : β ∈ Fset A Q p) : IsLocalFailure p β.natDegree A := by
  obtain ⟨U, hU, hβU, hiso, he⟩ := levellocal_iii hA hn hW hQ hβ
  obtain ⟨β', hβ', hdim⟩ := exists_hasType (modP p A) U hU
  rw [hasType_unique (modP p A) U hU hβU hβ']
  exact ⟨U, hU, hdim, hiso, he⟩

end PropIII

section ChainLemma

variable {R : Type*} [CommRing R]

def colonElem (I : Ideal R) (v : R) : Ideal R where
  carrier := {g | g * v ∈ I}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, add_mul] at *
    exact add_mem ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c g hg
    simp only [Set.mem_ofPred_eq, smul_eq_mul, mul_assoc] at *
    exact Ideal.mul_mem_left _ _ hg

theorem mem_colonElem {I : Ideal R} {v g : R} : g ∈ colonElem I v ↔ g * v ∈ I := Iff.rfl

def chainIdeal (I J : Ideal R) (t : R) (i : ℕ) : Ideal R := Ideal.span {t ^ i} * J ⊔ I

theorem mem_chainIdeal {I J : Ideal R} {t x : R} {i : ℕ} :
    x ∈ chainIdeal I J t i ↔ ∃ v ∈ J, ∃ w ∈ I, t ^ i * v + w = x := by
  rw [chainIdeal, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Ideal.mem_span_singleton_mul.1 hy
    exact ⟨v, hv, w, hw, rfl⟩
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact ⟨t ^ i * v, Ideal.mem_span_singleton_mul.2 ⟨v, hv, rfl⟩, w, hw, rfl⟩

theorem chainIdeal_antitone {I J : Ideal R} {t : R} {i j : ℕ} (hij : i ≤ j) :
    chainIdeal I J t j ≤ chainIdeal I J t i := by
  intro x hx
  obtain ⟨v, hv, w, hw, rfl⟩ := mem_chainIdeal.1 hx
  refine mem_chainIdeal.2 ⟨t ^ (j - i) * v, J.mul_mem_left _ hv, w, hw, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hij]

theorem chain_of_principal {I J m : Ideal R} (hm : m.IsMaximal) {t e : R} {N : ℕ} (_hIJ : I ≤ J)
    (hmJ : m * J ⊔ I = Ideal.span {t} * J ⊔ I) (hnil : m ^ N * J ≤ I) (heJ : e ∈ J)
    (he : ∀ v ∈ J, v - e * v ∈ I) :
    ∀ 𝔞 𝔟 : Ideal R, I ≤ 𝔞 → 𝔞 ≤ J → I ≤ 𝔟 → 𝔟 ≤ J → 𝔞 ≤ 𝔟 ∨ 𝔟 ≤ 𝔞 := by
  have htJ : ∀ k, ∀ v ∈ J, t ^ k * v ∈ m ^ k * J ⊔ I := by
    intro k
    induction k with
    | zero =>
      intro v hv
      simp only [pow_zero, one_mul]
      exact Ideal.mem_sup_left hv
    | succ k ih =>
      intro v hv
      have h1 : t * v ∈ m * J ⊔ I := by
        rw [hmJ]; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_mul.2 ⟨v, hv, rfl⟩)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
      have h2 : t ^ (k + 1) * v = t ^ k * a + t ^ k * b := by rw [pow_succ, mul_assoc, ← hab, mul_add]
      rw [h2]
      refine add_mem ?_ (Ideal.mem_sup_right (I.mul_mem_left _ hb))
      have : ∀ a ∈ m * J, t ^ k * a ∈ m ^ (k + 1) * J ⊔ I := by
        intro a ha
        refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
        · have := ih y hy
          obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.1 this
          have h3 : t ^ k * (x * y) = x * c + x * d := by rw [← mul_add, hcd]; ring
          rw [h3]
          refine add_mem (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right (I.mul_mem_left _ hd))
          have : m * (m ^ k * J) ≤ m ^ (k + 1) * J := by rw [pow_succ', mul_assoc]
          exact this (Ideal.mul_mem_mul hx hc)
        · rw [mul_add]; exact add_mem hx hy
      exact this a ha
  have htN : ∀ v ∈ J, t ^ N * v ∈ I := by
    intro v hv
    have := htJ N v hv
    have h : m ^ N * J ⊔ I ≤ I := sup_le hnil le_rfl
    exact h this
  have key : ∀ 𝔞 : Ideal R, I ≤ 𝔞 → 𝔞 ≤ J → ∃ i, 𝔞 = chainIdeal I J t i := by
    intro 𝔞 hI𝔞 h𝔞J
    classical
    by_cases hall : ∀ i, 𝔞 ≤ chainIdeal I J t i
    · refine ⟨N, le_antisymm (hall N) ?_⟩
      intro x hx
      obtain ⟨v, hv, w, hw, rfl⟩ := mem_chainIdeal.1 hx
      exact add_mem (hI𝔞 (htN v hv)) (hI𝔞 hw)
    · push Not at hall
      have hex : ∃ i, ¬ 𝔞 ≤ chainIdeal I J t i := hall
      set i0 := Nat.find hex
      have hi0 : ¬ 𝔞 ≤ chainIdeal I J t i0 := Nat.find_spec hex
      have hi00 : i0 ≠ 0 := by
        intro h0
        apply hi0
        rw [h0]
        intro x hx
        exact mem_chainIdeal.2 ⟨x, h𝔞J hx, 0, zero_mem _, by simp⟩
      obtain ⟨i, hi⟩ : ∃ i, i0 = i + 1 := ⟨i0 - 1, by omega⟩
      have hle : 𝔞 ≤ chainIdeal I J t i := by
        have := Nat.find_min hex (show i < i0 by omega)
        push Not at this
        exact this
      rw [hi] at hi0
      obtain ⟨u, hu𝔞, hun⟩ := Set.not_subset.1 hi0
      obtain ⟨v, hv, w, hw, huvw⟩ := mem_chainIdeal.1 (hle hu𝔞)
      have hvm : v ∉ m := by
        intro hvm
        apply hun
        have h1 : v ∈ m * J ⊔ I := by
          have : v = v * e + (v - e * v) := by ring
          rw [this]
          exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_mul hvm heJ))
            (Ideal.mem_sup_right (he v hv))
        rw [hmJ] at h1
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
        obtain ⟨c, hc, rfl⟩ := Ideal.mem_span_singleton_mul.1 ha
        refine mem_chainIdeal.2 ⟨c, hc, t ^ i * b + w, add_mem (I.mul_mem_left _ hb) hw, ?_⟩
        rw [← huvw, ← hab, pow_succ]; ring
      obtain ⟨a, μ, hμ, haμ⟩ := hm.exists_inv hvm
      have hJv : ∀ x ∈ J, ∃ r, x - r * v ∈ I := by
        intro x hx
        obtain ⟨s, hs⟩ : a * v ∣ (a * v + μ) ^ N - μ ^ N := by
          have := sub_dvd_pow_sub_pow (a * v + μ) μ N
          simpa using this
        refine ⟨s * a * x, ?_⟩
        have h1 : x = (a * v + μ) ^ N * x := by rw [haμ, one_pow, one_mul]
        have h2 : x - s * a * x * v = μ ^ N * x := by
          have := congrArg (· * x) hs
          linear_combination h1 + this
        rw [h2]
        exact hnil (Ideal.mul_mem_mul (Ideal.pow_mem_pow hμ N) hx)
      refine ⟨i, le_antisymm hle fun x hx => ?_⟩
      obtain ⟨v', hv', w', hw', rfl⟩ := mem_chainIdeal.1 hx
      obtain ⟨r, hr⟩ := hJv v' hv'
      have : t ^ i * v' + w' = r * u - r * w + t ^ i * (v' - r * v) + w' := by
        rw [← huvw]; ring
      rw [this]
      refine add_mem (add_mem (sub_mem (𝔞.mul_mem_left _ hu𝔞) (hI𝔞 (I.mul_mem_left _ hw)))
        (hI𝔞 (I.mul_mem_left _ hr))) (hI𝔞 hw')
  intro 𝔞 𝔟 h𝔞I h𝔞J h𝔟I h𝔟J
  obtain ⟨i, rfl⟩ := key 𝔞 h𝔞I h𝔞J
  obtain ⟨j, rfl⟩ := key 𝔟 h𝔟I h𝔟J
  rcases le_total i j with hij | hij
  · exact Or.inr (chainIdeal_antitone hij)
  · exact Or.inl (chainIdeal_antitone hij)

end ChainLemma

section CorChain

variable {A : Matrix (Fin n) (Fin n) ℤ} {p : ℕ} [hp : Fact p.Prime] {β : (ZMod p)[X]}
  (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0)

include hA hn hW in
theorem C_card_mem_idealT : C (((Kexp A : ℕ)) : ℤ) ∈ idealT A := by
  have h := card_nsmul_eq_zero' (G := TT A) (x := 1)
  rw [card_TT hA hn hW, nsmul_eq_mul, mul_one] at h
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast C, map_natCast]
  exact h

theorem idealM_eq_sup (β : (ZMod p)[X]) :
    idealM p β = Ideal.span {C (p : ℤ)} ⊔ Ideal.span {liftZ p β} := by
  rw [idealM, Ideal.span_insert]

theorem idealM_pow_le (k : ℕ) :
    idealM p β ^ (k + k) ≤ Ideal.span {C ((p : ℤ) ^ k)} ⊔ Ideal.span {liftZ p β ^ k} := by
  rw [idealM_eq_sup]
  refine Ideal.sup_pow_add_le_pow_sup_pow.trans ?_
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, C_pow]

theorem mem_colonElem_of_pow {I : Ideal ℤ[X]} {v : ℤ[X]} {k : ℕ}
    (h1 : C ((p : ℤ) ^ k) * v ∈ I) (h2 : liftZ p β ^ k * v ∈ I) :
    idealM p β ^ (k + k) ≤ colonElem I v := by
  refine (idealM_pow_le k).trans (sup_le ?_ ?_)
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact h1
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact h2

theorem JT_le_idealT_of_not_le (hβ : Irreducible β) (hIm : ¬ idealT A ≤ idealM p β) :
    JT A p β ≤ idealT A := by
  have hm := idealM_isMaximal hβ
  obtain ⟨i, hi, him⟩ := Set.not_subset.1 hIm
  obtain ⟨a, μ, hμ, haμ⟩ := hm.exists_inv him
  rintro v ⟨k, hk1, hk2⟩
  have hcol := mem_colonElem_of_pow hk1 hk2
  have h1 : (a * i + μ) ^ (k + k) ∈ colonElem (idealT A) v := by
    refine Ideal.add_pow_mem_of_pow_mem_of_le _ (m := 1) (n := k + k) ?_ ?_ (by omega)
    · rw [pow_one, mem_colonElem, mul_assoc]; exact Ideal.mul_mem_left _ _
        (by rw [mul_comm]; exact Ideal.mul_mem_left _ _ hi)
    · exact hcol (Ideal.pow_mem_pow hμ _)
  rw [haμ, one_pow, mem_colonElem, one_mul] at h1
  exact h1

include hA hn hW in
theorem exists_idem_JT (hβ : β ∈ factorsSet (redP p A.charpoly)) :
    ∃ e ∈ JT A p β, ∃ k, 1 ≤ k ∧ C ((p : ℤ) ^ k) * e ∈ idealT A ∧ liftZ p β ^ k * e ∈ idealT A ∧
      (∀ v ∈ JT A p β, v - e * v ∈ idealT A) ∧ (idealT A ≤ idealM p β → 1 - e ∈ idealM p β) := by
  set N := Kexp A with hNdef
  have hN0 : N ≠ 0 := pow_ne_zero 2 (Int.natAbs_ne_zero.2 hW)
  have hK : 1 ≤ N := one_le_Kexp hW
  have hNI := C_card_mem_idealT hA hn hW
  have hφI : A.charpoly ∈ idealT A := Ideal.subset_span (Set.mem_insert _ _)
  obtain ⟨j, N', c, hjN, hcop, ⟨s, hs⟩, ⟨t, ht⟩⟩ := exists_split p hN0
  have hjle : j ≤ N := (Nat.lt_pow_self hp.out.one_lt).le.trans
    (Nat.le_of_dvd (by omega) ⟨N', hjN.symm⟩)
  set f := idemZ p A.charpoly β N
  set a := mult (redP p A.charpoly) β
  set e := C c * f with hedef
  have hpjN : (p : ℤ) ^ j * c = ((N : ℕ) : ℤ) * s := by rw [hs, ← hjN]; push_cast; ring
  have he1 : C ((p : ℤ) ^ j) * e ∈ idealT A := by
    have : C ((p : ℤ) ^ j) * e = C (((N : ℕ) : ℤ)) * (C s * f) := by
      rw [hedef, ← mul_assoc, ← C_mul, hpjN, C_mul, mul_assoc]
    rw [this]; exact Ideal.mul_mem_right _ _ hNI
  have he2 : liftZ p β ^ (a * N) * e ∈ idealT A := by
    have hf := liftZ_pow_mul_idemZ (charpoly_monic A) hβ hK
    obtain ⟨g1, g2, hg⟩ := Ideal.mem_span_pair.1 hf
    have : liftZ p β ^ (a * N) * e = C (((N : ℕ) : ℤ)) * (C (s * (p : ℤ) ^ (N - j)) * g1) +
        A.charpoly * (C c * g2) := by
      rw [hedef, mul_left_comm, ← hg]
      have hc : c * (p : ℤ) ^ N = ((N : ℕ) : ℤ) * (s * (p : ℤ) ^ (N - j)) := by
        rw [← mul_assoc, ← hpjN, mul_comm ((p : ℤ) ^ j), mul_assoc, ← pow_add,
          Nat.add_sub_cancel' hjle]
      have hc' : C c * C ((p : ℤ) ^ N) = C (((N : ℕ) : ℤ)) * C (s * (p : ℤ) ^ (N - j)) := by
        rw [← C_mul, hc, C_mul]
      linear_combination g1 * hc'
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ hNI) (Ideal.mul_mem_right _ _ hφI)
  set k := j + a * N + 1
  have hk1 : C ((p : ℤ) ^ k) * e ∈ idealT A := by
    have hCk : C ((p : ℤ) ^ k) = C ((p : ℤ) ^ (a * N + 1)) * C ((p : ℤ) ^ j) := by
      rw [← C_mul, ← pow_add]; congr 2; omega
    rw [hCk, mul_assoc]; exact Ideal.mul_mem_left _ _ he1
  have hk2 : liftZ p β ^ k * e ∈ idealT A := by
    have hLk : liftZ p β ^ k = liftZ p β ^ (j + 1) * liftZ p β ^ (a * N) := by
      rw [← pow_add]; congr 1; omega
    rw [hLk, mul_assoc]; exact Ideal.mul_mem_left _ _ he2
  have heJ : e ∈ JT A p β := ⟨k, hk1, hk2⟩
  refine ⟨e, heJ, k, by omega, hk1, hk2, ?_, ?_⟩
  · rintro v ⟨kv, hv1, hv2⟩
    set 𝔠 := colonElem (idealT A) v
    have hc1 : C ((p : ℤ) ^ kv) ∈ 𝔠 := hv1
    have hc2 : liftZ p β ^ kv ∈ 𝔠 := hv2
    have hcN : C (((N : ℕ) : ℤ)) ∈ 𝔠 := Ideal.mul_mem_right _ _ hNI
    have hcφ : A.charpoly ∈ 𝔠 := Ideal.mul_mem_right _ _ hφI
    have hcpN : C ((p : ℤ) ^ N) ∈ 𝔠 := C_pow_mem_of_C_mem (by omega) hcN hc1
    have hJ : idealJ p N A.charpoly ≤ 𝔠 := by
      rw [idealJ, Ideal.span_le]
      rintro x (rfl | rfl)
      · exact hcpN
      · exact hcφ
    have hcf : 1 - f ∈ 𝔠 := by
      refine one_sub_idemZ_mem (charpoly_monic A) hβ hK hJ (k := kv + 1) (by omega) ?_ ?_
      · rw [pow_succ, C_mul]; exact Ideal.mul_mem_right _ _ hc1
      · rw [pow_succ]; exact Ideal.mul_mem_right _ _ hc2
    have hcpj : C ((p : ℤ) ^ j) ∈ 𝔠 := by
      obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left (N - j) hcop)
      have : C ((p : ℤ) ^ j) = C u * C ((p : ℤ) ^ N) + C w * C (((N : ℕ) : ℤ)) := by
        rw [← C_mul, ← C_mul, ← C_add]
        congr 1
        have hpN : (p : ℤ) ^ N = (p : ℤ) ^ j * (p : ℤ) ^ (N - j) := by
          rw [← pow_add, Nat.add_sub_cancel' hjle]
        have hN' : ((N : ℕ) : ℤ) = (p : ℤ) ^ j * (N' : ℤ) := by rw [← hjN]; push_cast; ring
        rw [hpN, hN']
        push_cast at huw
        linear_combination (-((p : ℤ) ^ j)) * huw
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _ hcpN) (Ideal.mul_mem_left _ _ hcN)
    have : v - e * v = C t * (C ((p : ℤ) ^ j) * v) + C c * ((1 - f) * v) := by
      rw [hedef]
      have h1 : (1 : ℤ[X]) - C c = C t * C ((p : ℤ) ^ j) := by
        rw [← C_1, ← C_sub, ht, ← C_mul, mul_comm]
      linear_combination v * h1
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hcpj) (Ideal.mul_mem_left _ _ hcf)
  · intro hIm
    have hj : 1 ≤ j := by
      by_contra hj0
      have hj0' : j = 0 := by omega
      rw [hj0', pow_zero, one_mul] at hjN
      have hNm : C (((N : ℕ) : ℤ)) ∈ idealM p β := hIm hNI
      rw [mem_idealM_iff, map_C] at hNm
      have hN0p : ((Int.castRingHom (ZMod p)) ((N : ℕ) : ℤ)) ≠ 0 := by
        rw [eq_intCast, Int.cast_natCast, ← hjN, Ne, ZMod.natCast_eq_zero_iff]
        exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hcop
      exact (irreducible_of_mem_factorsSet hβ).not_isUnit
        (isUnit_of_dvd_unit hNm (Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 hN0p)))
    have h1 : C (1 - c) ∈ idealM p β := by
      rw [ht, C_mul, ← Nat.sub_add_cancel hj, pow_succ, C_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    have h2 := one_sub_idemZ_mem_idealM (charpoly_monic A) hβ hK
    have : 1 - e = C (1 - c) + C c * (1 - f) := by
      rw [hedef, C_sub, C_1]; ring
    rw [this]
    exact add_mem h1 (Ideal.mul_mem_left _ _ h2)

include hA hn hW in
theorem idealM_pow_mul_JT_le (hβ : β ∈ factorsSet (redP p A.charpoly)) :
    ∃ N, idealM p β ^ N * JT A p β ≤ idealT A := by
  obtain ⟨e, heJ, k, -, hk1, hk2, he, -⟩ := exists_idem_JT hA hn hW hβ
  refine ⟨k + k, Ideal.mul_le.2 fun r hr v hv => ?_⟩
  have h1 : C ((p : ℤ) ^ k) * v ∈ idealT A := by
    have : C ((p : ℤ) ^ k) * v = C ((p : ℤ) ^ k) * (v - e * v) + (C ((p : ℤ) ^ k) * e) * v := by
      ring
    rw [this]; exact add_mem (Ideal.mul_mem_left _ _ (he v hv)) (Ideal.mul_mem_right _ _ hk1)
  have h2 : liftZ p β ^ k * v ∈ idealT A := by
    have : liftZ p β ^ k * v = liftZ p β ^ k * (v - e * v) + (liftZ p β ^ k * e) * v := by ring
    rw [this]; exact add_mem (Ideal.mul_mem_left _ _ (he v hv)) (Ideal.mul_mem_right _ _ hk2)
  exact mem_colonElem_of_pow h1 h2 hr

include hA hn hW in
theorem cor_chain_a (hβ : β ∈ factorsSet (redP p A.charpoly)) {t : ℤ[X]}
    (ht : idealM p β * JT A p β ⊔ idealT A = Ideal.span {t} * JT A p β ⊔ idealT A) :
    IsChainComponent A p β ∧ ∀ Q : Matrix (Fin n) (Fin n) ℚ, IsMateMatrix A Q → β ∉ Fset A Q p := by
  have hchain : IsChainComponent A p β := by
    obtain ⟨e, heJ, k, -, -, -, he, -⟩ := exists_idem_JT hA hn hW hβ
    obtain ⟨N, hnil⟩ := idealM_pow_mul_JT_le hA hn hW hβ
    have hm := idealM_isMaximal (irreducible_of_mem_factorsSet hβ)
    have H := chain_of_principal hm idealT_le_JT ht hnil heJ he
    intro 𝔄 𝔅 h𝔄 h𝔅
    have hcomap : ∀ 𝔄 : Ideal (TT A), 𝔄 ≤ TTpart A p β →
        idealT A ≤ 𝔄.comap (Ideal.Quotient.mk _) ∧ 𝔄.comap (Ideal.Quotient.mk _) ≤ JT A p β := by
      intro 𝔄 h𝔄
      refine ⟨fun f hf => ?_, ?_⟩
      · rw [Ideal.mem_comap, (Ideal.Quotient.eq_zero_iff_mem).2 hf]; exact zero_mem _
      · have := Ideal.comap_mono (f := Ideal.Quotient.mk (idealT A)) h𝔄
        rwa [TTpart, Ideal.comap_map_mk idealT_le_JT] at this
    obtain ⟨h1, h2⟩ := hcomap 𝔄 h𝔄
    obtain ⟨h3, h4⟩ := hcomap 𝔅 h𝔅
    rcases H _ _ h1 h2 h3 h4 with h | h
    · left
      have := Ideal.map_mono (f := Ideal.Quotient.mk (idealT A)) h
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this
    · right
      have := Ideal.map_mono (f := Ideal.Quotient.mk (idealT A)) h
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this
  exact ⟨hchain, fun Q hQ hβQ => (levellocal_ii hA hn hW hQ hβQ).2.1 hchain⟩

theorem le_sup_pow_of_le_sup_sq {R : Type*} [CommRing R] {m I : Ideal R} {t : R}
    (h : m ≤ Ideal.span {t} ⊔ m ^ 2 ⊔ I) : ∀ r, m ≤ Ideal.span {t} ⊔ m ^ (r + 1) ⊔ I := by
  intro r
  induction r with
  | zero =>
    rw [zero_add, pow_one]
    exact le_trans (le_sup_right : m ≤ Ideal.span {t} ⊔ m) le_sup_left
  | succ r ih =>
    set B := Ideal.span {t} ⊔ m ^ (r + 1 + 1) ⊔ I
    have e1 : m * Ideal.span {t} ≤ B :=
      le_trans Ideal.mul_le_right (le_trans (le_sup_left : Ideal.span {t} ≤ Ideal.span {t} ⊔ m ^ (r + 1 + 1))
        le_sup_left)
    have e2 : m * m ^ (r + 1) ≤ B := by
      rw [← pow_succ']
      exact le_trans (le_sup_right : m ^ (r + 1 + 1) ≤ Ideal.span {t} ⊔ m ^ (r + 1 + 1)) le_sup_left
    have e3 : m * I ≤ B := le_trans Ideal.mul_le_right le_sup_right
    have h2 : m ^ 2 ≤ B := by
      have : m * (Ideal.span {t} ⊔ m ^ (r + 1) ⊔ I) ≤ B := by
        rw [Ideal.mul_sup, Ideal.mul_sup]
        exact sup_le (sup_le e1 e2) e3
      rw [sq]
      exact le_trans (Ideal.mul_mono_right ih) this
    have h3 : Ideal.span {t} ≤ B :=
      le_trans (le_sup_left : Ideal.span {t} ≤ Ideal.span {t} ⊔ m ^ (r + 1 + 1)) le_sup_left
    have h4 : I ≤ B := le_sup_right
    exact le_trans h (sup_le (sup_le h3 h2) h4)

theorem mem_sup_of_decomp {m I : Ideal ℤ[X]} {x t g u v μ : ℤ[X]} (hg : g ∈ I) (hμ : μ ∈ m)
    (hx : x ∈ m) (h : x = u * g - v * t + μ * x) : x ∈ Ideal.span {t} ⊔ m ^ 2 ⊔ I := by
  have h1 : u * g ∈ Ideal.span {t} ⊔ m ^ 2 ⊔ I := Ideal.mem_sup_right (I.mul_mem_left u hg)
  have h2 : v * t ∈ Ideal.span {t} ⊔ m ^ 2 ⊔ I :=
    Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 (dvd_mul_left t v)))
  have h3 : μ * x ∈ Ideal.span {t} ⊔ m ^ 2 ⊔ I := by
    have : μ * x ∈ m ^ 2 := by rw [sq]; exact Ideal.mul_mem_mul hμ hx
    exact Ideal.mem_sup_left (Ideal.mem_sup_right this)
  rw [h]
  exact add_mem (sub_mem h1 h2) h3

include hA hn hW in
theorem cor_chain_b (hβ : β ∈ factorsSet (redP p A.charpoly))
    (hg : ∃ g ∈ idealT A, g ∉ idealM p β ^ 2) :
    ∃ t : ℤ[X], idealM p β * JT A p β ⊔ idealT A = Ideal.span {t} * JT A p β ⊔ idealT A := by
  have hβi := irreducible_of_mem_factorsSet hβ
  have hm := idealM_isMaximal hβi
  by_cases hIm : idealT A ≤ idealM p β
  · obtain ⟨g, hgI, hgm⟩ := hg
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (hIm hgI)
    have hpm : C (p : ℤ) ∈ idealM p β := Ideal.subset_span (Set.mem_insert _ _)
    have hβm : liftZ p β ∈ idealM p β := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    obtain ⟨t, htm, hle⟩ : ∃ t ∈ idealM p β,
        idealM p β ≤ Ideal.span {t} ⊔ idealM p β ^ 2 ⊔ idealT A := by
      by_cases ha : a ∈ idealM p β
      · have hb : b ∉ idealM p β := by
          intro hb
          apply hgm
          rw [← hab, sq]
          exact add_mem (Ideal.mul_mem_mul ha hpm) (Ideal.mul_mem_mul hb hβm)
        obtain ⟨b', μ, hμ, hb'μ⟩ := hm.exists_inv hb
        refine ⟨C (p : ℤ), hpm, ?_⟩
        have hgen : ∀ x ∈ ({C (p : ℤ), liftZ p β} : Set ℤ[X]),
            x ∈ Ideal.span {C (p : ℤ)} ⊔ idealM p β ^ 2 ⊔ idealT A := by
          rintro x (rfl | rfl)
          · exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span rfl))
          · refine mem_sup_of_decomp hgI hμ hβm (u := b') (v := b' * a) ?_
            rw [← hab]; linear_combination (-(liftZ p β)) * hb'μ
        exact Ideal.span_le.2 hgen
      · obtain ⟨a', μ, hμ, ha'μ⟩ := hm.exists_inv ha
        refine ⟨liftZ p β, hβm, ?_⟩
        have hgen : ∀ x ∈ ({C (p : ℤ), liftZ p β} : Set ℤ[X]),
            x ∈ Ideal.span {liftZ p β} ⊔ idealM p β ^ 2 ⊔ idealT A := by
          rintro x (rfl | rfl)
          · refine mem_sup_of_decomp hgI hμ hpm (u := a') (v := a' * b) ?_
            rw [← hab]; linear_combination (-(C (p : ℤ))) * ha'μ
          · exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span rfl))
        exact Ideal.span_le.2 hgen
    refine ⟨t, le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)⟩
    · obtain ⟨N, hnil⟩ := idealM_pow_mul_JT_le hA hn hW hβ
      have h1 := le_sup_pow_of_le_sup_sq hle N
      set B := Ideal.span {t} * JT A p β ⊔ idealT A
      have e1 : Ideal.span {t} * JT A p β ≤ B := le_sup_left
      have e2 : idealM p β ^ (N + 1) * JT A p β ≤ B := by
        have : idealM p β ^ (N + 1) * JT A p β ≤ idealM p β ^ N * JT A p β := by
          rw [pow_succ, mul_comm (idealM p β ^ N), mul_assoc]; exact Ideal.mul_le_right
        exact le_trans this (le_trans hnil le_sup_right)
      have e3 : idealT A * JT A p β ≤ B := le_trans Ideal.mul_le_left le_sup_right
      have : (Ideal.span {t} ⊔ idealM p β ^ (N + 1) ⊔ idealT A) * JT A p β ≤ B := by
        rw [Ideal.sup_mul, Ideal.sup_mul]
        exact sup_le (sup_le e1 e2) e3
      exact le_trans (Ideal.mul_mono_left h1) this
    · have : Ideal.span {t} ≤ idealM p β := by
        rw [Ideal.span_le, Set.singleton_subset_iff]; exact htm
      exact le_trans (Ideal.mul_mono_left this) le_sup_left
  · refine ⟨0, ?_⟩
    have hJT := JT_le_idealT_of_not_le hβi hIm
    rw [sup_eq_right.2 (Ideal.mul_le_right.trans hJT), Ideal.span_singleton_eq_bot.2 rfl,
      Ideal.bot_mul, bot_sup_eq]

include hA hn hW in
theorem TTpart_ne_bot_iff (hβ : β ∈ factorsSet (redP p A.charpoly)) :
    TTpart A p β ≠ ⊥ ↔ idealT A ≤ idealM p β := by
  constructor
  · intro hne
    by_contra hIm
    apply hne
    rw [TTpart]
    exact Ideal.map_mk_eq_bot_of_le (JT_le_idealT_of_not_le (irreducible_of_mem_factorsSet hβ) hIm)
  · intro hIm h0
    obtain ⟨e, heJ, -, -, -, -, -, he1⟩ := exists_idem_JT hA hn hW hβ
    have hmk : Ideal.Quotient.mk (idealT A) e ∈ TTpart A p β := Ideal.mem_map_of_mem _ heJ
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmk
    have hm := idealM_isMaximal (irreducible_of_mem_factorsSet hβ)
    apply hm.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : ℤ[X]) = (1 - e) + e := by ring
    rw [this]
    exact add_mem (he1 hIm) (hIm hmk)

end CorChain

end DGS
