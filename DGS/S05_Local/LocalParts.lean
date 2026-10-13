module

public import DGS.S05_Local.Components

@[expose] public section

open Matrix Polynomial

namespace DGS

variable {n : ℕ}

def IsIntQ (q : ℚ) : Prop := ∃ k : ℤ, q = k

theorem isIntQ_zero : IsIntQ 0 := ⟨0, by simp⟩

theorem isIntQ_intCast (k : ℤ) : IsIntQ (k : ℚ) := ⟨k, rfl⟩

theorem IsIntQ.add {q r : ℚ} (hq : IsIntQ q) (hr : IsIntQ r) : IsIntQ (q + r) := by
  obtain ⟨a, rfl⟩ := hq; obtain ⟨b, rfl⟩ := hr; exact ⟨a + b, by push_cast; ring⟩

theorem IsIntQ.sub {q r : ℚ} (hq : IsIntQ q) (hr : IsIntQ r) : IsIntQ (q - r) := by
  obtain ⟨a, rfl⟩ := hq; obtain ⟨b, rfl⟩ := hr; exact ⟨a - b, by push_cast; ring⟩

theorem IsIntQ.int_mul {q : ℚ} (hq : IsIntQ q) (k : ℤ) : IsIntQ (k * q) := by
  obtain ⟨a, rfl⟩ := hq; exact ⟨k * a, by push_cast; ring⟩

theorem isIntQ_sum {ι : Type*} (s : Finset ι) {f : ι → ℚ} (h : ∀ i ∈ s, IsIntQ (f i)) :
    IsIntQ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isIntQ_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isIntQ_dot_zsmul_left {y z : Fin n → ℚ} (k : ℤ) (h : IsIntQ (y ⬝ᵥ z)) :
    IsIntQ ((k • y) ⬝ᵥ z) := by
  rw [smul_dotProduct, zsmul_eq_mul]; exact h.int_mul k

theorem isIntQ_dot_zsmul_right {y z : Fin n → ℚ} (k : ℤ) (h : IsIntQ (y ⬝ᵥ z)) :
    IsIntQ (y ⬝ᵥ (k • z)) := by
  rw [dotProduct_smul, zsmul_eq_mul]; exact h.int_mul k

theorem isIntQ_of_mem_latDual {L : Submodule ℤ (Fin n → ℚ)} {y z : Fin n → ℚ} (hy : y ∈ latDual L)
    (hz : z ∈ L) : IsIntQ (y ⬝ᵥ z) := hy z hz

theorem isIntQ_of_mem_latDual' {L : Submodule ℤ (Fin n → ℚ)} {y z : Fin n → ℚ} (hy : y ∈ latDual L)
    (hz : z ∈ L) : IsIntQ (z ⬝ᵥ y) := by
  rw [dotProduct_comm]; exact hy z hz

section Act

variable (A : Matrix (Fin n) (Fin n) ℤ)

noncomputable def actZ (g : ℤ[X]) : Matrix (Fin n) (Fin n) ℚ :=
  aeval (toQ A) (g.map (Int.castRingHom ℚ))

theorem actZ_add (g h : ℤ[X]) : actZ A (g + h) = actZ A g + actZ A h := by
  rw [actZ, actZ, actZ, Polynomial.map_add, map_add]

theorem actZ_sub (g h : ℤ[X]) : actZ A (g - h) = actZ A g - actZ A h := by
  rw [actZ, actZ, actZ, Polynomial.map_sub, map_sub]

theorem actZ_mul (g h : ℤ[X]) : actZ A (g * h) = actZ A g * actZ A h := by
  rw [actZ, actZ, actZ, Polynomial.map_mul, map_mul]

theorem actZ_one : actZ A 1 = 1 := by rw [actZ, Polynomial.map_one, map_one]

theorem actZ_zero : actZ A 0 = 0 := by rw [actZ, Polynomial.map_zero, map_zero]

theorem actZ_X : actZ A X = toQ A := by rw [actZ, Polynomial.map_X, aeval_X]

theorem actZ_sum {ι : Type*} (s : Finset ι) (g : ι → ℤ[X]) :
    actZ A (∑ i ∈ s, g i) = ∑ i ∈ s, actZ A (g i) := by
  rw [actZ, Polynomial.map_sum, map_sum]; rfl

theorem actZ_C_mulVec (k : ℤ) (y : Fin n → ℚ) : actZ A (C k) *ᵥ y = k • y := by
  rw [actZ, Polynomial.map_C, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec,
    eq_intCast, Int.cast_smul_eq_zsmul]

theorem actZ_charpoly : actZ A A.charpoly = 0 := by
  rw [actZ, ← toQ_charpoly, aeval_self_charpoly]

variable {A}

theorem actZ_transpose (hA : A.IsSymm) (g : ℤ[X]) : (actZ A g)ᵀ = actZ A g := by
  rw [actZ, aeval_eq_sum_range, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.transpose_smul, Matrix.transpose_pow, (toQ_isSymm hA).eq]

theorem actZ_dotProduct (hA : A.IsSymm) (g : ℤ[X]) (y z : Fin n → ℚ) :
    (actZ A g *ᵥ y) ⬝ᵥ z = y ⬝ᵥ (actZ A g *ᵥ z) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, actZ_transpose hA]

theorem actZ_mulVec_mem {L : Submodule ℤ (Fin n → ℚ)} (hL : IsAStable A L) (g : ℤ[X])
    {y : Fin n → ℚ} (hy : y ∈ L) : actZ A g *ᵥ y ∈ L :=
  aeval_mulVec_mem hL g hy

theorem latZ_isAStable : IsAStable A (latZ n) := by
  rintro y ⟨c, rfl⟩
  exact ⟨A *ᵥ c, mulVec_intVec A c⟩

variable (A) in
theorem latC_isAStable : IsAStable A (latC A) := by
  intro y hy
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : toQ A *ᵥ y = 0 := Subsingleton.elim _ _
    rw [this]; exact zero_mem _
  · obtain ⟨g, rfl⟩ := (mem_latC_iff hn).1 hy
    refine (mem_latC_iff hn).2 ⟨X * g, ?_⟩
    rw [Polynomial.map_mul, iotaQ_mul, Polynomial.map_X, aeval_X]

theorem latDual_isAStable (hA : A.IsSymm) {L : Submodule ℤ (Fin n → ℚ)} (hL : IsAStable A L) :
    IsAStable A (latDual L) := by
  intro y hy z hz
  have h := hy _ (hL z hz)
  rw [← actZ_X, actZ_dotProduct hA]
  rw [← actZ_X] at h
  exact h

theorem latC_le_latZ (hn : 1 ≤ n) : latC A ≤ latZ n := by
  have := (lem_ideals hn (isMateMatrix_one A)).2.2.1
  rwa [latOf_one] at this

theorem latZ_le_latDual (hn : 1 ≤ n) : latZ n ≤ latDual (latC A) := by
  have := (lem_ideals hn (isMateMatrix_one A)).2.2.2
  rwa [latOf_one] at this

end Act

section Ann

variable (A : Matrix (Fin n) (Fin n) ℤ)

noncomputable def annC (y : Fin n → ℚ) : Ideal ℤ[X] where
  carrier := {g | actZ A g *ᵥ y ∈ latC A}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, actZ_add, add_mulVec] at *
    exact add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, actZ_zero, zero_mulVec]
    exact zero_mem _
  smul_mem' := by
    intro c g hg
    simp only [Set.mem_ofPred_eq, smul_eq_mul, actZ_mul, ← mulVec_mulVec] at *
    exact actZ_mulVec_mem (latC_isAStable A) c hg

variable {A}

theorem mem_annC {g : ℤ[X]} {y : Fin n → ℚ} : g ∈ annC A y ↔ actZ A g *ᵥ y ∈ latC A := Iff.rfl

theorem charpoly_mem_annC (y : Fin n → ℚ) : A.charpoly ∈ annC A y := by
  rw [mem_annC, actZ_charpoly, zero_mulVec]; exact zero_mem _

theorem C_mem_annC {k : ℤ} {y : Fin n → ℚ} : C k ∈ annC A y ↔ k • y ∈ latC A := by
  rw [mem_annC, actZ_C_mulVec]

theorem one_mem_annC {y : Fin n → ℚ} : 1 ∈ annC A y ↔ y ∈ latC A := by
  rw [mem_annC, actZ_one, one_mulVec]

theorem mem_annC_actZ {g h : ℤ[X]} {y : Fin n → ℚ} :
    g ∈ annC A (actZ A h *ᵥ y) ↔ g * h ∈ annC A y := by
  rw [mem_annC, mem_annC, actZ_mul, mulVec_mulVec]

theorem annC_add_le {y z : Fin n → ℚ} : annC A y ⊓ annC A z ≤ annC A (y + z) := by
  rintro g ⟨hy, hz⟩
  rw [mem_annC, mulVec_add]
  exact add_mem hy hz

theorem annC_le_zsmul (k : ℤ) {y : Fin n → ℚ} : annC A y ≤ annC A (k • y) := by
  intro g hg
  rw [mem_annC, mulVec_smul]
  exact Submodule.smul_mem _ k hg

theorem annC_eq_of_sub_mem {y z : Fin n → ℚ} (h : y - z ∈ latC A) : annC A y = annC A z := by
  have key : ∀ y z : Fin n → ℚ, y - z ∈ latC A → annC A z ≤ annC A y := by
    intro y z h g hg
    rw [mem_annC] at hg ⊢
    have : actZ A g *ᵥ y = actZ A g *ᵥ (y - z) + actZ A g *ᵥ z := by
      rw [← mulVec_add, sub_add_cancel]
    rw [this]
    exact add_mem (actZ_mulVec_mem (latC_isAStable A) g h) hg
  refine le_antisymm (key z y ?_) (key y z h)
  rw [← neg_sub]; exact neg_mem h

theorem idealJ_le_annC {p K : ℕ} {y : Fin n → ℚ} (h : C ((p : ℤ) ^ K) ∈ annC A y) :
    idealJ p K A.charpoly ≤ annC A y := by
  rw [idealJ, Ideal.span_le]
  rintro g (rfl | rfl)
  · exact h
  · exact charpoly_mem_annC y

theorem C_pow_mem_of_C_mem {p : ℕ} [hp : Fact p.Prime] {𝔞 : Ideal ℤ[X]} {N : ℕ} (hN : 0 < N)
    (hNmem : C (N : ℤ) ∈ 𝔞) {k : ℕ} (hk : C ((p : ℤ) ^ k) ∈ 𝔞) : C ((p : ℤ) ^ N) ∈ 𝔞 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 (Nat.gcd_dvd_left (p ^ k) N)
  have hjN : j ≤ N := by
    have h1 : p ^ j ≤ N := hj ▸ Nat.le_of_dvd hN (Nat.gcd_dvd_right _ _)
    exact (Nat.lt_pow_self hp.out.one_lt).le.trans h1
  have hg : C ((Nat.gcd (p ^ k) N : ℕ) : ℤ) ∈ 𝔞 := by
    rw [Nat.gcd_eq_gcd_ab, C_add, C_mul, C_mul]
    push_cast
    exact add_mem (Ideal.mul_mem_right _ _ hk) (Ideal.mul_mem_right _ _ hNmem)
  rw [hj] at hg
  have : (p : ℤ) ^ N = (p : ℤ) ^ (N - j) * ((p ^ j : ℕ) : ℤ) := by
    push_cast; rw [← pow_add, Nat.sub_add_cancel hjN]
  rw [this, C_mul]
  exact Ideal.mul_mem_left _ _ hg

theorem card_smul_mem_latC (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) {y : Fin n → ℚ}
    (hy : y ∈ latDual (latC A)) : (((walkMatrix A).det.natAbs ^ 2 : ℕ) : ℤ) • y ∈ latC A := by
  have h := card_nsmul_eq_zero' (G := DD A) (x := Submodule.Quotient.mk ⟨y, hy⟩)
  rw [card_DD hn hW, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, latCinDual,
    Submodule.mem_comap, Submodule.subtype_apply] at h
  rw [natCast_zsmul]
  exact h

theorem C_pow_card_mem_annC (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) {p : ℕ} [Fact p.Prime]
    {y : Fin n → ℚ} (hy : y ∈ latDual (latC A)) {k : ℕ} (hk : C ((p : ℤ) ^ k) ∈ annC A y) :
    C ((p : ℤ) ^ ((walkMatrix A).det.natAbs ^ 2)) ∈ annC A y := by
  refine C_pow_mem_of_C_mem ?_ ?_ hk
  · exact pow_pos (Int.natAbs_pos.2 hW) 2
  · rw [C_mem_annC]; exact card_smul_mem_latC hn hW hy

theorem exists_split (p : ℕ) [hp : Fact p.Prime] {N : ℕ} (hN : N ≠ 0) :
    ∃ (j N' : ℕ) (c : ℤ), p ^ j * N' = N ∧ Nat.Coprime p N' ∧ (N' : ℤ) ∣ c ∧ (p : ℤ) ^ j ∣ 1 - c := by
  set N' := ordCompl[p] N
  have hcop : Nat.Coprime (p ^ N.factorization p) N' :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp.out hN)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  refine ⟨N.factorization p, N', v * (N' : ℤ), Nat.ordProj_mul_ordCompl_eq_self N p,
    Nat.coprime_ordCompl hp.out hN, dvd_mul_left _ _, ⟨u, ?_⟩⟩
  rw [Nat.cast_pow] at huv
  linear_combination -huv

end Ann

section MPart

variable (A : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) [hp : Fact p.Prime] (β : (ZMod p)[X])

noncomputable def mPart (L : Submodule ℤ (Fin n → ℚ)) : Submodule ℤ (Fin n → ℚ) where
  carrier := {y | y ∈ L ∧ ∃ k, C ((p : ℤ) ^ k) ∈ annC A y ∧ liftZ p β ^ k ∈ annC A y}
  add_mem' := by
    rintro y z ⟨hy, k, hk1, hk2⟩ ⟨hz, l, hl1, hl2⟩
    refine ⟨L.add_mem hy hz, k + l, annC_add_le ⟨?_, ?_⟩, annC_add_le ⟨?_, ?_⟩⟩
    · rw [pow_add, C_mul]; exact Ideal.mul_mem_right _ _ hk1
    · rw [pow_add, C_mul]; exact Ideal.mul_mem_left _ _ hl1
    · rw [pow_add]; exact Ideal.mul_mem_right _ _ hk2
    · rw [pow_add]; exact Ideal.mul_mem_left _ _ hl2
  zero_mem' := ⟨L.zero_mem, 0, by simp [one_mem_annC], by simp [one_mem_annC]⟩
  smul_mem' := by
    rintro c y ⟨hy, k, hk1, hk2⟩
    exact ⟨L.smul_mem c hy, k, annC_le_zsmul c hk1, annC_le_zsmul c hk2⟩

variable {A p β}

theorem mem_mPart {L : Submodule ℤ (Fin n → ℚ)} {y : Fin n → ℚ} :
    y ∈ mPart A p β L ↔ y ∈ L ∧ ∃ k, C ((p : ℤ) ^ k) ∈ annC A y ∧ liftZ p β ^ k ∈ annC A y :=
  Iff.rfl

theorem mPart_le (L : Submodule ℤ (Fin n → ℚ)) : mPart A p β L ≤ L := fun _ hy => hy.1

theorem mPart_mono {L L' : Submodule ℤ (Fin n → ℚ)} (h : L ≤ L') :
    mPart A p β L ≤ mPart A p β L' := fun _ hy => ⟨h hy.1, hy.2⟩

theorem latC_le_mPart {L : Submodule ℤ (Fin n → ℚ)} (hC : latC A ≤ L) :
    latC A ≤ mPart A p β L := fun y hy =>
  ⟨hC hy, 0, by simpa [one_mem_annC] using hy, by simpa [one_mem_annC] using hy⟩

theorem mPart_isAStable {L : Submodule ℤ (Fin n → ℚ)} (hL : IsAStable A L) :
    IsAStable A (mPart A p β L) := by
  rintro y ⟨hy, k, hk1, hk2⟩
  refine ⟨hL y hy, k, ?_, ?_⟩
  · rw [← actZ_X, mem_annC_actZ]; exact Ideal.mul_mem_right _ _ hk1
  · rw [← actZ_X, mem_annC_actZ]; exact Ideal.mul_mem_right _ _ hk2

theorem actZ_mulVec_mem_mPart {L : Submodule ℤ (Fin n → ℚ)} (hL : IsAStable A L) (g : ℤ[X])
    {y : Fin n → ℚ} (hy : y ∈ mPart A p β L) : actZ A g *ᵥ y ∈ mPart A p β L := by
  obtain ⟨hy, k, hk1, hk2⟩ := hy
  refine ⟨actZ_mulVec_mem hL g hy, k, ?_, ?_⟩
  · rw [mem_annC_actZ]; exact Ideal.mul_mem_right _ _ hk1
  · rw [mem_annC_actZ]; exact Ideal.mul_mem_right _ _ hk2

theorem C_pow_card_mem_annC_of_mPart (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0) {y : Fin n → ℚ}
    (hy : y ∈ mPart A p β (latDual (latC A))) :
    C ((p : ℤ) ^ ((walkMatrix A).det.natAbs ^ 2)) ∈ annC A y := by
  obtain ⟨hy, k, hk1, -⟩ := hy
  exact C_pow_card_mem_annC hn hW hy hk1

variable (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0)

noncomputable abbrev Kexp (A : Matrix (Fin n) (Fin n) ℤ) : ℕ := (walkMatrix A).det.natAbs ^ 2

theorem one_le_Kexp (hW : (walkMatrix A).det ≠ 0) : 1 ≤ Kexp A :=
  Nat.one_le_iff_ne_zero.2 (pow_ne_zero 2 (Int.natAbs_ne_zero.2 hW))

theorem actZ_idemZ_mem_mPart (hβ : β ∈ factorsSet (redP p A.charpoly)) {K : ℕ} (hK : 1 ≤ K)
    {L : Submodule ℤ (Fin n → ℚ)} (hL : IsAStable A L) {y : Fin n → ℚ} (hy : y ∈ L)
    (hyK : C ((p : ℤ) ^ K) ∈ annC A y) :
    actZ A (idemZ p A.charpoly β K) *ᵥ y ∈ mPart A p β L := by
  have hφ := charpoly_monic A
  set a := mult (redP p A.charpoly) β
  refine ⟨actZ_mulVec_mem hL _ hy, a * K + K, ?_, ?_⟩
  · rw [mem_annC_actZ, pow_add, C_mul, mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hyK)
  · rw [mem_annC_actZ, pow_add, mul_comm (liftZ p β ^ (a * K)), mul_assoc]
    exact Ideal.mul_mem_left _ _ (idealJ_le_annC hyK (liftZ_pow_mul_idemZ hφ hβ hK))

theorem actZ_idemZ_sub_mem (hβ : β ∈ factorsSet (redP p A.charpoly)) {K : ℕ} (hK : 1 ≤ K)
    {L : Submodule ℤ (Fin n → ℚ)} {y : Fin n → ℚ} (hy : y ∈ mPart A p β L)
    (hyK : C ((p : ℤ) ^ K) ∈ annC A y) :
    y - actZ A (idemZ p A.charpoly β K) *ᵥ y ∈ latC A := by
  obtain ⟨-, k, hk1, hk2⟩ := hy
  have h1 : C ((p : ℤ) ^ (k + 1)) ∈ annC A y := by
    rw [pow_succ, C_mul]; exact Ideal.mul_mem_right _ _ hk1
  have h2 : liftZ p β ^ (k + 1) ∈ annC A y := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hk2
  have := one_sub_idemZ_mem (charpoly_monic A) hβ hK (idealJ_le_annC hyK) (by omega) h1 h2
  rw [mem_annC, actZ_sub, actZ_one, sub_mulVec, one_mulVec] at this
  exact this

theorem sum_actZ_idemZ_sub_mem {K : ℕ} (hK : 1 ≤ K) {y : Fin n → ℚ}
    (hyK : C ((p : ℤ) ^ K) ∈ annC A y) :
    ∑ β ∈ factorsSet (redP p A.charpoly), actZ A (idemZ p A.charpoly β K) *ᵥ y - y ∈ latC A := by
  have := idealJ_le_annC hyK (idemZ_sum (charpoly_monic A) (p := p) hK)
  rw [mem_annC, actZ_sub, actZ_one, sub_mulVec, one_mulVec, actZ_sum, Matrix.sum_mulVec] at this
  exact this

theorem actZ_idemZ_mem_of_ne (hβ : β ∈ factorsSet (redP p A.charpoly)) {β' : (ZMod p)[X]}
    (hβ' : β' ∈ factorsSet (redP p A.charpoly)) (hne : β ≠ β') {K : ℕ} (hK : 1 ≤ K)
    {L : Submodule ℤ (Fin n → ℚ)} {y : Fin n → ℚ} (hy : y ∈ mPart A p β L)
    (hyK : C ((p : ℤ) ^ K) ∈ annC A y) :
    actZ A (idemZ p A.charpoly β' K) *ᵥ y ∈ latC A := by
  obtain ⟨-, k, hk1, hk2⟩ := hy
  have h1 : C ((p : ℤ) ^ (k + 1)) ∈ annC A y := by
    rw [pow_succ, C_mul]; exact Ideal.mul_mem_right _ _ hk1
  have h2 : liftZ p β ^ (k + 1) ∈ annC A y := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hk2
  exact idemZ_mem_of_ne (charpoly_monic A) hβ hβ' hne hK (idealJ_le_annC hyK) (by omega) h1 h2

end MPart

section Pairing

variable {A : Matrix (Fin n) (Fin n) ℤ} {p : ℕ} [hp : Fact p.Prime] {β : (ZMod p)[X]}

omit hp in
theorem isIntQ_dot_of_coprime {y z : Fin n → ℚ} (hy : y ∈ latDual (latC A))
    (hz : z ∈ latDual (latC A)) {k N' : ℕ} (hk : ((p : ℤ) ^ k) • y ∈ latC A)
    (hN' : (N' : ℤ) • z ∈ latC A) (hcop : Nat.Coprime p N') : IsIntQ (y ⬝ᵥ z) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left k hcop)
  have h1 : IsIntQ ((((p : ℤ) ^ k) • y) ⬝ᵥ z) := isIntQ_of_mem_latDual' hz hk
  have h2 : IsIntQ (y ⬝ᵥ ((N' : ℤ) • z)) := isIntQ_of_mem_latDual hy hN'
  have huv' : (u : ℚ) * ((p : ℚ) ^ k) + (v : ℚ) * (N' : ℚ) = 1 := by exact_mod_cast huv
  have : y ⬝ᵥ z = u * ((((p : ℤ) ^ k) • y) ⬝ᵥ z) + v * (y ⬝ᵥ ((N' : ℤ) • z)) := by
    rw [smul_dotProduct, dotProduct_smul, zsmul_eq_mul, zsmul_eq_mul]
    push_cast
    linear_combination -(y ⬝ᵥ z) * huv'
  rw [this]
  exact (h1.int_mul u).add (h2.int_mul v)

theorem mem_of_forall_dot_mPart (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0)
    (hβ : β ∈ factorsSet (redP p A.charpoly)) {Λ : Submodule ℤ (Fin n → ℚ)} (hΛ : IsAStable A Λ)
    (hΛu : latDual Λ = Λ) (hCΛ : latC A ≤ Λ) {y : Fin n → ℚ}
    (hy : y ∈ mPart A p β (latDual (latC A))) (h : ∀ z ∈ mPart A p β Λ, IsIntQ (y ⬝ᵥ z)) :
    y ∈ Λ := by
  have hΛC : Λ ≤ latDual (latC A) := by
    have := latDual_anti hCΛ; rwa [hΛu] at this
  rw [← hΛu]
  intro z hz
  have hzC := hΛC hz
  set N := (walkMatrix A).det.natAbs ^ 2 with hNdef
  have hN0 : N ≠ 0 := pow_ne_zero 2 (Int.natAbs_ne_zero.2 hW)
  have hK : 1 ≤ N := Nat.one_le_iff_ne_zero.2 hN0
  obtain ⟨j, N', c, hjN, hcop, ⟨s, hs⟩, ⟨t, ht⟩⟩ := exists_split p hN0
  have hNz : (N : ℤ) • z ∈ latC A := card_smul_mem_latC hn hW hzC
  have hzsplit : y ⬝ᵥ z = y ⬝ᵥ (c • z) + y ⬝ᵥ ((1 - c) • z) := by
    rw [← dotProduct_add, ← add_smul, add_sub_cancel, one_smul]
  rw [hzsplit]
  obtain ⟨hyC, k, hk1, hk2⟩ := hy
  refine IsIntQ.add ?_ ?_
  ·
    set zp := c • z
    have hzpC : zp ∈ latDual (latC A) := Submodule.smul_mem _ c hzC
    have hzpΛ : zp ∈ Λ := Λ.smul_mem c hz
    have hzpj : C ((p : ℤ) ^ j) ∈ annC A zp := by
      rw [C_mem_annC, smul_smul, hs]
      have : (p : ℤ) ^ j * ((N' : ℤ) * s) = s * (N : ℤ) := by rw [← hjN]; push_cast; ring
      rw [this, ← smul_smul]
      exact Submodule.smul_mem _ s hNz
    have hzpK : C ((p : ℤ) ^ N) ∈ annC A zp := C_pow_card_mem_annC hn hW hzpC hzpj
    have hyK : C ((p : ℤ) ^ N) ∈ annC A y := C_pow_card_mem_annC hn hW hyC hk1
    have hsum := sum_actZ_idemZ_sub_mem (A := A) (p := p) hK hzpK
    have hdecomp : y ⬝ᵥ zp = ∑ β' ∈ factorsSet (redP p A.charpoly),
        y ⬝ᵥ (actZ A (idemZ p A.charpoly β' N) *ᵥ zp) -
        y ⬝ᵥ (∑ β' ∈ factorsSet (redP p A.charpoly), actZ A (idemZ p A.charpoly β' N) *ᵥ zp - zp) := by
      rw [dotProduct_sub, dotProduct_sum]; ring
    rw [hdecomp]
    refine IsIntQ.sub (isIntQ_sum _ fun β' hβ' => ?_) (isIntQ_of_mem_latDual hyC hsum)
    by_cases hb : β' = β
    · subst hb
      exact h _ (actZ_idemZ_mem_mPart hβ hK hΛ hzpΛ hzpK)
    · rw [← actZ_dotProduct hA]
      exact isIntQ_of_mem_latDual' hzpC
        (actZ_idemZ_mem_of_ne hβ hβ' (Ne.symm hb) hK ⟨hyC, k, hk1, hk2⟩ hyK)
  ·
    refine isIntQ_dot_of_coprime hyC (Submodule.smul_mem _ _ hzC) (C_mem_annC.1 hk1) ?_ hcop
    rw [smul_smul, ht]
    have : (N' : ℤ) * ((p : ℤ) ^ j * t) = t * (N : ℤ) := by rw [← hjN]; push_cast; ring
    rw [this, ← smul_smul]
    exact Submodule.smul_mem _ t hNz

theorem mPart_eq_of_le (hA : A.IsSymm) (hn : 1 ≤ n) (hW : (walkMatrix A).det ≠ 0)
    (hβ : β ∈ factorsSet (redP p A.charpoly)) {Λ Λ' : Submodule ℤ (Fin n → ℚ)}
    (hΛ : IsAStable A Λ) (hΛu : latDual Λ = Λ) (hCΛ : latC A ≤ Λ)
    (hΛ'u : latDual Λ' = Λ') (hCΛ' : latC A ≤ Λ')
    (hle : mPart A p β Λ ≤ mPart A p β Λ') : mPart A p β Λ = mPart A p β Λ' := by
  refine le_antisymm hle fun y hy => ?_
  have hΛ'C : Λ' ≤ latDual (latC A) := by
    have := latDual_anti hCΛ'; rwa [hΛ'u] at this
  have hyΛ : y ∈ Λ := by
    refine mem_of_forall_dot_mPart hA hn hW hβ hΛ hΛu hCΛ (mPart_mono hΛ'C hy) fun z hz => ?_
    have hy' : y ∈ latDual Λ' := by rw [hΛ'u]; exact hy.1
    exact isIntQ_of_mem_latDual hy' (hle hz).1
  exact ⟨hyΛ, hy.2⟩

end Pairing

end DGS
