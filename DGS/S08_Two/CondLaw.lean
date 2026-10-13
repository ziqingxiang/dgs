module

public import DGS.S08_Two.PolyCount

@[expose] public section

open Matrix Polynomial Module

namespace DGS

section QFormSym

variable {R : Type*} [CommRing R] {n : ℕ}

theorem qForm_add_transpose (C : Matrix (Fin n) (Fin n) R) (y : Fin n → R) :
    qForm (C + Cᵀ) y + ∑ i, C i i * y i * y i = y ⬝ᵥ (C *ᵥ y) := by
  simp only [qForm, upperPart, dotProduct, mulVec, Matrix.add_apply, transpose_apply, of_apply,
    Finset.mul_sum]
  have hsplit : ∀ i l : Fin n, y i * (C i l * y l) =
      (if i < l then y i * C i l * y l else 0) + (if l < i then y i * C i l * y l else 0) +
        (if i = l then y i * C i l * y l else 0) := by
    intro i l
    rcases lt_trichotomy i l with h | rfl | h
    · rw [ite_eq_left h, ite_eq_right (not_lt.2 h.le), ite_eq_right h.ne]; ring
    · simp only [lt_irrefl, ite_false, ite_true, zero_add]; ring
    · rw [ite_eq_right (not_lt.2 h.le), ite_eq_left h, ite_eq_right h.ne']; ring
  have hL : ∀ i l : Fin n, y i * ((if i < l then C i l + C l i else 0) * y l) =
      (if i < l then y i * C i l * y l else 0) + (if i < l then y l * C l i * y i else 0) := by
    intro i l
    split_ifs <;> ring
  simp_rw [hL, hsplit, Finset.sum_add_distrib]
  have hswap : ∑ i : Fin n, ∑ l : Fin n, (if i < l then y l * C l i * y i else 0) =
      ∑ i : Fin n, ∑ l : Fin n, (if l < i then y i * C i l * y l else 0) := Finset.sum_comm
  rw [hswap]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  ring

end QFormSym

section F2

variable {n : ℕ}

local notation "V" => Fin n → ZMod 2
local notation "Mat" => Matrix (Fin n) (Fin n) (ZMod 2)

theorem qForm_sym_vecMulVec (u u' h : V) :
    qForm (vecMulVec u u' + vecMulVec u' u) h = (u ⬝ᵥ h) * (u' ⬝ᵥ h) + (u * u') ⬝ᵥ h := by
  have h1 := qForm_add_transpose (vecMulVec u u') h
  rw [transpose_vecMulVec] at h1
  have h2 : h ⬝ᵥ (vecMulVec u u' *ᵥ h) = (u ⬝ᵥ h) * (u' ⬝ᵥ h) := by
    simp only [dotProduct, mulVec, vecMulVec_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have h3 : ∑ i, vecMulVec u u' i i * h i * h i = (u * u') ⬝ᵥ h := by
    simp only [vecMulVec_apply, dotProduct, Pi.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := ZMod.pow_card (h i)
    rw [sq] at this
    rw [mul_assoc, this]
  rw [h2, h3] at h1
  have h2' : (2 : ZMod 2) = 0 := rfl
  linear_combination h1 - ((u * u') ⬝ᵥ h) * h2'

def prodSpan (K : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {x | ∃ u ∈ orthC K, ∃ u' ∈ orthC K, x = u * u'}

def BadK (K : Submodule (ZMod 2) V) : Prop :=
  ¬ orthC (Submodule.span (ZMod 2) {ones n (ZMod 2)}) ≤ prodSpan K

theorem vecMulVec_sym_mem_altKill {K : Submodule (ZMod 2) V} {u u' : V} (hu : u ∈ orthC K)
    (hu' : u' ∈ orthC K) : vecMulVec u u' + vecMulVec u' u ∈ altKill K := by
  refine ⟨?_, ?_, ?_⟩
  · rw [transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_comm]
  · intro i
    simp only [Matrix.add_apply, vecMulVec_apply]
    rw [mul_comm (u' i), ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  · intro y hy
    rw [add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, dotProduct_comm u', dotProduct_comm u,
      hu y hy, hu' y hy]
    simp

theorem aeval_mulVec_eq_of_sub_mem {M₀ M : Mat} (h : M - M₀ ∈ altKill (cyc M₀ (ones n (ZMod 2))))
    (g : (ZMod 2)[X]) : aeval M g *ᵥ ones n (ZMod 2) = aeval M₀ g *ᵥ ones n (ZMod 2) := by
  have hpow : ∀ i : ℕ, M ^ i *ᵥ ones n (ZMod 2) = M₀ ^ i *ᵥ ones n (ZMod 2) := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, pow_succ', ← mulVec_mulVec]
      have hmem : M₀ ^ i *ᵥ ones n (ZMod 2) ∈ cyc M₀ (ones n (ZMod 2)) :=
        ⟨X ^ i, by rw [evalVec_apply, map_pow, aeval_X]⟩
      have hB := h.2.2 _ hmem
      have : M = M₀ + (M - M₀) := by abel
      rw [this, add_mulVec, hB, add_zero]
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_mulVec, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mulVec, smul_mulVec, hpow]

theorem muVec_eq_of_sub_mem {M₀ M : Mat} (h : M - M₀ ∈ altKill (cyc M₀ (ones n (ZMod 2)))) :
    muVec M (ones n (ZMod 2)) = muVec M₀ (ones n (ZMod 2)) := by
  apply muVec_eq_of M _ (muVec_monic _ _)
  intro g
  rw [aeval_mulVec_eq_of_sub_mem h, muVec_dvd_iff]

theorem cyc_eq_of_sub_mem {M₀ M : Mat} (h : M - M₀ ∈ altKill (cyc M₀ (ones n (ZMod 2)))) :
    cyc M (ones n (ZMod 2)) = cyc M₀ (ones n (ZMod 2)) := by
  ext y
  rw [mem_cyc, mem_cyc]
  simp only [aeval_mulVec_eq_of_sub_mem h]

def ZEv (M : Mat) (β : (ZMod 2)[X]) : Prop :=
  β ∣ muVec M (ones n (ZMod 2)) ∧ ∀ r : (ZMod 2)[X], r.degree < β.degree →
    qForm (offDiag n (ZMod 2))
        (aeval M (contract 2 (muVec M (ones n (ZMod 2)) ^ 2 /ₘ β * r)) *ᵥ ones n (ZMod 2)) +
      qForm M (aeval M (contract 2 (divX (muVec M (ones n (ZMod 2)) ^ 2 /ₘ β * r))) *ᵥ
        ones n (ZMod 2)) = 0

theorem forall_deg_lt_iff (Λ : (ZMod 2)[X] →+ ZMod 2) (d : ℕ) :
    (∀ r : (ZMod 2)[X], r.degree < d → Λ r = 0) ↔ ∀ i : Fin d, Λ (X ^ (i : ℕ)) = 0 := by
  constructor
  · intro h i
    apply h
    rw [degree_X_pow]
    exact_mod_cast i.2
  · intro h r hr
    by_cases hr0 : r = 0
    · rw [hr0, map_zero]
    have hnd : r.natDegree < d := (natDegree_lt_iff_degree_lt hr0).2 hr
    rw [as_sum_range' r d hnd, map_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    rcases zmod2_cases (r.coeff i) with h0 | h1
    · rw [h0, monomial_zero_right, map_zero]
    · rw [h1, ← C_mul_X_pow_eq_monomial, C_1, one_mul]
      exact h ⟨i, Finset.mem_range.1 hi⟩

theorem upperPart_smul (c : ZMod 2) (B : Mat) : upperPart (c • B) = c • upperPart B := by
  ext i l
  simp only [upperPart, of_apply, Matrix.smul_apply]
  split_ifs <;> simp

def qVecMap {d : ℕ} (b : Fin d → V) : Mat →ₗ[ZMod 2] (Fin d → ZMod 2) where
  toFun M := fun i => qForm M (b i)
  map_add' M M' := by funext i; exact qForm_add_left M M' (b i)
  map_smul' c M := by
    funext i
    simp only [qForm, upperPart_smul, smul_mulVec, dotProduct_smul, Pi.smul_apply,
      RingHom.id_apply]

theorem qVecMap_apply {d : ℕ} (b : Fin d → V) (M : Mat) (i : Fin d) :
    qVecMap b M i = qForm M (b i) := rfl

theorem zmod2_add_eq_zero_iff {x y : ZMod 2} : x + y = 0 ↔ y = x := by
  revert x y
  decide

theorem contract_two_zero : contract 2 (0 : (ZMod 2)[X]) = 0 := by
  ext j
  simp [coeff_contract]

theorem ones_ne_zero' (hn : 1 ≤ n) : ones n (ZMod 2) ≠ 0 := by
  intro h
  have := congrFun h ⟨0, hn⟩
  simp [ones] at this

section Step2

variable {M₀ : Matrix (Fin n) (Fin n) (ZMod 2)} (hM₀ : IsAlt M₀) {β : (ZMod 2)[X]} (hβm : β.Monic)
  (hβ : Irreducible β) (hβμ : β ∣ muVec M₀ (ones n (ZMod 2)))
include hM₀ hβm hβ hβμ

omit hM₀ in
theorem b_eq_zero_imp {r : (ZMod 2)[X]} (hr : r.degree < β.degree)
    (h0 : aeval M₀ (contract 2 (divX (muVec M₀ (ones n (ZMod 2)) ^ 2 /ₘ β * r))) *ᵥ
      ones n (ZMod 2) = 0) : r = 0 := by
  set μ := muVec M₀ (ones n (ZMod 2)) with hμ
  have hμm : μ.Monic := muVec_monic _ _
  by_contra hr0
  have hβf : β ∈ factorsSet μ := mem_factorsSet_of_dvd hμm hβm hβ hβμ
  set c := mult μ β with hc
  have hc1 : 1 ≤ c := mult_pos hβf
  have hcof := pow_mul_cofactor hμm hβf
  have hg : ¬ β ∣ cofactor μ β := by
    intro h
    have h1 : β ∣ β ^ c := dvd_pow_self β (by omega)
    exact hβ.not_isUnit ((isCoprime_pow_cofactor hβf).isUnit_of_dvd' h1 h)
  have hrβ : ¬ β ∣ r := by
    intro h
    have := natDegree_le_of_dvd h hr0
    have hr' := (natDegree_lt_iff_degree_lt hr0).2
      (by rwa [degree_eq_natDegree hβm.ne_zero] at hr)
    omega
  have hβsq : β ∣ μ ^ 2 := hβμ.trans (dvd_pow_self μ two_ne_zero)
  obtain ⟨hq1, -, -⟩ := quot_spec hβm (hμm.pow 2) hβsq
  set f := μ ^ 2 /ₘ β * r with hf
  have hfβ : f * β = μ ^ 2 * r := by
    rw [hf]
    calc μ ^ 2 /ₘ β * r * β = r * (β * (μ ^ 2 /ₘ β)) := by ring
      _ = μ ^ 2 * r := by rw [hq1]; ring
  have hsoc := (lem_socle hβ hc1 hcof.symm hg hrβ hfβ (sq_decomp f)).2
  apply hsoc
  have hdvd : μ ∣ contract 2 (divX f) := (muVec_dvd_iff M₀ _).2 h0
  have hβcμ : β ^ c ∣ μ := Dvd.intro _ hcof
  exact hβcμ.trans hdvd

theorem step2_count (hn : 1 ≤ n) (hB : ¬ BadK (cyc M₀ (ones n (ZMod 2)))) :
    Nat.card {M : Matrix (Fin n) (Fin n) (ZMod 2) //
        M - M₀ ∈ altKill (cyc M₀ (ones n (ZMod 2))) ∧ ZEv M β} * 2 ^ (β.natDegree - 1) ≤
      Nat.card {M : Matrix (Fin n) (Fin n) (ZMod 2) //
        M - M₀ ∈ altKill (cyc M₀ (ones n (ZMod 2)))} := by
  set e := ones n (ZMod 2) with he
  set K := cyc M₀ e with hK
  set μ := muVec M₀ e with hμ
  set U := altKill K with hU
  set d := β.natDegree with hd
  set c₀ := μ ^ 2 /ₘ β with hc₀
  set a : (ZMod 2)[X] → V := fun r => aeval M₀ (contract 2 (c₀ * r)) *ᵥ e with ha
  set b : (ZMod 2)[X] → V := fun r => aeval M₀ (contract 2 (divX (c₀ * r))) *ᵥ e with hb
  set bv : Fin d → V := fun i => b (X ^ (i : ℕ)) with hbv
  set Φ := qVecMap bv with hΦ
  set y : Fin d → ZMod 2 := fun i => qForm (offDiag n (ZMod 2)) (a (X ^ (i : ℕ))) with hy
  have hbadd : ∀ r r', b (r + r') = b r + b r' := by
    intro r r'
    simp only [hb, mul_add, contract_two_divX_add, map_add, add_mulVec]
  have haadd : ∀ r r', a (r + r') = a r + a r' := by
    intro r r'
    simp only [ha, mul_add, contract_two_add, map_add, add_mulVec]
  have hdeg : β.degree = (d : WithBot ℕ) := degree_eq_natDegree hβm.ne_zero
  have hA : ∀ M, M - M₀ ∈ U → (ZEv M β ↔ Φ M = y) := by
    intro M hMU
    have hMalt : IsAlt M := by
      have := hM₀.add ⟨hMU.1, hMU.2.1⟩
      rwa [add_sub_cancel] at this
    have hμM : muVec M e = μ := muVec_eq_of_sub_mem hMU
    have hev : ∀ g, aeval M g *ᵥ e = aeval M₀ g *ᵥ e := aeval_mulVec_eq_of_sub_mem hMU
    have hcycM : cyc M e = K := cyc_eq_of_sub_mem hMU
    let Λ : (ZMod 2)[X] →+ ZMod 2 :=
      { toFun := fun r => qForm (offDiag n (ZMod 2)) (a r) + qForm M (b r)
        map_zero' := by simp [ha, hb, contract_two_zero]
        map_add' := by
          intro r r'
          rw [haadd, hbadd, qForm_add_cyc_J hM₀.1 hM₀.2 (aeval_mulVec_mem_cyc _ _ _)
            (aeval_mulVec_mem_cyc _ _ _), qForm_add_cyc_A hMalt.1 hMalt.2
            (by rw [hcycM]; exact aeval_mulVec_mem_cyc _ _ _)
            (by rw [hcycM]; exact aeval_mulVec_mem_cyc _ _ _)]
          ring }
    have hΛ : ∀ r, Λ r = qForm (offDiag n (ZMod 2)) (a r) + qForm M (b r) := fun r => rfl
    constructor
    · rintro ⟨-, h⟩
      funext i
      have := h (X ^ (i : ℕ)) (by rw [degree_X_pow, hdeg]; exact_mod_cast i.2)
      rw [hμM, hev, hev] at this
      exact zmod2_add_eq_zero_iff.1 this
    · intro hΦy
      refine ⟨by rw [hμM]; exact hβμ, fun r hr => ?_⟩
      rw [hμM, hev, hev]
      have hall : ∀ i : Fin d, Λ (X ^ (i : ℕ)) = 0 := by
        intro i
        rw [hΛ]
        exact zmod2_add_eq_zero_iff.2 (congrFun hΦy i)
      have := (forall_deg_lt_iff Λ d).2 hall r (by rwa [hdeg] at hr)
      rw [hΛ] at this
      exact this
  have hbind : LinearIndependent (ZMod 2) bv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let bA : (ZMod 2)[X] →+ V :=
      { toFun := b
        map_zero' := by simp [hb, contract_two_zero]
        map_add' := hbadd }
    have hlin : ∑ j, g j • bv j = b (polyOfFin g) := by
      have h1 : polyOfFin g = ∑ j, g j • (X : (ZMod 2)[X]) ^ (j : ℕ) := by
        simp only [polyOfFin, smul_eq_C_mul]
      have h2 : b (polyOfFin g) = bA (polyOfFin g) := rfl
      rw [h2, h1, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ZMod.map_smul]
      rfl
    rw [hlin] at hg
    have hr := b_eq_zero_imp hβm hβ hβμ (r := polyOfFin g)
      (by rw [hdeg]; exact degree_polyOfFin_lt g) hg
    have := congrArg (coeff · (i : ℕ)) hr
    simp only [coeff_polyOfFin, dite_eq_left i.2, coeff_zero] at this
    exact this
  set Ψ := Matrix.mulVecLin (Matrix.of bv) with hΨ
  have hkerΨ : LinearMap.ker Ψ = orthC (Submodule.span (ZMod 2) (Set.range bv)) := by
    ext z
    rw [LinearMap.mem_ker, mem_orthC_span_iff, hΨ, Matrix.mulVecLin_apply]
    constructor
    · intro h i
      have := congrFun h i
      simpa [mulVec, dotProduct] using this
    · intro h
      funext i
      simpa [mulVec, dotProduct] using h i
  have hdimker : finrank (ZMod 2) (LinearMap.ker Ψ) = n - d := by
    rw [hkerΨ, finrank_orthC_span hbind]
  set E := orthC (Submodule.span (ZMod 2) {ones n (ZMod 2)}) with hE
  have hdimE : finrank (ZMod 2) E = n - 1 := by
    have h1 : finrank (ZMod 2) (Submodule.span (ZMod 2) {ones n (ZMod 2)}) + finrank (ZMod 2) E = n :=
      finrank_orthC_add _
    have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) {ones n (ZMod 2)}) = 1 :=
      finrank_span_singleton (ones_ne_zero' hn)
    omega
  have hEmap : E.map Ψ ≤ U.map Φ := by
    rw [Submodule.map_le_iff_le_comap]
    have hprod : prodSpan K ≤ (U.map Φ).comap Ψ := by
      rw [prodSpan, Submodule.span_le]
      rintro _ ⟨u, hu, u', hu', rfl⟩
      refine ⟨vecMulVec u u' + vecMulVec u' u, vecMulVec_sym_mem_altKill hu hu', ?_⟩
      funext i
      have hbi : bv i ∈ K := aeval_mulVec_mem_cyc _ _ _
      rw [hΦ, qVecMap_apply, qForm_sym_vecMulVec]
      have h1 : u ⬝ᵥ bv i = 0 := by rw [dotProduct_comm]; exact hu _ hbi
      rw [h1, zero_mul, zero_add, hΨ, Matrix.mulVecLin_apply]
      simp only [mulVec, dotProduct, Matrix.of_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    exact (not_not.1 hB).trans hprod
  have hdn : d ≤ n := by
    have h1 := finrank_span_eq_card hbind
    rw [Fintype.card_fin] at h1
    have h2 := Submodule.finrank_le (Submodule.span (ZMod 2) (Set.range bv))
    rw [Module.finrank_fin_fun] at h2
    omega
  have hdimΨE : d - 1 ≤ finrank (ZMod 2) (E.map Ψ) := by
    have h1 := finrank_map_add_finrank_inf_ker' Ψ E
    rw [hdimE] at h1
    have h2 : finrank (ZMod 2) (E ⊓ LinearMap.ker Ψ : Submodule (ZMod 2) V) ≤ n - d := by
      rw [← hdimker]
      exact Submodule.finrank_mono inf_le_right
    omega
  have hdimΦ := hdimΨE.trans (Submodule.finrank_mono hEmap)
  have hcongr : Nat.card {M : Mat // M - M₀ ∈ U ∧ ZEv M β} =
      Nat.card {M : Mat // M - M₀ ∈ U ∧ Φ M = y} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun M =>
      ⟨fun h => ⟨h.1, (hA M h.1).1 h.2⟩, fun h => ⟨h.1, (hA M h.1).2 h.2⟩⟩)
  rw [hcongr, natCard_coset_fiber, natCard_coset, Nat.card_zmod]
  have hle := finrank_map_le' Φ U
  split_ifs
  · rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  · rw [zero_mul]
    exact Nat.zero_le _

end Step2

end F2

end DGS
