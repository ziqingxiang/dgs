module

public import DGS.S07_Small.Tight

@[expose] public section

open Matrix Polynomial Filter Module

namespace DGS

section Upper

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem finrank_ker_aeval_pow_le (f : Module.End F V) {β : F[X]} (hβ : Irreducible β) {a : ℕ}
    (ha : ¬ β ^ (a + 1) ∣ f.charpoly) (k : ℕ) :
    finrank F (LinearMap.ker (aeval f (β ^ k))) ≤ a * β.natDegree := by
  set N := aeval f β with hN
  obtain ⟨m, hm, hm1⟩ :=
    ((N.eventually_isCompl_ker_pow_range_pow).and (eventually_ge_atTop (k + 1))).exists
  set P := LinearMap.ker (N ^ m) with hP
  set W := LinearMap.range (N ^ m) with hW
  have hcomm : Commute f (N ^ m) := (Commute.pow_right (aeval_mul_comm f β).symm m)
  have hcommx : ∀ y, (N ^ m) (f y) = f ((N ^ m) y) := by
    intro y
    have h := LinearMap.congr_fun hcomm.eq y
    simp only [Module.End.mul_apply] at h
    exact h.symm
  have hfP : ∀ x ∈ P, f x ∈ P := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hcommx, hx, map_zero]
  have hfW : ∀ x ∈ W, f x ∈ W := by
    rintro _ ⟨y, rfl⟩
    exact ⟨f y, hcommx y⟩
  set FP := f.restrict hfP with hFP
  set FW := f.restrict hfW with hFW
  set e := Submodule.prodEquivOfIsCompl P W hm with he
  have hψ : FP.prodMap FW = e.symm.conj f := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply, LinearEquiv.symm_symm, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.eq_symm_apply,
      Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', LinearMap.prodMap_apply,
      LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply, map_add]
  have hχ : f.charpoly = FP.charpoly * FW.charpoly := by
    rw [← e.symm.charpoly_conj f, ← hψ, LinearMap.charpoly_prodMap]
  have hN0 : ∀ x : P, (aeval FP (β ^ m)) x = 0 := by
    intro x
    apply Subtype.ext
    rw [aeval_restrict_coe f hfP (β ^ m) x, map_pow, ZeroMemClass.coe_zero]
    exact x.2
  have hχP0 : FP.charpoly ≠ 0 := (LinearMap.charpoly_monic FP).ne_zero
  obtain ⟨e', g, hndvd, hfac⟩ := WfDvdMonoid.max_power_factor hχP0 hβ
  have hg0 : g ≠ 0 := by
    rintro rfl; rw [mul_zero] at hfac; exact hχP0 hfac
  have hgunit : IsUnit g := by
    by_contra hg
    obtain ⟨γ, hγi, hγg⟩ := WfDvdMonoid.exists_irreducible_factor hg hg0
    have hγχ : γ ∣ FP.charpoly := by rw [hfac]; exact dvd_mul_of_dvd_right hγg _
    apply not_injective_aeval_of_dvd_charpoly FP hγi hγχ
    have hcop : IsCoprime γ (β ^ m) := by
      have h1 : IsCoprime γ β := by
        rw [Irreducible.coprime_iff_not_dvd hγi]
        intro hγβ
        exact hndvd ((hγi.dvd_symm hβ hγβ).trans hγg)
      exact h1.pow_right
    obtain ⟨s, t, hst⟩ := hcop
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 := LinearMap.congr_fun (congrArg (aeval FP) hst) x
    rw [map_add, map_mul, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.one_apply, hx, map_zero, zero_add, hN0 x, map_zero] at h1
    exact h1.symm
  have hdeg : FP.charpoly.natDegree = e' * β.natDegree := by
    rw [hfac, natDegree_mul (pow_ne_zero _ hβ.ne_zero) hg0, natDegree_pow,
      natDegree_eq_zero_of_isUnit hgunit, add_zero]
  have he'a : e' ≤ a := by
    by_contra h
    push Not at h
    apply ha
    have h1 : β ^ (a + 1) ∣ β ^ e' := pow_dvd_pow β h
    have h2 : β ^ e' ∣ f.charpoly := by
      rw [hχ, hfac, mul_assoc]; exact dvd_mul_right _ _
    exact h1.trans h2
  have hle : LinearMap.ker (aeval f (β ^ k)) ≤ P := by
    rw [map_pow, hP]
    exact ker_pow_mono N (by omega)
  calc finrank F (LinearMap.ker (aeval f (β ^ k))) ≤ finrank F P := Submodule.finrank_mono hle
    _ = FP.charpoly.natDegree := (LinearMap.charpoly_natDegree FP).symm
    _ = e' * β.natDegree := hdeg
    _ ≤ a * β.natDegree := Nat.mul_le_mul_right _ he'a

end Upper

section Mult

variable {F : Type*} [Field F] {φ : F[X]}

theorem not_pow_succ_mult_dvd (hφ : φ.Monic) {β : F[X]} (hβ : β ∈ factorsSet φ) :
    ¬ β ^ (mult φ β + 1) ∣ φ := by
  intro h
  have hβi := irreducible_of_mem_factorsSet hβ
  have h1 : β ^ mult φ β * β ∣ β ^ mult φ β * cofactor φ β := by
    rw [← pow_succ, pow_mul_cofactor hφ hβ]
    exact h
  have h2 : β ∣ cofactor φ β := (mul_dvd_mul_iff_left (pow_ne_zero _ hβi.ne_zero)).1 h1
  have h3 := isCoprime_pow_cofactor hβ
  have h4 : β ∣ β ^ mult φ β := dvd_pow_self β (mult_pos hβ).ne'
  exact hβi.not_isUnit (h3.isUnit_of_dvd' h4 h2)

end Mult

section MatrixDim

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

theorem finrank_ker_eq_of_exact {F : Type*} [Field F] (M : Matrix (Fin n) (Fin n) F) {β : F[X]}
    (hβ : Irreducible β) {a : ℕ} (hdvd : β ^ a ∣ M.charpoly) (hndvd : ¬ β ^ (a + 1) ∣ M.charpoly) :
    finrank F (LinearMap.ker (aeval (Matrix.toLin' M) (β ^ a))) = a * β.natDegree := by
  apply le_antisymm
  · exact finrank_ker_aeval_pow_le (Matrix.toLin' M) hβ (by rw [charpoly_toLin']; exact hndvd) a
  · exact finrank_ker_aeval_pow_ge (Matrix.toLin' M) hβ (by rw [charpoly_toLin']; exact hdvd)

end MatrixDim

section Vanish

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} {p : ℕ} [hp : Fact p.Prime]

theorem mem_latC_of_not_dvd {β : (ZMod p)[X]} (hβi : Irreducible β)
    (hβ : ¬ β ∣ redP p A.charpoly) {y : Fin n → ℚ} (hy : y ∈ mPart A p β (latZ n)) :
    y ∈ latC A := by
  obtain ⟨-, k, hk1, hk2⟩ := hy
  have hφ : A.charpoly ∈ annC A y := charpoly_mem_annC y
  have hcop : IsCoprime (β ^ k) (redP p A.charpoly) :=
    ((Irreducible.coprime_iff_not_dvd hβi).2 hβ).pow_left
  obtain ⟨a, b, hab⟩ := hcop
  set u : ℤ[X] := liftZ p a * liftZ p β ^ k + liftZ p b * A.charpoly with hu
  have hu_mem : u ∈ annC A y :=
    add_mem (Ideal.mul_mem_left _ _ hk2) (Ideal.mul_mem_left _ _ hφ)
  have h1 : C (p : ℤ) ∣ 1 - u := by
    rw [← map_eq_zero_iff_C_dvd]
    rw [Polynomial.map_sub, Polynomial.map_one, hu, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_pow, map_liftZ, map_liftZ, map_liftZ]
    rw [show redP p A.charpoly = A.charpoly.map (Int.castRingHom (ZMod p)) from rfl] at hab
    rw [hab, sub_self]
  obtain ⟨h, hh⟩ := h1
  have h2 : (1 - u) ^ k ∈ annC A y := by
    rw [hh, mul_pow, ← C_pow]
    exact Ideal.mul_mem_right _ _ hk1
  have h3 : (1 - u) ^ k - 1 ∈ annC A y := by
    obtain ⟨w, hw⟩ := sub_one_dvd_pow_sub_one (1 - u) k
    rw [hw, show (1 - u - 1) = -u by ring, neg_mul]
    exact neg_mem (Ideal.mul_mem_right _ _ hu_mem)
  have h4 : (1 : ℤ[X]) ∈ annC A y := by
    have : (1 : ℤ[X]) = (1 - u) ^ k - ((1 - u) ^ k - 1) := by ring
    rw [this]
    exact sub_mem h2 h3
  exact one_mem_annC.1 h4

end Vanish

end DGS
