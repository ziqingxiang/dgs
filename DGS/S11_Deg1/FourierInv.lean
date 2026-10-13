module

public import DGS.S11_Deg1.PTdef
public import DGS.S06_Fourier.FourierBound

@[expose] public section

open Finset Matrix
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime]

theorem prob_eq_le_fourier {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]
    (X : Ω → ι → ZMod p) (a : ι → ZMod p) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ τ : ι → ZMod p, τ ≠ 0 →
      ‖(Fintype.card Ω : ℂ)⁻¹ * ∑ ω, ZMod.stdAddChar (∑ i, τ i * X ω i)‖ ≤ ε) :
    prob (fun ω => X ω = a) ≤ ((p : ℝ) ^ Fintype.card ι)⁻¹ + ε := by
  classical
  set k := Fintype.card ι with hk
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpk : ((p : ℂ) ^ k) ≠ 0 := pow_ne_zero _ hp0
  have hΩ0 : (Fintype.card Ω : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set Φ : (ι → ZMod p) → ℂ := fun τ =>
    (Fintype.card Ω : ℂ)⁻¹ * ∑ ω, ZMod.stdAddChar (∑ i, τ i * X ω i) with hΦ
  have hind : ∀ ω, (if X ω = a then (1 : ℂ) else 0) = ((p : ℂ) ^ k)⁻¹ *
      ∑ τ : ι → ZMod p, ZMod.stdAddChar (-(∑ i, τ i * a i)) * ZMod.stdAddChar (∑ i, τ i * X ω i) := by
    intro ω
    have h := sum_stdAddChar_dot (q := p) (X ω - a)
    have e : ∀ τ : ι → ZMod p, ZMod.stdAddChar (∑ i, τ i * (X ω - a) i) =
        ZMod.stdAddChar (-(∑ i, τ i * a i)) * ZMod.stdAddChar (∑ i, τ i * X ω i) := by
      intro τ
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [Pi.sub_apply, mul_sub, sum_sub_distrib]
      ring
    simp_rw [e] at h
    rw [h]
    by_cases hX : X ω = a
    · rw [ite_eq_left hX, ite_eq_left (sub_eq_zero.2 hX), inv_mul_cancel₀ hpk]
    · rw [ite_eq_right hX, ite_eq_right (fun h' => hX (sub_eq_zero.1 h')), mul_zero]
  have hprob : ((prob fun ω => X ω = a : ℝ) : ℂ) =
      ((p : ℂ) ^ k)⁻¹ * ∑ τ : ι → ZMod p, ZMod.stdAddChar (-(∑ i, τ i * a i)) * Φ τ := by
    have hcard : (Nat.card {ω // X ω = a} : ℂ) = ∑ ω, if X ω = a then (1 : ℂ) else 0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]
    unfold prob
    push_cast
    rw [hcard, Nat.card_eq_fintype_card]
    simp_rw [hind]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [hΦ]
    rw [mul_div_assoc, div_eq_mul_inv, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.mul_sum]
    ring
  have hΦle : ∀ τ, ‖Φ τ‖ ≤ 1 := by
    intro τ
    rw [hΦ, norm_mul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_le_iff₀ (by exact_mod_cast Fintype.card_pos)]
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_stdAddChar, sum_const, card_univ, nsmul_eq_mul, mul_one, le_refl]
  have hnorm : prob (fun ω => X ω = a) = ‖((prob fun ω => X ω = a : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (prob_nonneg _)]
  have hsum : ∑ τ : ι → ZMod p, ‖ZMod.stdAddChar (-(∑ i, τ i * a i)) * Φ τ‖ ≤
      1 + (((p : ℝ) ^ k) - 1) * ε := by
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : ι → ZMod p))]
    have h0 : ‖ZMod.stdAddChar (-(∑ i, (0 : ι → ZMod p) i * a i)) * Φ 0‖ ≤ 1 := by
      rw [norm_mul, norm_stdAddChar, one_mul]
      exact hΦle 0
    have h1 : ∑ τ ∈ univ.erase (0 : ι → ZMod p), ‖ZMod.stdAddChar (-(∑ i, τ i * a i)) * Φ τ‖ ≤
        ∑ τ ∈ univ.erase (0 : ι → ZMod p), ε := by
      refine sum_le_sum fun τ hτ => ?_
      rw [norm_mul, norm_stdAddChar, one_mul]
      exact hε τ (ne_of_mem_erase hτ)
    have h2 : ∑ τ ∈ univ.erase (0 : ι → ZMod p), ε = (((p : ℝ) ^ k) - 1) * ε := by
      rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fun, ZMod.card,
        nsmul_eq_mul, ← hk]
      have : 1 ≤ p ^ k := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
      push_cast [this]
      ring
    linarith
  have hpkR : (0 : ℝ) < (p : ℝ) ^ k := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  rw [hnorm, hprob, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc ((p : ℝ) ^ k)⁻¹ * ‖∑ τ : ι → ZMod p, ZMod.stdAddChar (-(∑ i, τ i * a i)) * Φ τ‖
      ≤ ((p : ℝ) ^ k)⁻¹ * (1 + (((p : ℝ) ^ k) - 1) * ε) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans hsum) (by positivity)
    _ = ((p : ℝ) ^ k)⁻¹ + ε - ((p : ℝ) ^ k)⁻¹ * ε := by
        field_simp
        ring
    _ ≤ ((p : ℝ) ^ k)⁻¹ + ε := by
        have : 0 ≤ ((p : ℝ) ^ k)⁻¹ * ε := mul_nonneg (by positivity) hε0
        linarith

variable {m : ℕ}

theorem sgnP_eq_twoValued (ξ : Fin m → Bool) : sgnP p ξ = twoValued (1 : ZMod p) (-1) ξ := by
  funext j
  simp only [sgnP, twoValued]
  cases ξ j <;> simp

theorem prob_quad_eq_le (B : Matrix (Fin m) (Fin m) (ZMod p)) (a : ZMod p) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ t : ZMod p, t ≠ 0 → ‖quadSum B t‖ ≤ ε) :
    prob (fun ξ : Fin m → Bool => sgnP p ξ ⬝ᵥ (B *ᵥ sgnP p ξ) = a) ≤ 1 / p + ε := by
  have h := prob_eq_le_fourier (Ω := Fin m → Bool) (ι := Fin 1)
    (fun ξ _ => sgnP p ξ ⬝ᵥ (B *ᵥ sgnP p ξ)) (fun _ => a) hε0 (fun τ hτ => by
      have hτ0 : τ 0 ≠ 0 := by
        intro h0
        apply hτ
        funext i
        rw [Subsingleton.elim i 0, h0]
        rfl
      have e : (Fintype.card (Fin m → Bool) : ℂ)⁻¹ *
          ∑ ξ : Fin m → Bool, ZMod.stdAddChar (∑ i : Fin 1, τ i * (sgnP p ξ ⬝ᵥ (B *ᵥ sgnP p ξ))) =
            quadSum B (τ 0) := by
        unfold quadSum
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        push_cast
        simp
      rw [e]
      exact hε _ hτ0)
  rw [Fintype.card_fin, pow_one, ← one_div] at h
  refine le_trans (le_of_eq (prob_congr fun ξ => ?_)) h
  constructor
  · intro h1
    funext i
    exact h1
  · intro h1
    exact congrFun h1 0

theorem prob_quad2_eq_le (B B' : Matrix (Fin m) (Fin m) (ZMod p)) (a b : ZMod p) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ t t' : ZMod p, (t ≠ 0 ∨ t' ≠ 0) → ‖quadSum (t • B + t' • B') 1‖ ≤ ε) :
    prob (fun ξ : Fin m → Bool => sgnP p ξ ⬝ᵥ (B *ᵥ sgnP p ξ) = a ∧
      sgnP p ξ ⬝ᵥ (B' *ᵥ sgnP p ξ) = b) ≤ 1 / (p : ℝ) ^ 2 + ε := by
  have h := prob_eq_le_fourier (Ω := Fin m → Bool) (ι := Fin 2)
    (fun ξ => ![sgnP p ξ ⬝ᵥ (B *ᵥ sgnP p ξ), sgnP p ξ ⬝ᵥ (B' *ᵥ sgnP p ξ)]) ![a, b] hε0
    (fun τ hτ => by
      have hτ0 : τ 0 ≠ 0 ∨ τ 1 ≠ 0 := by
        by_contra h0
        push Not at h0
        apply hτ
        funext i
        fin_cases i
        · exact h0.1
        · exact h0.2
      have h3 := hε (τ 0) (τ 1) hτ0
      rw [quadSum_add_smul] at h3
      have e : (Fintype.card (Fin m → Bool) : ℂ)⁻¹ * ∑ ξ : Fin m → Bool, ZMod.stdAddChar
          (∑ i : Fin 2, τ i * ![sgnP p ξ ⬝ᵥ (B *ᵥ sgnP p ξ), sgnP p ξ ⬝ᵥ (B' *ᵥ sgnP p ξ)] i) =
            ((2 : ℂ) ^ m)⁻¹ * ∑ ξ : Fin m → Bool, ZMod.stdAddChar
              (τ 0 * (sgnP p ξ ⬝ᵥ (B *ᵥ sgnP p ξ)) + τ 1 * (sgnP p ξ ⬝ᵥ (B' *ᵥ sgnP p ξ))) := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        push_cast
        simp [Fin.sum_univ_two]
      rw [e]
      exact h3)
  rw [Fintype.card_fin, ← one_div] at h
  refine le_trans (le_of_eq (prob_congr fun ξ => ?_)) h
  constructor
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i
    · exact h1
    · exact h2
  · intro h1
    exact ⟨congrFun h1 0, congrFun h1 1⟩

theorem prob_perp_le (K : Submodule (ZMod p) (Fin m → ZMod p)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ v ∈ K, v ≠ 0 → ∏ j, |cosP (v j)| ≤ ε) :
    prob (fun ξ : Fin m → Bool => ∀ k ∈ K, twoValued (1 : ZMod p) (-1) ξ ⬝ᵥ k = 0) ≤
      ((p : ℝ) ^ Module.finrank (ZMod p) K)⁻¹ + ε := by
  classical
  set r := Module.finrank (ZMod p) K with hr
  let b := Module.finBasisOfFinrankEq (ZMod p) K hr.symm
  set w : Fin m → Fin r → ZMod p := fun j i => (b i : Fin m → ZMod p) j with hw
  have hev : ∀ ξ : Fin m → Bool, (∀ k ∈ K, twoValued (1 : ZMod p) (-1) ξ ⬝ᵥ k = 0) ↔ sgnSum w ξ = 0 := by
    intro ξ
    have hcoord : ∀ i, sgnSum w ξ i = twoValued (1 : ZMod p) (-1) ξ ⬝ᵥ (b i : Fin m → ZMod p) := by
      intro i
      simp only [sgnSum, Finset.sum_apply, Pi.smul_apply, hw, dotProduct, twoValued]
      refine Finset.sum_congr rfl fun j _ => ?_
      cases ξ j <;> simp
    constructor
    · intro h
      funext i
      rw [hcoord, Pi.zero_apply]
      exact h _ (b i).2
    · intro h k hk
      have hspan : (⟨k, hk⟩ : K) = ∑ i, b.repr ⟨k, hk⟩ i • b i := (b.sum_repr _).symm
      have hk' : k = ∑ i, b.repr ⟨k, hk⟩ i • (b i : Fin m → ZMod p) := by
        have h1 : ((⟨k, hk⟩ : K) : Fin m → ZMod p) =
            ((∑ i, b.repr ⟨k, hk⟩ i • b i : K) : Fin m → ZMod p) := congrArg Subtype.val hspan
        rw [Submodule.coe_sum] at h1
        simpa only [Submodule.coe_smul] using h1
      rw [hk', dotProduct_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [dotProduct_smul, ← hcoord, h, Pi.zero_apply, smul_zero]
  have hvec : ∀ τ : Fin r → ZMod p, ∀ j, τ ⬝ᵥ w j = (∑ i, τ i • (b i : Fin m → ZMod p)) j := by
    intro τ j
    simp [dotProduct, hw, Finset.sum_apply]
  have hmem : ∀ τ : Fin r → ZMod p, (∑ i, τ i • (b i : Fin m → ZMod p)) ∈ K := fun τ =>
    K.sum_mem fun i _ => K.smul_mem _ (b i).2
  have hne : ∀ τ : Fin r → ZMod p, τ ≠ 0 → (∑ i, τ i • (b i : Fin m → ZMod p)) ≠ 0 := by
    intro τ hτ h0
    apply hτ
    have h1 : (∑ i, τ i • b i : K) = 0 := by
      apply Subtype.ext
      simpa using h0
    have := (Fintype.linearIndependent_iff.1 b.linearIndependent) τ h1
    funext i
    exact this i
  have hrho : rhoHat w ≤ ((p : ℝ) ^ r)⁻¹ + ε := by
    unfold rhoHat
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : Fin r → ZMod p))]
    have h0 : ∏ j, |cosP ((0 : Fin r → ZMod p) ⬝ᵥ w j)| = 1 := by
      simp [cosP]
    have h1 : ∑ τ ∈ univ.erase (0 : Fin r → ZMod p), ∏ j, |cosP (τ ⬝ᵥ w j)| ≤
        ∑ τ ∈ univ.erase (0 : Fin r → ZMod p), ε := by
      refine sum_le_sum fun τ hτ => ?_
      simp_rw [hvec τ]
      exact hε _ (hmem τ) (hne τ (ne_of_mem_erase hτ))
    have h2 : ∑ τ ∈ univ.erase (0 : Fin r → ZMod p), ε = (((p : ℝ) ^ r) - 1) * ε := by
      rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fun, ZMod.card,
        Fintype.card_fin, nsmul_eq_mul]
      have : 1 ≤ p ^ r := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
      push_cast [this]
      ring
    have hp : (0 : ℝ) < (p : ℝ) ^ r := by
      have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      positivity
    rw [h0]
    calc ((p : ℝ) ^ r)⁻¹ * (1 + ∑ τ ∈ univ.erase (0 : Fin r → ZMod p), ∏ j, |cosP (τ ⬝ᵥ w j)|)
        ≤ ((p : ℝ) ^ r)⁻¹ * (1 + (((p : ℝ) ^ r) - 1) * ε) := by
          gcongr
          linarith
      _ = ((p : ℝ) ^ r)⁻¹ + ε - ((p : ℝ) ^ r)⁻¹ * ε := by
          field_simp
          ring
      _ ≤ ((p : ℝ) ^ r)⁻¹ + ε := by
          have : 0 ≤ ((p : ℝ) ^ r)⁻¹ * ε := mul_nonneg (by positivity) hε0
          linarith
  calc prob (fun ξ : Fin m → Bool => ∀ k ∈ K, twoValued (1 : ZMod p) (-1) ξ ⬝ᵥ k = 0)
      = prob (fun ξ : Fin m → Bool => sgnSum w ξ = 0) := prob_congr hev
    _ ≤ rhoG w := prob_sgnSum_le_rhoG w 0
    _ ≤ rhoHat w := rhoG_le_rhoHat w
    _ ≤ ((p : ℝ) ^ r)⁻¹ + ε := hrho

end DGS
