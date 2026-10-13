module

public import DGS.S11_Deg1.Rankp

@[expose] public section

open Finset Filter Topology Matrix Polynomial
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime]

theorem snoc_dotProduct_snoc {F : Type*} [CommRing F] {r : ℕ} (v v' : Fin r → F) (t t' : F) :
    (Fin.snoc v t : Fin (r + 1) → F) ⬝ᵥ Fin.snoc v' t' = v ⬝ᵥ v' + t * t' := by
  simp [dotProduct, Fin.sum_univ_castSucc]

def IsoK {m : ℕ} (μ : ZMod p) (ω : Pairs m → Bool) : Prop :=
  ∀ w ∈ LinearMap.ker (shiftedMat (F := ZMod p) 1 (-1) μ ω).mulVecLin, w ⬝ᵥ w = 0

def Rep1 {m : ℕ} (μ : ZMod p) (ω : Pairs m → Bool) : Prop :=
  geomMult 1 (-1) μ ω = 1 ∧ IsoK μ ω

omit [Fact (Nat.Prime p)] in
theorem modP_seidelOf_symm {m : ℕ} (ω : Pairs m → Bool) :
    (modP p (seidelOf ω))ᵀ = modP p (seidelOf ω) := by
  ext i j
  simp only [modP, transpose_apply, map_apply, seidelOf]
  rw [symOf_comm]

theorem repeated_iff {m : ℕ} (μ : ZMod p) (ω : Pairs m → Bool) :
    (X - C μ) ^ 2 ∣ (modP p (seidelOf ω)).charpoly ↔ 2 ≤ geomMult 1 (-1) μ ω ∨ Rep1 μ ω := by
  have heig : Module.End.eigenspace (toLin' (modP p (seidelOf ω))) μ =
      LinearMap.ker (shiftedMat (F := ZMod p) 1 (-1) μ ω).mulVecLin := by
    ext w
    rw [Module.End.mem_eigenspace_iff, toLin'_apply, LinearMap.mem_ker, mulVecLin_apply,
      shiftedMat_eq_modP, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
  rw [sq_dvd_charpoly_iff _ (modP_seidelOf_symm ω) μ, heig]
  rfl

theorem isUnit_det_of_geomMult_eq_zero {m : ℕ} (μ : ZMod p) (ω : Pairs m → Bool)
    (h0 : geomMult 1 (-1) μ ω = 0) : IsUnit (shiftedMat (F := ZMod p) 1 (-1) μ ω).det := by
  rw [isUnit_iff_ne_zero]
  intro hd
  obtain ⟨v, hv0, hv⟩ := (exists_mulVec_eq_zero_iff).2 hd
  have hpos : 0 < geomMult 1 (-1) μ ω := by
    unfold geomMult corank
    refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact hv
    · intro h
      exact hv0 (congrArg Subtype.val h)
  omega

theorem iso_step0 {m : ℕ} (hp23 : 23 ≤ p) (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (μ : ZMod p) (ω : Pairs m → Bool) (hPT : GoodPT (seidelOf ω)) (h0 : geomMult 1 (-1) μ ω = 0) :
    prob (fun ξ : Fin m → Bool => Rep1 μ (succPairs ω ξ)) ≤
      1 / (p : ℝ) ^ 2 + Real.exp (-(cPT * m) / 2) := by
  set L := shiftedMat (F := ZMod p) 1 (-1) μ ω with hL
  have hLT : Lᵀ = L := shiftedMat_transpose μ ω
  have hdet : IsUnit L.det := isUnit_det_of_geomMult_eq_zero μ ω h0
  have hLiT : (L⁻¹)ᵀ = L⁻¹ := by rw [transpose_nonsing_inv, hLT]
  have hsub : ∀ ξ : Fin m → Bool, Rep1 μ (succPairs ω ξ) →
      sgnP p ξ ⬝ᵥ (L⁻¹ *ᵥ sgnP p ξ) = -μ ∧ sgnP p ξ ⬝ᵥ ((L⁻¹ * L⁻¹) *ᵥ sgnP p ξ) = -1 := by
    rintro ξ ⟨h1, hiso⟩
    unfold geomMult corank at h1
    unfold IsoK at hiso
    rw [shiftedMat_succPairs] at h1 hiso
    set y := twoValued (1 : ZMod p) (-1) ξ with hy
    have hc : -μ = y ⬝ᵥ (L⁻¹ *ᵥ y) := (lem_border_inv hLT hdet).2.1.1 h1
    have hker := (lem_border_inv (c := -μ) (y := y) hLT hdet).2.2 hc
    have hx : (Fin.snoc (L⁻¹ *ᵥ y) (-1) : Fin (m + 1) → ZMod p) ∈
        LinearMap.ker (border L y (-μ)).mulVecLin := (hker _).2 ⟨1, by rw [one_smul]⟩
    have hxx := hiso _ hx
    rw [snoc_dotProduct_snoc] at hxx
    have e : (L⁻¹ *ᵥ y) ⬝ᵥ (L⁻¹ *ᵥ y) = y ⬝ᵥ ((L⁻¹ * L⁻¹) *ᵥ y) := by
      rw [mulVec_dotProduct_of_symm hLiT, mulVec_mulVec]
    rw [sgnP_eq_twoValued, ← hy]
    refine ⟨hc.symm, ?_⟩
    rw [← e]
    linear_combination hxx
  refine (prob_mono fun ξ h => hsub ξ h).trans ?_
  exact prob_quad2_eq_le _ _ _ _ (Real.exp_pos _).le fun t t' ht =>
    quadSum_pencil_le hPT hp23 hpm μ hdet ht

theorem iso_step1 {m : ℕ} (hp23 : 23 ≤ p) (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (μ : ZMod p) (ω : Pairs m → Bool) (hSE : GoodSE (seidelOf ω)) (h1 : geomMult 1 (-1) μ ω = 1) :
    prob (fun ξ : Fin m → Bool => Rep1 μ (succPairs ω ξ)) ≤
      (1 / p + Real.exp (-2 * cSE * m)) * @ite ℝ (IsoK μ ω) (Classical.dec _) 1 0 := by
  set L := shiftedMat (F := ZMod p) 1 (-1) μ ω with hL
  have hLT : Lᵀ = L := shiftedMat_transpose μ ω
  have hsub : ∀ ξ : Fin m → Bool, Rep1 μ (succPairs ω ξ) →
      (∀ k ∈ LinearMap.ker L.mulVecLin, twoValued (1 : ZMod p) (-1) ξ ⬝ᵥ k = 0) ∧ IsoK μ ω := by
    rintro ξ ⟨hr, hiso⟩
    have hstep := geomMult_succPairs μ ω ξ
    have hperp : ∀ k ∈ LinearMap.ker L.mulVecLin, twoValued (1 : ZMod p) (-1) ξ ⬝ᵥ k = 0 :=
      hstep.2.2.1 (by omega)
    refine ⟨hperp, ?_⟩
    obtain ⟨⟨y0, hy0⟩, -, hb1, hb2⟩ := lem_border_b (c := -μ) hLT hperp
    by_cases hc : -μ = twoValued (1 : ZMod p) (-1) ξ ⬝ᵥ y0
    · have h2 := (hb2 y0 hy0 hc).2
      have h3 : geomMult 1 (-1) μ (succPairs ω ξ) = corank L + 1 := by
        unfold geomMult
        rw [shiftedMat_succPairs]
        exact h2
      have h4 : geomMult 1 (-1) μ ω = corank L := rfl
      omega
    · have hker := (hb1 y0 hy0 hc).1
      intro w hw
      have hw' : (Fin.snoc w 0 : Fin (m + 1) → ZMod p) ∈
          LinearMap.ker (border L (twoValued (1 : ZMod p) (-1) ξ) (-μ)).mulVecLin :=
        (hker w 0).2 ⟨hw, rfl⟩
      unfold IsoK at hiso
      rw [shiftedMat_succPairs] at hiso
      have := hiso _ hw'
      rwa [snoc_dotProduct_snoc, mul_zero, add_zero] at this
  by_cases hI : IsoK μ ω
  · rw [ite_eq_left hI, mul_one]
    refine (prob_mono fun ξ h => (hsub ξ h).1).trans ?_
    have := rankp_hyp_ii hp23 hpm μ ω hSE
    rwa [h1, pow_one, ← one_div] at this
  · rw [ite_eq_right hI, mul_zero]
    refine le_of_eq ?_
    rw [prob_congr (Q := fun _ => False) fun ξ => ⟨fun h => hI (hsub ξ h).2, False.elim⟩, prob_false]

theorem iso_step {m : ℕ} (hp23 : 23 ≤ p) (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (μ : ZMod p) (ω : Pairs m → Bool) (hE : EvRK m ω) {ϖ : ℝ}
    (hϖ1 : Real.exp (-(cPT * m) / 2) ≤ ϖ) (hϖ2 : Real.exp (-2 * cSE * m) ≤ ϖ) :
    prob (fun ξ : Fin m → Bool => Rep1 μ (succPairs ω ξ)) ≤
      (1 / (p : ℝ) ^ 2 + ϖ) + (1 / p + ϖ) * @ite ℝ (Rep1 μ ω) (Classical.dec _) 1 0 +
        @ite ℝ (2 ≤ geomMult 1 (-1) μ ω) (Classical.dec _) 1 0 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hϖ0 : 0 ≤ ϖ := (Real.exp_pos _).le.trans hϖ1
  have hI0 : (0 : ℝ) ≤ @ite ℝ (Rep1 μ ω) (Classical.dec _) 1 0 := by split_ifs <;> norm_num
  have hI0' : (0 : ℝ) ≤ @ite ℝ (2 ≤ geomMult 1 (-1) μ ω) (Classical.dec _) 1 0 := by
    split_ifs <;> norm_num
  have hθ0 : (0 : ℝ) ≤ 1 / p + ϖ := by positivity
  obtain h | h | h : geomMult 1 (-1) μ ω = 0 ∨ geomMult 1 (-1) μ ω = 1 ∨ 2 ≤ geomMult 1 (-1) μ ω := by
    omega
  · have h1 := iso_step0 hp23 hpm μ ω hE.2 h
    have h2 : (0 : ℝ) ≤ (1 / p + ϖ) * @ite ℝ (Rep1 μ ω) (Classical.dec _) 1 0 := mul_nonneg hθ0 hI0
    linarith
  · have h1 := iso_step1 hp23 hpm μ ω hE.1 h
    have h2 : @ite ℝ (IsoK μ ω) (Classical.dec _) 1 0 = @ite ℝ (Rep1 μ ω) (Classical.dec _) 1 0 := by
      by_cases hI : IsoK μ ω
      · rw [ite_eq_left hI, ite_eq_left ⟨h, hI⟩]
      · rw [ite_eq_right hI, ite_eq_right (fun h' => hI h'.2)]
    rw [h2] at h1
    have h3 : (1 / p + Real.exp (-2 * cSE * m)) * @ite ℝ (Rep1 μ ω) (Classical.dec _) 1 0 ≤
        (1 / p + ϖ) * @ite ℝ (Rep1 μ ω) (Classical.dec _) 1 0 :=
      mul_le_mul_of_nonneg_right (by linarith) hI0
    have h4 : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 + ϖ := by positivity
    linarith
  · rw [ite_eq_left h]
    have h1 := prob_le_one (fun ξ : Fin m → Bool => Rep1 μ (succPairs ω ξ))
    have h2 : (0 : ℝ) ≤ (1 / p + ϖ) * @ite ℝ (Rep1 μ ω) (Classical.dec _) 1 0 := mul_nonneg hθ0 hI0
    have h4 : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 + ϖ := by positivity
    linarith

theorem iso_rec {m m0 : ℕ} (hm0 : m0 ≤ m) (hp23 : 23 ≤ p)
    (hpm : (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8))) (μ : ZMod p) {ϖ : ℝ}
    (hϖ1 : Real.exp (-(cPT * m) / 2) ≤ ϖ) (hϖ2 : Real.exp (-2 * cSE * m) ≤ ϖ) :
    prob (fun ω : Pairs (m + 1) → Bool => Rep1 μ ω ∧ EaccRec EvRK m0 (m + 1) ω) ≤
      (1 / (p : ℝ) ^ 2 + ϖ) + (1 / p + ϖ) * prob (fun ω : Pairs m → Bool => Rep1 μ ω ∧ EaccRec EvRK m0 m ω) +
        prob (fun ω : Pairs m → Bool => 2 ≤ geomMult 1 (-1) μ ω ∧ EaccRec EvRK m0 m ω) := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hϖ0 : 0 ≤ ϖ := (Real.exp_pos _).le.trans hϖ1
  have hθ0 : (0 : ℝ) ≤ 1 / p + ϖ := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 + ϖ := by positivity
  have e1 : prob (fun ω : Pairs (m + 1) → Bool => Rep1 μ ω ∧ EaccRec EvRK m0 (m + 1) ω) =
      expect (fun ω : Pairs m → Bool => expect (fun ξ : Fin m → Bool =>
        @ite ℝ (Rep1 μ (succPairs ω ξ) ∧ EaccRec EvRK m0 (m + 1) (succPairs ω ξ)) (Classical.dec _) 1 0)) := by
    rw [← expect_indicator', expect_succPairs]
  have hpt : ∀ ω : Pairs m → Bool, expect (fun ξ : Fin m → Bool =>
      @ite ℝ (Rep1 μ (succPairs ω ξ) ∧ EaccRec EvRK m0 (m + 1) (succPairs ω ξ)) (Classical.dec _) 1 0) ≤
      (1 / (p : ℝ) ^ 2 + ϖ) + (1 / p + ϖ) * @ite ℝ (Rep1 μ ω ∧ EaccRec EvRK m0 m ω) (Classical.dec _) 1 0 +
        @ite ℝ (2 ≤ geomMult 1 (-1) μ ω ∧ EaccRec EvRK m0 m ω) (Classical.dec _) 1 0 := by
    intro ω
    by_cases hacc : EaccRec EvRK m0 m ω ∧ EvRK m ω
    · have hcongr : ∀ ξ, @ite ℝ (Rep1 μ (succPairs ω ξ) ∧ EaccRec EvRK m0 (m + 1) (succPairs ω ξ))
          (Classical.dec _) 1 0 = @ite ℝ (Rep1 μ (succPairs ω ξ)) (Classical.dec _) 1 0 := by
        intro ξ
        have : EaccRec EvRK m0 (m + 1) (succPairs ω ξ) :=
          (EaccRec_succPairs EvRK m0 ω ξ).2 ⟨hacc.1, fun _ => hacc.2⟩
        by_cases h1 : Rep1 μ (succPairs ω ξ)
        · rw [ite_eq_left ⟨h1, this⟩, ite_eq_left h1]
        · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1]
      simp only [hcongr]
      rw [expect_indicator']
      refine (iso_step hp23 hpm μ ω hacc.2 hϖ1 hϖ2).trans (le_of_eq ?_)
      have e2 : @ite ℝ (Rep1 μ ω ∧ EaccRec EvRK m0 m ω) (Classical.dec _) 1 0 =
          @ite ℝ (Rep1 μ ω) (Classical.dec _) 1 0 := by
        by_cases h1 : Rep1 μ ω
        · rw [ite_eq_left ⟨h1, hacc.1⟩, ite_eq_left h1]
        · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1]
      have e3 : @ite ℝ (2 ≤ geomMult 1 (-1) μ ω ∧ EaccRec EvRK m0 m ω) (Classical.dec _) 1 0 =
          @ite ℝ (2 ≤ geomMult 1 (-1) μ ω) (Classical.dec _) 1 0 := by
        by_cases h1 : 2 ≤ geomMult 1 (-1) μ ω
        · rw [ite_eq_left ⟨h1, hacc.1⟩, ite_eq_left h1]
        · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1]
      rw [e2, e3]
    · have hcongr : ∀ ξ, @ite ℝ (Rep1 μ (succPairs ω ξ) ∧ EaccRec EvRK m0 (m + 1) (succPairs ω ξ))
          (Classical.dec _) 1 0 = 0 := by
        intro ξ
        rw [ite_eq_right]
        rw [EaccRec_succPairs]
        exact fun h => hacc ⟨h.2.1, h.2.2 hm0⟩
      simp only [hcongr, expect_const]
      have h1 : (0 : ℝ) ≤ @ite ℝ (Rep1 μ ω ∧ EaccRec EvRK m0 m ω) (Classical.dec _) 1 0 := by
        split_ifs <;> norm_num
      have h2 : (0 : ℝ) ≤ @ite ℝ (2 ≤ geomMult 1 (-1) μ ω ∧ EaccRec EvRK m0 m ω) (Classical.dec _) 1 0 := by
        split_ifs <;> norm_num
      have := mul_nonneg hθ0 h1
      linarith
  rw [e1]
  refine (expect_mono hpt).trans (le_of_eq ?_)
  rw [expect_add, expect_add, expect_const, expect_const_mul, expect_indicator', expect_indicator']

theorem iter_rec {d : ℕ → ℝ} {A θ : ℝ} (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hd1 : ∀ m, d m ≤ 1)
    {m1 : ℕ} : ∀ k, (∀ j, j < k → d (m1 + j + 1) ≤ A + θ * d (m1 + j)) →
      d (m1 + k) ≤ A / (1 - θ) + θ ^ k
  | 0, _ => by
    have : 0 ≤ A / (1 - θ) := div_nonneg hA (by linarith)
    simp only [add_zero, pow_zero]
    linarith [hd1 m1]
  | k + 1, h => by
    have ih := iter_rec hA hθ0 hθ1 hd1 k (fun j hj => h j (by omega))
    have h1 := h k (by omega)
    have hθ' : 1 - θ ≠ 0 := by linarith
    have e : A + θ * (A / (1 - θ)) = A / (1 - θ) := by
      field_simp
      ring
    calc d (m1 + (k + 1)) = d (m1 + k + 1) := by rw [add_assoc]
      _ ≤ A + θ * d (m1 + k) := h1
      _ ≤ A + θ * (A / (1 - θ) + θ ^ k) := by gcongr
      _ = A / (1 - θ) + θ ^ (k + 1) := by rw [mul_add, ← add_assoc, e, pow_succ]; ring

omit [Fact (Nat.Prime p)] in
theorem iso_numbers {B ϖ : ℝ} (hp23 : (23 : ℝ) ≤ p) (hϖ0 : 0 ≤ ϖ) (hϖ : ϖ ≤ 1 / 100000) (hB : 0 ≤ B) :
    (2.2 / (p : ℝ) ^ 2 + B) / (1 - (1 / p + ϖ)) ≤ 2.3 / (p : ℝ) ^ 2 + ϖ + 1.1 * B := by
  have hp0 : (0 : ℝ) < p := by linarith
  set x : ℝ := 1 / p with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 23 := by rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hp23
  have hx2 : 1 / (p : ℝ) ^ 2 = x ^ 2 := by rw [hx, _root_.one_div_pow]
  have hD : 0.95 ≤ 1 - (x + ϖ) := by linarith
  rw [div_le_iff₀ (by linarith)]
  rw [show 2.2 / (p : ℝ) ^ 2 = 2.2 * (1 / (p : ℝ) ^ 2) by ring,
    show 2.3 / (p : ℝ) ^ 2 = 2.3 * (1 / (p : ℝ) ^ 2) by ring, hx2]
  have hx3 : x ^ 2 ≤ 1 / 529 := by nlinarith
  have h1 : 0 ≤ B * ((1 - (x + ϖ)) - 0.95) := mul_nonneg hB (by linarith)
  have h2 : 0 ≤ x ^ 2 * (0.1 - 2.3 * x) := mul_nonneg (sq_nonneg x) (by linarith)
  have h3 : 0 ≤ ϖ * (1 - x - ϖ - 2.3 * x ^ 2) := mul_nonneg hϖ0 (by linarith)
  nlinarith

theorem isocond_one (hp23 : 23 ≤ p) {n : ℕ} (hn16 : 16 ≤ n) (μ : ZMod p) {ϖ : ℝ} (hϖ0 : 0 ≤ ϖ)
    (hϖ : ϖ ≤ 1 / 100000)
    (hpm : ∀ m, (3 * n + 3) / 4 ≤ m → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)))
    (hϖ1 : ∀ m, (3 * n + 3) / 4 ≤ m → Real.exp (-(cPT * m) / 2) ≤ ϖ)
    (hϖ2 : ∀ m, (3 * n + 3) / 4 ≤ m → Real.exp (-2 * cSE * m) ≤ ϖ) :
    prob (fun ω : Pairs n → Bool => (X - C μ) ^ 2 ∣ (modP p (seidelOf ω)).charpoly) ≤
      3.5 / (p : ℝ) ^ 2 + (4.2 * ϖ + 2.1 * C0 * (0.163 : ℝ) ^ (((n / 8 : ℕ) : ℝ) / 2) +
        (1 / p + ϖ) ^ (n - ((3 * n + 3) / 4 + n / 8 + 1)) +
        prob (fun ω : Pairs n → Bool => ¬ EaccRec EvRK ((3 * n + 3) / 4) n ω)) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hpR : (23 : ℝ) ≤ p := by exact_mod_cast hp23
  have hp0 : (0 : ℝ) < p := by linarith
  set m0 := (3 * n + 3) / 4 with hm0
  set m1 := m0 + n / 8 + 1 with hm1
  have hm1n : m1 ≤ n := by omega
  have hC0 := C0_pos
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  have hq : 23 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; exact hp23
  have hcor := lem_corank (F := ZMod p) (n := n) (one_ne_neg_one_zmod hp2) hq μ (by omega) hϖ0 hϖ EvRK
    (fun m hm0' hmn ω hE h0 => by
      rw [hcard, ← one_div]
      exact (rankp_hyp_i hp23 (hpm m hm0') μ ω hE.2 h0).trans (add_le_add le_rfl (hϖ1 m hm0')))
    (fun m hm0' hmn ω hE _ => by
      rw [hcard]
      exact (rankp_hyp_ii hp23 (hpm m hm0') μ ω hE.1).trans (add_le_add le_rfl (hϖ2 m hm0')))
  rw [hcard, ← hm0] at hcor
  set ρ1 : ℝ := (0.163 : ℝ) ^ (((n / 8 : ℕ) : ℝ) / 2) with hρ1
  have hρ1_0 : 0 ≤ ρ1 := by positivity
  set B : ℝ := 2 * ϖ + C0 * ρ1 with hB
  have hB0 : 0 ≤ B := by positivity
  have hb : ∀ m, m1 ≤ m → m ≤ n → prob (fun ω : Pairs m → Bool =>
      2 ≤ geomMult 1 (-1) μ ω ∧ EaccRec EvRK m0 m ω) ≤ 1.2 / (p : ℝ) ^ 2 + ϖ + C0 * ρ1 := by
    intro m hm hmn
    refine (hcor.1 m (by omega) hmn).trans ?_
    have hexp : ((n / 8 : ℕ) : ℝ) / 2 ≤ ((m : ℝ) - m0 - 1) / 2 := by
      have : ((m0 + n / 8 + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
      push_cast at this
      linarith
    have h2 := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 0.163) (by norm_num) hexp
    rw [← hρ1] at h2
    have := mul_le_mul_of_nonneg_left h2 hC0.le
    linarith
  set d : ℕ → ℝ := fun m => prob (fun ω : Pairs m → Bool => Rep1 μ ω ∧ EaccRec EvRK m0 m ω) with hd
  set θ : ℝ := 1 / p + ϖ with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by
    have : 1 / (p : ℝ) ≤ 1 / 23 := one_div_le_one_div_of_le (by norm_num) hpR
    linarith
  set A : ℝ := 2.2 / (p : ℝ) ^ 2 + B with hA
  have hA0 : 0 ≤ A := by positivity
  have hdrec : ∀ j, j < n - m1 → d (m1 + j + 1) ≤ A + θ * d (m1 + j) := by
    intro j hj
    have h1 := iso_rec (m := m1 + j) (m0 := m0) (by omega) hp23 (hpm _ (by omega)) μ
      (hϖ1 _ (by omega)) (hϖ2 _ (by omega))
    have h2 := hb (m1 + j) (by omega) (by omega)
    calc d (m1 + j + 1) ≤ (1 / (p : ℝ) ^ 2 + ϖ) + θ * d (m1 + j) +
          prob (fun ω : Pairs (m1 + j) → Bool => 2 ≤ geomMult 1 (-1) μ ω ∧ EaccRec EvRK m0 (m1 + j) ω) := h1
      _ ≤ A + θ * d (m1 + j) := by
          rw [hA, hB]
          have e : 2.2 / (p : ℝ) ^ 2 = 1 / (p : ℝ) ^ 2 + 1.2 / (p : ℝ) ^ 2 := by ring
          rw [e]
          linarith
  have hdn := iter_rec (d := d) hA0 hθ0 hθ1 (fun m => prob_le_one _) (m1 := m1) (n - m1) hdrec
  rw [show m1 + (n - m1) = n by omega] at hdn
  have hnum := iso_numbers (B := B) hpR hϖ0 hϖ hB0
  have hbn := hcor.1 n (by omega) le_rfl
  have hρn : (0.163 : ℝ) ^ (((n : ℝ) - m0 - 1) / 2) ≤ ρ1 := by
    refine Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ?_
    have : ((m0 + n / 8 + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hm1n
    push_cast at this
    linarith
  calc prob (fun ω : Pairs n → Bool => (X - C μ) ^ 2 ∣ (modP p (seidelOf ω)).charpoly)
      ≤ prob (fun ω : Pairs n → Bool => (2 ≤ geomMult 1 (-1) μ ω ∧ EaccRec EvRK m0 n ω) ∨
          ((Rep1 μ ω ∧ EaccRec EvRK m0 n ω) ∨ ¬ EaccRec EvRK m0 n ω)) := by
        refine prob_mono fun ω h => ?_
        rw [repeated_iff] at h
        tauto
    _ ≤ prob (fun ω : Pairs n → Bool => 2 ≤ geomMult 1 (-1) μ ω ∧ EaccRec EvRK m0 n ω) +
          (d n + prob (fun ω : Pairs n → Bool => ¬ EaccRec EvRK m0 n ω)) :=
        (prob_or_le _ _).trans (add_le_add le_rfl (prob_or_le _ _))
    _ ≤ (1.2 / (p : ℝ) ^ 2 + ϖ + C0 * ρ1) + ((A / (1 - θ) + θ ^ (n - m1)) +
          prob (fun ω : Pairs n → Bool => ¬ EaccRec EvRK m0 n ω)) := by
        gcongr
        exact hbn.trans (by have := mul_le_mul_of_nonneg_left hρn hC0.le; linarith)
    _ ≤ 3.5 / (p : ℝ) ^ 2 + (4.2 * ϖ + 2.1 * C0 * ρ1 + θ ^ (n - m1) +
          prob (fun ω : Pairs n → Bool => ¬ EaccRec EvRK m0 n ω)) := by
        rw [hA, hθ]
        rw [hB] at hnum
        have e : 3.5 / (p : ℝ) ^ 2 = 1.2 / (p : ℝ) ^ 2 + 2.3 / (p : ℝ) ^ 2 := by ring
        rw [e]
        nlinarith

theorem eventually_rpow_ninth_le_mul {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ((1 : ℝ) / 9) ≤ c * n := by
  filter_upwards [eventually_ge_atTop (⌈1 / c ^ 2⌉₊ + 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have h1 : (n : ℝ) ^ ((1 : ℝ) / 9) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h1
  have h2 : 1 / c ^ 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈1 / c ^ 2⌉₊ ≤ n))
  have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by positivity)
  have h3 : 1 ≤ c * √(n : ℝ) := by
    have : 1 / c ≤ √(n : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity), div_pow, one_pow]
      exact h2
    rwa [div_le_iff₀ hc, mul_comm] at this
  calc (n : ℝ) ^ ((1 : ℝ) / 9) ≤ √(n : ℝ) := h1
    _ = √(n : ℝ) * 1 := (mul_one _).symm
    _ ≤ √(n : ℝ) * (c * √(n : ℝ)) := by gcongr
    _ = c * n := by
        rw [show √(n : ℝ) * (c * √(n : ℝ)) = c * (√(n : ℝ) * √(n : ℝ)) by ring, hsq]

theorem prob_not_EaccRec_EvRK_le {N n m0 : ℕ}
    (hN : ∀ b, N ≤ b → prob (fun ω : Pairs b → Bool => ¬ EvRK b ω) ≤ 3 * Real.exp (-(b : ℝ) / 200))
    (hA : N ≤ m0) :
    prob (fun ω : Pairs n → Bool => ¬ EaccRec EvRK m0 n ω) ≤ n * (3 * Real.exp (-(m0 : ℝ) / 200)) := by
  refine (prob_not_EaccRec_le EvRK m0 n).trans ?_
  calc ∑ j ∈ Ico m0 n, prob (fun ω : Pairs j → Bool => ¬ EvRK j ω)
      ≤ ∑ _j ∈ Ico m0 n, 3 * Real.exp (-(m0 : ℝ) / 200) := by
        refine sum_le_sum fun j hj => ?_
        have hj0 : m0 ≤ j := (mem_Ico.1 hj).1
        refine (hN j (hA.trans hj0)).trans ?_
        gcongr
    _ = ((n - m0 : ℕ) : ℝ) * (3 * Real.exp (-(m0 : ℝ) / 200)) := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ n * (3 * Real.exp (-(m0 : ℝ) / 200)) := by
        gcongr
        exact_mod_cast Nat.sub_le n m0

theorem isocond_err_eventually :
    ∀ᶠ n : ℕ in atTop, 4.2 * Real.exp (-(cPT * ((3 * n + 3) / 4 : ℕ)) / 2) +
      2.1 * C0 * (0.163 : ℝ) ^ (((n / 8 : ℕ) : ℝ) / 2) +
      (0.05 : ℝ) ^ (n - ((3 * n + 3) / 4 + n / 8 + 1)) +
      n * (3 * Real.exp (-(((3 * n + 3) / 4 : ℕ) : ℝ) / 200)) ≤ Real.exp (-(2 * cRK) * n) := by
  have hc := cRK_pos
  have hc' := cRK_le
  have hC0 := C0_pos
  filter_upwards [eventually_const_le_exp (a := cRK) (C := 16.8) (by positivity),
    eventually_const_le_exp (a := 0.09375 - 2 * cRK) (C := 8.4 * C0 * Real.exp 0.75) (by linarith),
    eventually_const_le_exp (a := 0.1875 - 2 * cRK) (C := 4 * Real.exp 3) (by linarith),
    eventually_mul_le_exp (b := 3 / 800 - 2 * cRK) (K := 12) (by linarith) (by norm_num),
    eventually_ge_atTop 16] with n h1 h2 h3 h4 h5
  obtain ⟨hm0a, hm0b⟩ := m0_bounds n
  set m0 : ℝ := (((3 * n + 3) / 4 : ℕ) : ℝ) with hm0
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast h5
  have hcPT : cPT = 8 * cRK := by unfold cRK; ring
  have hb : Real.exp (-1.5) ≥ 0.2 := by
    have := exp_three_halves_le
    rw [show (-1.5 : ℝ) = -(3 / 2) by norm_num, Real.exp_neg, ge_iff_le,
      le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    linarith
  have t1 : 4.2 * Real.exp (-(cPT * m0) / 2) ≤ Real.exp (-(2 * cRK) * n) / 4 := by
    have e1 : Real.exp (-(cPT * m0) / 2) ≤ Real.exp (-(3 * cRK) * n) := by
      apply Real.exp_le_exp.2
      rw [hcPT]
      nlinarith
    have e2 : Real.exp (-(3 * cRK) * n) * Real.exp (cRK * n) = Real.exp (-(2 * cRK) * n) := by
      rw [← Real.exp_add]
      ring_nf
    have e3 : 0 < Real.exp (-(3 * cRK) * n) := Real.exp_pos _
    nlinarith
  have t2 : 2.1 * C0 * (0.163 : ℝ) ^ (((n / 8 : ℕ) : ℝ) / 2) ≤ Real.exp (-(2 * cRK) * n) / 4 := by
    have hk : (n : ℝ) / 8 - 1 ≤ ((n / 8 : ℕ) : ℝ) := by
      have h1 : n < 8 * (n / 8) + 8 := by omega
      have h2 : (n : ℝ) < 8 * ((n / 8 : ℕ) : ℝ) + 8 := by exact_mod_cast h1
      linarith
    have hx0 : 0 ≤ ((n / 8 : ℕ) : ℝ) / 2 := by positivity
    have e1 : (0.163 : ℝ) ^ (((n / 8 : ℕ) : ℝ) / 2) ≤ Real.exp (-1.5 * (((n / 8 : ℕ) : ℝ) / 2)) := by
      rw [Real.exp_mul]
      exact Real.rpow_le_rpow (by norm_num) (by linarith) hx0
    have e2 : Real.exp (-1.5 * (((n / 8 : ℕ) : ℝ) / 2)) ≤ Real.exp 0.75 * Real.exp (-0.09375 * n) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith
    have e3 : Real.exp (-0.09375 * n) * Real.exp ((0.09375 - 2 * cRK) * n) = Real.exp (-(2 * cRK) * n) := by
      rw [← Real.exp_add]
      ring_nf
    have e4 : 0 < Real.exp (-0.09375 * n) := Real.exp_pos _
    calc 2.1 * C0 * (0.163 : ℝ) ^ (((n / 8 : ℕ) : ℝ) / 2)
        ≤ 2.1 * C0 * (Real.exp 0.75 * Real.exp (-0.09375 * n)) :=
          mul_le_mul_of_nonneg_left (e1.trans e2) (by positivity)
      _ ≤ Real.exp (-(2 * cRK) * n) / 4 := by nlinarith
  have t3 : (0.05 : ℝ) ^ (n - ((3 * n + 3) / 4 + n / 8 + 1)) ≤ Real.exp (-(2 * cRK) * n) / 4 := by
    have hk : (n : ℝ) / 8 - 2 ≤ ((n - ((3 * n + 3) / 4 + n / 8 + 1) : ℕ) : ℝ) := by
      have h1 : n / 8 * 8 ≤ n := Nat.div_mul_le_self n 8
      have h2 : (3 * n + 3) / 4 + n / 8 + 1 ≤ n := by omega
      rw [Nat.cast_sub h2]
      push_cast
      have h3 : ((n / 8 : ℕ) : ℝ) * 8 ≤ n := by exact_mod_cast h1
      linarith
    have e1 : (0.05 : ℝ) ^ (n - ((3 * n + 3) / 4 + n / 8 + 1)) ≤
        Real.exp (-1.5 * ((n - ((3 * n + 3) / 4 + n / 8 + 1) : ℕ) : ℝ)) := by
      rw [show -1.5 * ((n - ((3 * n + 3) / 4 + n / 8 + 1) : ℕ) : ℝ) =
        ((n - ((3 * n + 3) / 4 + n / 8 + 1) : ℕ) : ℝ) * (-1.5) by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) (by linarith) _
    have e2 : Real.exp (-1.5 * ((n - ((3 * n + 3) / 4 + n / 8 + 1) : ℕ) : ℝ)) ≤
        Real.exp 3 * Real.exp (-0.1875 * n) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith
    have e3 : Real.exp (-0.1875 * n) * Real.exp ((0.1875 - 2 * cRK) * n) = Real.exp (-(2 * cRK) * n) := by
      rw [← Real.exp_add]
      ring_nf
    have e4 : 0 < Real.exp (-0.1875 * n) := Real.exp_pos _
    calc (0.05 : ℝ) ^ (n - ((3 * n + 3) / 4 + n / 8 + 1)) ≤ Real.exp 3 * Real.exp (-0.1875 * n) := e1.trans e2
      _ ≤ Real.exp (-(2 * cRK) * n) / 4 := by nlinarith
  have t4 : n * (3 * Real.exp (-m0 / 200)) ≤ Real.exp (-(2 * cRK) * n) / 4 := by
    have e1 : Real.exp (-m0 / 200) ≤ Real.exp (-(3 / 800) * n) := by
      apply Real.exp_le_exp.2
      linarith
    have e3 : Real.exp (-(3 / 800) * n) * Real.exp ((3 / 800 - 2 * cRK) * n) = Real.exp (-(2 * cRK) * n) := by
      rw [← Real.exp_add]
      ring_nf
    have e4 : 0 < Real.exp (-(3 / 800) * n) := Real.exp_pos _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc (n : ℝ) * (3 * Real.exp (-m0 / 200)) ≤ n * (3 * Real.exp (-(3 / 800) * n)) := by gcongr
      _ ≤ Real.exp (-(2 * cRK) * n) / 4 := by nlinarith
  linarith

theorem prop_isocond_of
    (hPT : ∀ᶠ m : ℕ in atTop, probSeidel m (fun T => ¬ GoodPT T) ≤ Real.exp (-(m : ℝ) / 200)) :
    ∀ᶠ n : ℕ in atTop, ∀ (p : ℕ) [Fact p.Prime], 23 ≤ p →
      (p : ℝ) ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 9)) →
        ∑ μ : ZMod p, prob (fun ω : Pairs n → Bool => (X - C μ) ^ 2 ∣ (modP p (seidelOf ω)).charpoly) ≤
          3.5 / p + Real.exp (-cRK * n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (prob_not_EvRK_le hPT)
  have hA : ∀ᶠ n : ℕ in atTop, N ≤ (3 * n + 3) / 4 := by
    filter_upwards [eventually_ge_atTop (2 * N)] with n hn
    omega
  have hC : ∀ᶠ n : ℕ in atTop, Real.exp (-(cPT * ((3 * n + 3) / 4 : ℕ)) / 2) ≤ 1 / 100000 := by
    filter_upwards [eventually_const_le_exp (a := 3 * cPT / 8) (C := 100000) (by have := cPT_pos; positivity)]
      with n hn
    have hm := (m0_bounds n).1
    have hexp : Real.exp (3 * cPT / 8 * n) ≤ Real.exp (cPT * ((3 * n + 3) / 4 : ℕ) / 2) := by
      apply Real.exp_le_exp.2
      have := cPT_pos
      nlinarith
    rw [show -(cPT * ((3 * n + 3) / 4 : ℕ)) / 2 = -(cPT * ((3 * n + 3) / 4 : ℕ) / 2) by ring, Real.exp_neg,
      inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  filter_upwards [hA, hC, eventually_rpow_ninth_le, isocond_err_eventually,
    eventually_rpow_ninth_le_mul cRK_pos, eventually_ge_atTop 16] with n hA hC hB hD hE hn16
  intro p _ hp23 hpn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpR : (23 : ℝ) ≤ p := by exact_mod_cast hp23
  set m0 := (3 * n + 3) / 4 with hm0
  set ϖ := Real.exp (-(cPT * m0) / 2) with hϖ
  have hϖ0 : 0 ≤ ϖ := (Real.exp_pos _).le
  have hpm : ∀ m, m0 ≤ m → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 8)) := by
    intro m hm
    refine hpn.trans (Real.exp_le_exp.2 (hB.trans ?_))
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hm) (by norm_num)
  have hϖ1 : ∀ m, m0 ≤ m → Real.exp (-(cPT * m) / 2) ≤ ϖ := by
    intro m hm
    apply Real.exp_le_exp.2
    have : (m0 : ℝ) ≤ m := by exact_mod_cast hm
    have := cPT_pos
    nlinarith
  have hϖ2 : ∀ m, m0 ≤ m → Real.exp (-2 * cSE * m) ≤ ϖ := by
    intro m hm
    apply Real.exp_le_exp.2
    have : (m0 : ℝ) ≤ m := by exact_mod_cast hm
    have h1 := cPT_le
    have h2 := cPT_pos
    have h3 : (0 : ℝ) ≤ m0 := Nat.cast_nonneg _
    unfold cSE
    nlinarith
  have hsum := prob_not_EaccRec_EvRK_le (n := n) hN hA
  set err : ℝ := 4.2 * ϖ + 2.1 * C0 * (0.163 : ℝ) ^ (((n / 8 : ℕ) : ℝ) / 2) +
    (0.05 : ℝ) ^ (n - (m0 + n / 8 + 1)) + n * (3 * Real.exp (-(m0 : ℝ) / 200)) with herr
  have hone : ∀ μ : ZMod p, prob (fun ω : Pairs n → Bool => (X - C μ) ^ 2 ∣ (modP p (seidelOf ω)).charpoly) ≤
      3.5 / (p : ℝ) ^ 2 + err := by
    intro μ
    refine (isocond_one hp23 hn16 μ hϖ0 hC hpm hϖ1 hϖ2).trans ?_
    have hθ : (1 / p + ϖ : ℝ) ^ (n - (m0 + n / 8 + 1)) ≤ (0.05 : ℝ) ^ (n - (m0 + n / 8 + 1)) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have : 1 / (p : ℝ) ≤ 1 / 23 := one_div_le_one_div_of_le (by norm_num) hpR
      linarith
    rw [herr]
    linarith
  have herr0 : 0 ≤ err := by
    rw [herr]
    have := C0_pos
    positivity
  calc ∑ μ : ZMod p, prob (fun ω : Pairs n → Bool => (X - C μ) ^ 2 ∣ (modP p (seidelOf ω)).charpoly)
      ≤ ∑ _μ : ZMod p, (3.5 / (p : ℝ) ^ 2 + err) := sum_le_sum fun μ _ => hone μ
    _ = 3.5 / p + p * err := by
        rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
        field_simp
    _ ≤ 3.5 / p + Real.exp ((n : ℝ) ^ ((1 : ℝ) / 9)) * Real.exp (-(2 * cRK) * n) := by
        gcongr
    _ ≤ 3.5 / p + Real.exp (-cRK * n) := by
        rw [← Real.exp_add]
        gcongr
        linarith

end DGS
