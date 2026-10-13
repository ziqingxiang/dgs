module

public import DGS.S06_Fourier.FourierBound

@[expose] public section

open Matrix
open scoped Real

namespace DGS

section Signs

variable {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι] [DecidableEq ι]

def sgnZ (x : Bool) : ℤ := if x then 1 else -1

@[simp] theorem sgnZ_true : sgnZ true = 1 := rfl
@[simp] theorem sgnZ_false : sgnZ false = -1 := rfl

def sgnSum (w : ι → G) (ξ : ι → Bool) : G := ∑ j, sgnZ (ξ j) • w j

noncomputable def rhoG (w : ι → G) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun ξ' : ι → Bool =>
    prob fun ξ : ι → Bool => sgnSum w ξ = sgnSum w ξ'

theorem rhoG_nonneg (w : ι → G) : 0 ≤ rhoG w :=
  Finset.le_sup'_of_le _ (Finset.mem_univ fun _ => true) (prob_nonneg _)

theorem prob_sgnSum_le_rhoG (w : ι → G) (a : G) :
    prob (fun ξ : ι → Bool => sgnSum w ξ = a) ≤ rhoG w := by
  by_cases h : ∃ ξ', sgnSum w ξ' = a
  · obtain ⟨ξ', rfl⟩ := h
    exact Finset.le_sup' (fun ξ' : ι → Bool => prob fun ξ : ι → Bool => sgnSum w ξ = sgnSum w ξ')
      (Finset.mem_univ ξ')
  · push Not at h
    have h0 : prob (fun ξ : ι → Bool => sgnSum w ξ = a) = 0 := by
      rw [prob_congr (Q := fun _ => False) (fun ξ => ⟨fun h' => h ξ h', False.elim⟩), prob_false]
    rw [h0]
    exact rhoG_nonneg w

theorem rhoG_le_of_forall {w : ι → G} {c : ℝ}
    (h : ∀ a, prob (fun ξ : ι → Bool => sgnSum w ξ = a) ≤ c) : rhoG w ≤ c :=
  Finset.sup'_le _ _ fun _ξ' _ => h _

theorem rhoG_le_one (w : ι → G) : rhoG w ≤ 1 :=
  rhoG_le_of_forall fun _ => prob_le_one _

omit [DecidableEq ι] in
theorem sgnSum_split (P : ι → Prop) [DecidablePred P] (w : ι → G) (ξ : ι → Bool) :
    sgnSum w ξ = sgnSum (fun j : {j // P j} => w j) (fun j => ξ j) +
      sgnSum (fun j : {j // ¬ P j} => w j) (fun j => ξ j) := by
  unfold sgnSum
  exact (Fintype.sum_subtype_add_sum_subtype P (fun j => sgnZ (ξ j) • w j)).symm

theorem rhoG_le_restrict (P : ι → Prop) [DecidablePred P] (w : ι → G) :
    rhoG w ≤ rhoG (fun j : {j // P j} => w j) := by
  refine rhoG_le_of_forall fun a => ?_
  let e := Equiv.piEquivPiSubtypeProd P (fun _ : ι => Bool)
  have h1 : prob (fun ξ : ι → Bool => sgnSum w ξ = a) =
      prob (fun x : ({j // P j} → Bool) × ({j // ¬ P j} → Bool) =>
        sgnSum (fun j : {j // P j} => w j) x.1 =
          a - sgnSum (fun j : {j // ¬ P j} => w j) x.2) := by
    rw [← prob_equiv e]
    refine prob_congr fun ξ => ?_
    rw [sgnSum_split P w ξ, eq_sub_iff_add_eq]
    rfl
  rw [h1]
  refine prob_le_of_forall_snd (P := fun x : ({j // P j} → Bool) × ({j // ¬ P j} → Bool) =>
      sgnSum (fun j : {j // P j} => w j) x.1 = a - sgnSum (fun j : {j // ¬ P j} => w j) x.2)
    (fun ξ₂ => ?_) (rhoG_nonneg _)
  exact prob_sgnSum_le_rhoG (fun j : {j // P j} => w j) (a - sgnSum (fun j : {j // ¬ P j} => w j) ξ₂)

theorem rhoG_map {H : Type*} [AddCommGroup H] (f : G →+ H) (hf : Function.Injective f)
    (w : ι → G) : rhoG (fun j => f (w j)) = rhoG w := by
  have hs : ∀ ξ, sgnSum (fun j => f (w j)) ξ = f (sgnSum w ξ) := by
    intro ξ
    simp only [sgnSum, map_sum, map_zsmul]
  apply le_antisymm
  · refine rhoG_le_of_forall fun a => ?_
    by_cases ha : ∃ g, f g = a
    · obtain ⟨g, rfl⟩ := ha
      calc prob (fun ξ : ι → Bool => sgnSum (fun j => f (w j)) ξ = f g)
          = prob (fun ξ : ι → Bool => sgnSum w ξ = g) :=
            prob_congr fun ξ => by rw [hs, hf.eq_iff]
        _ ≤ rhoG w := prob_sgnSum_le_rhoG w g
    · push Not at ha
      have h0 : prob (fun ξ : ι → Bool => sgnSum (fun j => f (w j)) ξ = a) = 0 := by
        rw [prob_congr (Q := fun _ => False) (fun ξ => ⟨fun h' => ha _ ((hs ξ).symm.trans h'),
          False.elim⟩), prob_false]
      rw [h0]
      exact rhoG_nonneg w
  · refine rhoG_le_of_forall fun a => ?_
    calc prob (fun ξ : ι → Bool => sgnSum w ξ = a)
        = prob (fun ξ : ι → Bool => sgnSum (fun j => f (w j)) ξ = f a) :=
          prob_congr fun ξ => by rw [hs, hf.eq_iff]
      _ ≤ rhoG (fun j => f (w j)) := prob_sgnSum_le_rhoG _ _

theorem rhoG_comp_equiv {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι) (w : ι → G) :
    rhoG (fun j => w (e j)) = rhoG w := by
  have hs : ∀ ξ : ι → Bool, sgnSum (fun j => w (e j)) (fun j => ξ (e j)) = sgnSum w ξ := by
    intro ξ
    exact Equiv.sum_comp e (fun j => sgnZ (ξ j) • w j)
  let E : (ι → Bool) ≃ (ι' → Bool) := e.arrowCongr (Equiv.refl Bool) |>.symm
  have hE : ∀ ξ : ι → Bool, E ξ = fun j => ξ (e j) := fun ξ => rfl
  apply le_antisymm
  · refine rhoG_le_of_forall fun a => ?_
    calc prob (fun ξ' : ι' → Bool => sgnSum (fun j => w (e j)) ξ' = a)
        = prob (fun ξ : ι → Bool => sgnSum (fun j => w (e j)) (E ξ) = a) :=
          (prob_equiv E (fun ξ' => sgnSum (fun j => w (e j)) ξ' = a)).symm
      _ = prob (fun ξ : ι → Bool => sgnSum w ξ = a) := prob_congr fun ξ => by rw [hE, hs]
      _ ≤ rhoG w := prob_sgnSum_le_rhoG w a
  · refine rhoG_le_of_forall fun a => ?_
    calc prob (fun ξ : ι → Bool => sgnSum w ξ = a)
        = prob (fun ξ : ι → Bool => sgnSum (fun j => w (e j)) (E ξ) = a) :=
          prob_congr fun ξ => by rw [hE, hs]
      _ = prob (fun ξ' : ι' → Bool => sgnSum (fun j => w (e j)) ξ' = a) :=
          prob_equiv E (fun ξ' => sgnSum (fun j => w (e j)) ξ' = a)
      _ ≤ rhoG (fun j => w (e j)) := prob_sgnSum_le_rhoG _ a

theorem sum_prod_bool {R : Type*} [CommSemiring R] (f : ι → Bool → R) :
    ∑ ξ : ι → Bool, ∏ j, f j (ξ j) = ∏ j, (f j true + f j false) := by
  rw [← Fintype.prod_sum f]
  simp only [Fintype.sum_bool]

end Signs

section Fourier

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def cosP (x : ZMod p) : ℝ := Real.cos (2 * π * (x.val : ℝ) / p)

omit [Fact (Nat.Prime p)] in
theorem abs_cosP_le_one (x : ZMod p) : |cosP x| ≤ 1 := Real.abs_cos_le_one _

theorem stdAddChar_add_neg (x : ZMod p) :
    ZMod.stdAddChar x + ZMod.stdAddChar (-x) = 2 * (cosP x : ℂ) := by
  have h1 : ZMod.stdAddChar x = Complex.exp (2 * π * Complex.I * (x.val : ℤ) / p) := by
    rw [← ZMod.stdAddChar_coe]
    simp
  have h2 : ZMod.stdAddChar (-x) = Complex.exp (2 * π * Complex.I * (-(x.val : ℤ) : ℤ) / p) := by
    rw [← ZMod.stdAddChar_coe]
    simp
  rw [h1, h2, cosP, Complex.ofReal_cos, Complex.cos]
  push_cast
  have e1 : 2 * ↑π * Complex.I * ↑(x.val : ℕ) / (p : ℂ) =
      (2 * ↑π * ↑(x.val : ℕ) / ↑p) * Complex.I := by ring
  have e2 : 2 * ↑π * Complex.I * -↑(x.val : ℕ) / (p : ℂ) =
      -(2 * ↑π * ↑(x.val : ℕ) / ↑p) * Complex.I := by ring
  rw [e1, e2]
  ring

local notation "ψp" => (ZMod.stdAddChar : AddChar (ZMod p) ℂ)

theorem norm_stdAddChar (x : ZMod p) : ‖(ZMod.stdAddChar x : ℂ)‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

noncomputable def rhoHat {d : ℕ} (w : ι → Fin d → ZMod p) : ℝ :=
  ((p : ℝ) ^ d)⁻¹ * ∑ τ : Fin d → ZMod p, ∏ j, |cosP (τ ⬝ᵥ w j)|

noncomputable def rhoHatP (w : ι → ZMod p) : ℝ :=
  (p : ℝ)⁻¹ * ∑ c : ZMod p, ∏ j, |cosP (c * w j)|

omit [DecidableEq ι] in
theorem rhoHat_nonneg {d : ℕ} (w : ι → Fin d → ZMod p) : 0 ≤ rhoHat w := by
  unfold rhoHat
  have : (0 : ℝ) ≤ ((p : ℝ) ^ d)⁻¹ := by positivity
  exact mul_nonneg this (Finset.sum_nonneg fun τ _ => Finset.prod_nonneg fun j _ => abs_nonneg _)

omit [DecidableEq ι] in
theorem rhoHatP_nonneg (w : ι → ZMod p) : 0 ≤ rhoHatP w := by
  unfold rhoHatP
  have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  exact mul_nonneg this (Finset.sum_nonneg fun τ _ => Finset.prod_nonneg fun j _ => abs_nonneg _)

theorem dotProduct_zsmul {d : ℕ} (τ v : Fin d → ZMod p) (z : ℤ) :
    τ ⬝ᵥ (z • v) = (z : ZMod p) * (τ ⬝ᵥ v) := by
  rw [dotProduct_smul, zsmul_eq_mul]

theorem prob_sgnSum_eq_fourier {d : ℕ} (w : ι → Fin d → ZMod p) (a : Fin d → ZMod p) :
    ((prob fun ξ : ι → Bool => sgnSum w ξ = a : ℝ) : ℂ) =
      ((p : ℂ) ^ d)⁻¹ * ∑ τ : Fin d → ZMod p,
        ZMod.stdAddChar (-(τ ⬝ᵥ a)) * ∏ j, (cosP (τ ⬝ᵥ w j) : ℂ) := by
  classical
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hind : ∀ ξ : ι → Bool, (if sgnSum w ξ = a then (1 : ℂ) else 0) =
      ((p : ℂ) ^ d)⁻¹ * ∑ τ : Fin d → ZMod p, ψp (τ ⬝ᵥ (sgnSum w ξ - a)) := by
    intro ξ
    have h := sum_stdAddChar_dot (q := p) (sgnSum w ξ - a)
    simp only [Fintype.card_fin] at h
    have h' : ∑ τ : Fin d → ZMod p, ψp (τ ⬝ᵥ (sgnSum w ξ - a)) =
        if sgnSum w ξ - a = 0 then (p : ℂ) ^ d else 0 := by
      rw [← h]
      rfl
    rw [h']
    by_cases hS : sgnSum w ξ = a
    · rw [ite_eq_left hS, ite_eq_left (sub_eq_zero.2 hS)]
      field_simp
    · rw [ite_eq_right hS, ite_eq_right (fun h => hS (sub_eq_zero.1 h))]
      simp
  have hfac : ∀ (τ : Fin d → ZMod p) (ξ : ι → Bool), ψp (τ ⬝ᵥ (sgnSum w ξ - a)) =
      ψp (-(τ ⬝ᵥ a)) * ∏ j, ψp ((sgnZ (ξ j) : ZMod p) * (τ ⬝ᵥ w j)) := by
    intro τ ξ
    rw [dotProduct_sub, sub_eq_neg_add, AddChar.map_add_eq_mul]
    congr 1
    rw [sgnSum, dotProduct_sum, addChar_map_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [dotProduct_zsmul]
  have hsum : ∀ τ : Fin d → ZMod p,
      ∑ ξ : ι → Bool, ∏ j, ψp ((sgnZ (ξ j) : ZMod p) * (τ ⬝ᵥ w j)) =
        2 ^ Fintype.card ι * ∏ j, (cosP (τ ⬝ᵥ w j) : ℂ) := by
    intro τ
    rw [sum_prod_bool (fun j b => ψp ((sgnZ b : ZMod p) * (τ ⬝ᵥ w j)))]
    simp only [sgnZ_true, sgnZ_false, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul]
    simp_rw [stdAddChar_add_neg]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hcard : (Nat.card {ξ : ι → Bool // sgnSum w ξ = a} : ℂ) =
      ∑ ξ : ι → Bool, if sgnSum w ξ = a then (1 : ℂ) else 0 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]
  have hΩ : (Nat.card (ι → Bool) : ℂ) = 2 ^ Fintype.card ι := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool]
    push_cast
    ring
  unfold prob
  push_cast
  rw [hcard, hΩ]
  simp_rw [hind, hfac]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hsum]
  have h2 : (2 : ℂ) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  field_simp

theorem rhoG_le_rhoHat {d : ℕ} (w : ι → Fin d → ZMod p) : rhoG w ≤ rhoHat w := by
  refine rhoG_le_of_forall fun a => ?_
  have h := prob_sgnSum_eq_fourier w a
  have hn : prob (fun ξ : ι → Bool => sgnSum w ξ = a) =
      ‖((prob fun ξ : ι → Bool => sgnSum w ξ = a : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (prob_nonneg _)]
  rw [hn, h, norm_mul, norm_inv, norm_pow, Complex.norm_natCast, rhoHat]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
  rw [norm_mul, norm_stdAddChar, one_mul, norm_prod]
  refine le_of_eq (Finset.prod_congr rfl fun j _ => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]

omit [DecidableEq ι] in
theorem rhoHat_le_restrict {d : ℕ} (P : ι → Prop) [DecidablePred P] (w : ι → Fin d → ZMod p) :
    rhoHat w ≤ rhoHat (fun j : {j // P j} => w j) := by
  unfold rhoHat
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) (by positivity)
  rw [← Fintype.prod_subtype_mul_prod_subtype P (fun j => |cosP (τ ⬝ᵥ w j)|)]
  refine mul_le_of_le_one_right (Finset.prod_nonneg fun j _ => abs_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ => abs_cosP_le_one _

omit [DecidableEq ι] in
theorem rhoHatP_le_restrict (P : ι → Prop) [DecidablePred P] (w : ι → ZMod p) :
    rhoHatP w ≤ rhoHatP (fun j : {j // P j} => w j) := by
  unfold rhoHatP
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) (by positivity)
  rw [← Fintype.prod_subtype_mul_prod_subtype P (fun j => |cosP (c * w j)|)]
  refine mul_le_of_le_one_right (Finset.prod_nonneg fun j _ => abs_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ => abs_cosP_le_one _

def toV1 (x : ZMod p) : Fin 1 → ZMod p := fun _ => x

def toV1Hom : ZMod p →+ (Fin 1 → ZMod p) where
  toFun := toV1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toV1Hom_injective : Function.Injective (toV1Hom (p := p)) :=
  fun _x _y h => congrFun h 0

omit [DecidableEq ι] in
theorem rhoHat_toV1 (w : ι → ZMod p) : rhoHat (fun j => toV1 (w j)) = rhoHatP w := by
  unfold rhoHat rhoHatP
  rw [pow_one]
  congr 1
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod p)) _ _ fun τ => ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [toV1, dotProduct, Equiv.funUnique]

theorem rhoG_le_rhoHatP (w : ι → ZMod p) : rhoG w ≤ rhoHatP w := by
  rw [← rhoG_map toV1Hom toV1Hom_injective w, ← rhoHat_toV1]
  exact rhoG_le_rhoHat _

end Fourier

end DGS
