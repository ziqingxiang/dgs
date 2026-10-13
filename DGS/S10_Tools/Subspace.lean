module

public import DGS.S10_Tools.BlockDelta
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Module.ZMod

@[expose] public section

open Finset Matrix Module
open scoped Real

namespace DGS

theorem sum_comp_surj {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (T : A →+ B) (hT : Function.Surjective T) (F : B → ℝ) :
    ∑ a, F (T a) = Nat.card T.ker * ∑ b, F b := by
  classical
  set sec := Function.surjInv hT with hsec
  have hsec' : ∀ b, T (sec b) = b := Function.surjInv_eq hT
  let e : A ≃ T.ker × B :=
    { toFun := fun a => (⟨a - sec (T a), by
          rw [AddMonoidHom.mem_ker, map_sub, hsec', sub_self]⟩, T a)
      invFun := fun x => x.1 + sec x.2
      left_inv := fun a => by simp
      right_inv := fun x => by
        obtain ⟨⟨k, hk⟩, b⟩ := x
        rw [AddMonoidHom.mem_ker] at hk
        ext
        · simp [hk, hsec']
        · simp [hk, hsec'] }
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  have : ∀ (k : T.ker) (b : B), T (e.symm (k, b)) = b := by
    intro k b
    show T (k.1 + sec b) = b
    rw [map_add, T.mem_ker.1 k.2, hsec', zero_add]
  simp only [this, sum_const, card_univ, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card]

theorem card_eq_card_ker_mul {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (T : A →+ B) (hT : Function.Surjective T) :
    (Fintype.card A : ℝ) = Nat.card T.ker * Fintype.card B := by
  have := sum_comp_surj T hT (fun _ => (1 : ℝ))
  simpa using this

variable {p : ℕ} [Fact p.Prime] {d g : ℕ}

noncomputable def charRestrict (L : Submodule (ZMod p) (Fin d → ZMod p))
    (φ : L ≃ₗ[ZMod p] (Fin g → ZMod p)) : (Fin d → ZMod p) →+ (Fin g → ZMod p) where
  toFun τ := fun i => τ ⬝ᵥ (φ.symm (Pi.single i 1) : Fin d → ZMod p)
  map_zero' := by funext i; simp
  map_add' τ τ' := by funext i; simp [add_dotProduct]

theorem dotProduct_eq_charRestrict (L : Submodule (ZMod p) (Fin d → ZMod p))
    (φ : L ≃ₗ[ZMod p] (Fin g → ZMod p)) (τ : Fin d → ZMod p) (v : L) :
    τ ⬝ᵥ (v : Fin d → ZMod p) = charRestrict L φ τ ⬝ᵥ φ v := by
  have h1 : v = ∑ i, (φ v) i • φ.symm (Pi.single i 1) := by
    conv_lhs => rw [← φ.symm_apply_apply v]
    conv_lhs => rw [← Finset.univ_sum_single (φ v)]
    rw [map_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← map_smul]
    congr 1
    funext k
    simp [Pi.single_apply]
  conv_lhs => rw [h1]
  rw [Submodule.coe_sum, dotProduct_sum]
  simp only [Submodule.coe_smul, dotProduct_smul, smul_eq_mul]
  rw [dotProduct]
  refine sum_congr rfl fun i _ => ?_
  simp only [charRestrict, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ring

theorem charRestrict_surjective (L : Submodule (ZMod p) (Fin d → ZMod p))
    (φ : L ≃ₗ[ZMod p] (Fin g → ZMod p)) : Function.Surjective (charRestrict L φ) := by
  intro σ
  let f : L →ₗ[ZMod p] ZMod p :=
    { toFun := fun u => σ ⬝ᵥ φ u
      map_add' := fun u v => by simp [dotProduct_add]
      map_smul' := fun c u => by simp [dotProduct_smul] }
  obtain ⟨G, hG⟩ := LinearMap.exists_extend f
  refine ⟨fun k => G (Pi.single k 1), ?_⟩
  have hsingle : ∀ (k : Fin d) (c : ZMod p),
      (Pi.single k c : Fin d → ZMod p) = c • Pi.single k 1 := by
    intro k c
    funext k'
    simp [Pi.single_apply]
  have hGv : ∀ v : Fin d → ZMod p, G v = (fun k => G (Pi.single k 1)) ⬝ᵥ v := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum, dotProduct]
    refine sum_congr rfl fun k _ => ?_
    rw [hsingle k (v k), map_smul, smul_eq_mul, mul_comm]
  funext i
  simp only [charRestrict, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [← hGv]
  have := LinearMap.congr_fun hG (φ.symm (Pi.single i 1))
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
  rw [this]
  simp [f, dotProduct_single]

theorem rhoHat_eq_of_subspace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule (ZMod p) (Fin d → ZMod p)) (φ : L ≃ₗ[ZMod p] (Fin g → ZMod p))
    (w : ι → Fin d → ZMod p) (hw : ∀ j, w j ∈ L) :
    rhoHat w = rhoHat (fun j => φ ⟨w j, hw j⟩) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hT := charRestrict_surjective L φ
  have hcard := card_eq_card_ker_mul (charRestrict L φ) hT
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
  push_cast at hcard
  unfold rhoHat
  have h1 : ∑ τ : Fin d → ZMod p, ∏ j, |cosP (τ ⬝ᵥ w j)| =
      ∑ τ : Fin d → ZMod p, (fun σ : Fin g → ZMod p => ∏ j, |cosP (σ ⬝ᵥ φ ⟨w j, hw j⟩)|)
        (charRestrict L φ τ) := by
    refine sum_congr rfl fun τ _ => ?_
    refine prod_congr rfl fun j _ => ?_
    rw [dotProduct_eq_charRestrict L φ τ ⟨w j, hw j⟩]
  have h2 := sum_comp_surj (charRestrict L φ) hT
    (fun σ : Fin g → ZMod p => ∏ j, |cosP (σ ⬝ᵥ φ ⟨w j, hw j⟩)|)
  rw [h1, h2, ← mul_assoc]
  congr 1
  have hpg : (0 : ℝ) < (p : ℝ) ^ g := by positivity
  have hk : (Nat.card (charRestrict L φ).ker : ℝ) ≠ 0 := by
    have := Nat.card_pos (α := (charRestrict L φ).ker)
    positivity
  rw [hcard]
  field_simp

theorem Rl_map {G H : Type*} [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : G →+ H) (hf : Function.Injective f) (l : ℕ)
    (w : ι → G) : Rl l (fun j => f (w j)) = Rl l w := by
  unfold Rl vanSet
  congr 1
  refine filter_congr fun x _ => ?_
  unfold sgnSumIdx
  rw [show ∑ r, sgnZ (x.2 r) • f (w (x.1 r)) = f (∑ r, sgnZ (x.2 r) • w (x.1 r)) by
    simp [map_sum, map_zsmul]]
  exact map_eq_zero_iff f hf

theorem rl_map {G H : Type*} [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : G →+ H) (hf : Function.Injective f) (l : ℕ)
    (w : ι → G) : rl l (fun j => f (w j)) = rl l w := by
  unfold rl
  rw [Rl_map f hf]

noncomputable def outL {ι : Type*} (L : Submodule (ZMod p) (Fin d → ZMod p))
    (w : ι → Fin d → ZMod p) : ℕ := Nat.card {i // w i ∉ L}

noncomputable def subspaceEquiv (L : Submodule (ZMod p) (Fin d → ZMod p)) :
    L ≃ₗ[ZMod p] (Fin (finrank (ZMod p) L) → ZMod p) :=
  LinearEquiv.ofFinrankEq L (Fin (finrank (ZMod p) L) → ZMod p) (by simp)

noncomputable def subspaceEmb (L : Submodule (ZMod p) (Fin d → ZMod p)) :
    (Fin (finrank (ZMod p) L) → ZMod p) →+ (Fin d → ZMod p) :=
  (L.subtype.comp (subspaceEquiv L).symm.toLinearMap).toAddMonoidHom

theorem subspaceEmb_injective (L : Submodule (ZMod p) (Fin d → ZMod p)) :
    Function.Injective (subspaceEmb L) := by
  intro x y h
  have : ((subspaceEquiv L).symm x : Fin d → ZMod p) = ((subspaceEquiv L).symm y : Fin d → ZMod p) := h
  exact (subspaceEquiv L).symm.injective (Subtype.ext this)

theorem subspaceEmb_apply (L : Submodule (ZMod p) (Fin d → ZMod p)) (v : Fin d → ZMod p)
    (hv : v ∈ L) : subspaceEmb L (subspaceEquiv L ⟨v, hv⟩) = v := by
  simp [subspaceEmb]

theorem rl_subspace {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule (ZMod p) (Fin d → ZMod p))
    (w : ι → Fin d → ZMod p) (hw : ∀ j, w j ∈ L) (l : ℕ) :
    rl l w = rl l (fun j => subspaceEquiv L ⟨w j, hw j⟩) := by
  have := rl_map (subspaceEmb L) (subspaceEmb_injective L) l
    (fun j => subspaceEquiv L ⟨w j, hw j⟩)
  simp only [subspaceEmb_apply] at this
  exact this

theorem halasz_subspace (hp2 : p ≠ 2) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule (ZMod p) (Fin d → ZMod p)) (w : ι → Fin d → ZMod p) (hw : ∀ j, w j ∈ L)
    {l : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ Fintype.card ι)
    (hU : ∀ U : Submodule (ZMod p) (Fin d → ZMod p), U ≤ L → U ≠ L →
      (0.18 : ℝ) * Fintype.card ι / l ≤ outL U w) :
    rhoHat w ≤ 1 / (p : ℝ) ^ finrank (ZMod p) L + 8 * √(π * l / Fintype.card ι) * rl l w +
      Real.exp (-(Fintype.card ι : ℝ) / (16 * l)) := by
  set φ := subspaceEquiv L
  set w' := fun j => φ ⟨w j, hw j⟩ with hw'
  rw [rhoHat_eq_of_subspace L φ w hw, rl_subspace L w hw]
  refine prop_halasz hp2 w' hl hm fun K hK => ?_
  set U : Submodule (ZMod p) (Fin d → ZMod p) :=
    ((AddSubgroup.toZModSubmodule p K).comap φ.toLinearMap).map L.subtype with hUdef
  have hmemU : ∀ j, w j ∈ U ↔ w' j ∈ K := by
    intro j
    constructor
    · rintro ⟨u, hu, hu'⟩
      have : u = ⟨w j, hw j⟩ := Subtype.ext hu'
      subst this
      exact hu
    · intro h
      exact ⟨⟨w j, hw j⟩, h, rfl⟩
  have hUL : U ≤ L := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hUne : U ≠ L := by
    intro hUL'
    apply hK
    rw [eq_top_iff]
    intro x _
    have hx : ((φ.symm x : L) : Fin d → ZMod p) ∈ U := by
      rw [hUL']
      exact (φ.symm x).2
    obtain ⟨u, hu, hu'⟩ := hx
    have : u = φ.symm x := Subtype.ext hu'
    rw [this] at hu
    simpa using hu
  have h := hU U hUL hUne
  have hcard : outL U w = Nat.card {j // w' j ∉ K} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun j => not_congr (hmemU j))
  rw [hcard] at h
  exact h

theorem rl_ge_inv_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → Fin g → ZMod p) (l : ℕ)
    (hm : 1 ≤ Fintype.card ι) : 1 / (p : ℝ) ^ g ≤ rl l u := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h := sum_cosSumC_pow (one_ne_zero : (1 : ZMod p) ≠ 0) u l
  have h0 : cosSumC 1 u 0 = Fintype.card ι := by
    simp [cosSumC, cosP]
  have hnn : ∀ σ, 0 ≤ cosSumC 1 u σ ^ (2 * l) := fun σ => by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have h1 : cosSumC 1 u 0 ^ (2 * l) ≤ ∑ σ, cosSumC 1 u σ ^ (2 * l) :=
    single_le_sum (fun σ _ => hnn σ) (mem_univ _)
  rw [h, h0] at h1
  have hm' : (0 : ℝ) < (Fintype.card ι : ℝ) ^ (2 * l) := by
    have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hm
    positivity
  have hpg : (0 : ℝ) < (p : ℝ) ^ g := by positivity
  rw [div_le_iff₀ hpg]
  have : (Fintype.card ι : ℝ) ^ (2 * l) * 1 ≤ (Fintype.card ι : ℝ) ^ (2 * l) * (rl l u * (p : ℝ) ^ g) := by
    rw [mul_one]
    linarith
  exact le_of_mul_le_mul_left this hm'

theorem lem_lineheavy {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule (ZMod p) (Fin d → ZMod p))
    {θ : ℝ} (_hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (l : ℕ) (w : ι → Fin d → ZMod p)
    (hm : 1 ≤ Fintype.card ι) (hout : (outL L w : ℝ) ≤ θ * Fintype.card ι) :
    (1 - θ) ^ (2 * l) / (p : ℝ) ^ finrank (ZMod p) L ≤ rl l w := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set m : ℝ := (Fintype.card ι : ℝ) with hmdef
  have hmR : (1 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm
  set m' := Fintype.card {i // w i ∈ L} with hm'def
  have hsplit : (m' : ℝ) + outL L w = m := by
    have := Fintype.card_subtype_compl (fun i => w i ∈ L)
    have h2 : outL L w = Fintype.card {i // ¬ w i ∈ L} := by
      rw [outL, Nat.card_eq_fintype_card]
    have h3 : m' + Fintype.card {i // ¬ w i ∈ L} = Fintype.card ι := by
      have := Fintype.card_subtype_le (fun i => w i ∈ L)
      rw [Fintype.card_subtype_compl]
      omega
    rw [h2, hmdef]
    exact_mod_cast h3
  have hm'R : (1 - θ) * m ≤ m' := by linarith
  have hm'pos : 0 < (m' : ℝ) := by nlinarith
  have hm'1 : 1 ≤ m' := by
    have : (0 : ℝ) < m' := hm'pos
    exact_mod_cast this
  set u := fun i : {i // w i ∈ L} => w i with hu
  have hru := rl_ge_inv_pow (fun j => subspaceEquiv L ⟨u j, j.2⟩) l (by rw [← hm'def]; exact hm'1)
  rw [← rl_subspace L u (fun j => j.2) l] at hru
  have hR := Rl_restrict_le l (fun i => w i ∈ L) w
  have hpg : (0 : ℝ) < (p : ℝ) ^ finrank (ZMod p) L := by positivity
  have h1 : (2 * (m' : ℝ)) ^ (2 * l) / (p : ℝ) ^ finrank (ZMod p) L ≤ Rl l w := by
    have : (2 * (m' : ℝ)) ^ (2 * l) / (p : ℝ) ^ finrank (ZMod p) L ≤ Rl l u := by
      unfold rl at hru
      rw [← hm'def] at hru
      have hpos : (0 : ℝ) < (2 * (m' : ℝ)) ^ (2 * l) := by positivity
      rw [le_div_iff₀ hpos] at hru
      rw [div_le_iff₀ hpg]
      calc (2 * (m' : ℝ)) ^ (2 * l) = 1 / (p : ℝ) ^ finrank (ZMod p) L * (2 * (m' : ℝ)) ^ (2 * l) *
            (p : ℝ) ^ finrank (ZMod p) L := by field_simp
        _ ≤ Rl l u * (p : ℝ) ^ finrank (ZMod p) L := by gcongr
    exact this.trans (by exact_mod_cast hR)
  unfold rl
  rw [← hmdef]
  have h2m : (0 : ℝ) < (2 * m) ^ (2 * l) := by positivity
  rw [le_div_iff₀ h2m]
  calc (1 - θ) ^ (2 * l) / (p : ℝ) ^ finrank (ZMod p) L * (2 * m) ^ (2 * l)
      = (2 * ((1 - θ) * m)) ^ (2 * l) / (p : ℝ) ^ finrank (ZMod p) L := by
        rw [mul_pow, mul_pow, mul_pow]
        ring
    _ ≤ (2 * (m' : ℝ)) ^ (2 * l) / (p : ℝ) ^ finrank (ZMod p) L := by
        gcongr
    _ ≤ Rl l w := h1

end DGS
