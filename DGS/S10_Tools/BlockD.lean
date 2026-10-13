module

public import DGS.S10_Tools.Subspace
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open Finset Module
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime] {d : ℕ}

structure BDHyp (p d l s : ℕ) : Prop where
  hp2 : p ≠ 2
  hd2 : 2 ≤ d
  hd4 : d ≤ 4
  hl : 50 ≤ l
  hs1 : 16 * l * Real.log (2 * (p : ℝ) ^ d / (1 / 100)) ≤ s
  hs2 : 32 * (1 + 1 / 100) / (1 / 100) * √(π * l) * (p : ℝ) ^ d * (3 * l / 2 : ℝ) ^ (2 * l) ≤
    (s : ℝ) ^ (((l : ℝ) + 1) / 2)
  hs3 : 100 * (p : ℝ) ^ (d - 1) * (3 * l / 2 : ℝ) ^ (2 * l) ≤ (s : ℝ) ^ ((l : ℝ) / 2)
  hs4 : 1400 * l ≤ s
  hs5 : 3 ≤ d → √((s : ℝ) / l) ≤ p

noncomputable def varth (d l g : ℕ) : ℝ := 0.18 * 2.1 ^ (d - 1 - g) / l

noncomputable def varpi (l s : ℕ) : ℝ := 6 * (1 + 1 / 100) * √(π * l) / ((1 / 100) * √(s : ℝ))

def window (p l s g : ℕ) : Set ℝ := Set.Ioo (varpi l s / (p : ℝ) ^ g) (1.1 / (p : ℝ) ^ g)

section Numbers

variable {l s : ℕ}

theorem varth_pos (hl : 1 ≤ l) (g : ℕ) : 0 < varth d l g := by
  unfold varth
  have : (0 : ℝ) < l := by exact_mod_cast hl
  positivity

theorem varth_ge (hl : 1 ≤ l) (g : ℕ) : 0.18 / l ≤ varth d l g := by
  unfold varth
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have : (1 : ℝ) ≤ 2.1 ^ (d - 1 - g) := one_le_pow₀ (by norm_num)
  rw [div_le_div_iff_of_pos_right hl']
  nlinarith

theorem varth_le (hd4 : d ≤ 4) (hl : 1 ≤ l) {g : ℕ} (hg : 1 ≤ g) : varth d l g ≤ 0.7938 / l := by
  unfold varth
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  rw [div_le_div_iff_of_pos_right hl']
  have : (2.1 : ℝ) ^ (d - 1 - g) ≤ 2.1 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith

theorem varth_le_small (hd4 : d ≤ 4) (hl : 50 ≤ l) {g : ℕ} (hg : 1 ≤ g) : varth d l g ≤ 0.016 := by
  have h := varth_le hd4 (by omega : 1 ≤ l) hg
  have hl' : (50 : ℝ) ≤ l := by exact_mod_cast hl
  have : (0.7938 : ℝ) / l ≤ 0.7938 / 50 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith

theorem varth_pred {g : ℕ} (hg : g + 1 ≤ d - 1) : varth d l g = 2.1 * varth d l (g + 1) := by
  unfold varth
  have : d - 1 - g = (d - 1 - (g + 1)) + 1 := by omega
  rw [this, pow_succ]
  ring

theorem varth_anti {g g' : ℕ} (hgg : g ≤ g') : varth d l g' ≤ varth d l g := by
  unfold varth
  rcases Nat.eq_zero_or_pos l with h0 | hl
  · simp [h0]
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  rw [div_le_div_iff_of_pos_right hl']
  have : (2.1 : ℝ) ^ (d - 1 - g') ≤ 2.1 ^ (d - 1 - g) := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith

theorem exp_16133_le : Real.exp 1.6133 ≤ 5.06 := by
  have h1 : Real.exp 1.6133 = Real.exp 1 * Real.exp 0.6133 := by
    rw [← Real.exp_add]
    norm_num
  have h2 := Real.exp_bound' (x := 0.6133) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have h3 := Real.exp_one_lt_d9
  rw [h1]
  have h4 : 0 < Real.exp 0.6133 := Real.exp_pos _
  nlinarith

theorem one_sub_pow_ge (hl : 50 ≤ l) {θ : ℝ} (_hθ0 : 0 ≤ θ) (hθ : θ ≤ 0.7938 / l) :
    (0.1975 : ℝ) ≤ (1 - θ) ^ (2 * l) := by
  have hl' : (50 : ℝ) ≤ l := by exact_mod_cast hl
  have hθ1 : θ ≤ 0.016 := by
    have : (0.7938 : ℝ) / l ≤ 0.7938 / 50 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hpos : 0 < 1 - θ := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hinv : 1 - (1 - θ)⁻¹ = -(θ / (1 - θ)) := by
    field_simp
    ring
  rw [hinv] at hlog
  have hb : 2 * l * (θ / (1 - θ)) ≤ 1.6133 := by
    rw [mul_div_assoc', div_le_iff₀ hpos]
    have : 2 * l * θ ≤ 1.5876 := by
      rw [le_div_iff₀ (by linarith)] at hθ
      linarith
    nlinarith
  have h1 : (1 - θ) ^ (2 * l) = Real.exp (2 * l * Real.log (1 - θ)) := by
    rw [← Real.exp_log (pow_pos hpos (2 * l)), Real.log_pow]
    push_cast
    ring_nf
  rw [h1]
  have h2 : -1.6133 ≤ 2 * l * Real.log (1 - θ) := by nlinarith
  have h3 : Real.exp (-1.6133) ≤ Real.exp (2 * l * Real.log (1 - θ)) := Real.exp_le_exp.2 h2
  have h4 : (0.1975 : ℝ) ≤ Real.exp (-1.6133) := by
    rw [Real.exp_neg]
    have := exp_16133_le
    rw [le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    calc Real.exp 1.6133 ≤ 5.06 := this
      _ ≤ (0.1975 : ℝ)⁻¹ := by norm_num
  linarith

theorem one_sub_varth_pow_ge (hd4 : d ≤ 4) (hl : 50 ≤ l) {g : ℕ} (hg : 1 ≤ g) :
    (0.1975 : ℝ) ≤ (1 - varth d l g) ^ (2 * l) :=
  one_sub_pow_ge hl (varth_pos (by omega) g).le (varth_le hd4 (by omega) hg)

end Numbers

section Heavy

variable {l : ℕ} {β : Type*} [Fintype β] [DecidableEq β]

def HeavyOn (d l : ℕ) (u : β → Fin d → ZMod p) (L : Submodule (ZMod p) (Fin d → ZMod p)) : Prop :=
  1 ≤ finrank (ZMod p) L ∧ finrank (ZMod p) L < d ∧
    (outL L u : ℝ) < varth d l (finrank (ZMod p) L) * Fintype.card β

def HasHeavy (d l g : ℕ) (u : β → Fin d → ZMod p) : Prop :=
  ∃ L : Submodule (ZMod p) (Fin d → ZMod p), finrank (ZMod p) L = g ∧ HeavyOn d l u L

noncomputable def gStar (d l : ℕ) (u : β → Fin d → ZMod p) : ℕ := by
  classical
  exact if h : ∃ g, HasHeavy d l g u then Nat.find h else d

omit [DecidableEq β] in
theorem gStar_le (u : β → Fin d → ZMod p) : gStar d l u ≤ d := by
  classical
  unfold gStar
  split_ifs with h
  · have h' := h
    obtain ⟨g, L, hL, hh⟩ := h'
    exact (Nat.find_min' h ⟨L, hL, hh⟩).trans (hL ▸ hh.2.1.le)
  · exact le_rfl

omit [DecidableEq β] in
theorem gStar_spec (u : β → Fin d → ZMod p) (h : gStar d l u < d) :
    ∃ L : Submodule (ZMod p) (Fin d → ZMod p), finrank (ZMod p) L = gStar d l u ∧ HeavyOn d l u L := by
  classical
  unfold gStar at h ⊢
  split_ifs at h ⊢ with h'
  · exact Nat.find_spec h'
  · exact absurd h (lt_irrefl d)

omit [DecidableEq β] in
theorem gStar_min (u : β → Fin d → ZMod p) (L : Submodule (ZMod p) (Fin d → ZMod p))
    (h1 : 1 ≤ finrank (ZMod p) L) (h2 : finrank (ZMod p) L < gStar d l u) :
    varth d l (finrank (ZMod p) L) * Fintype.card β ≤ outL L u := by
  classical
  have hd : finrank (ZMod p) L < d := lt_of_lt_of_le h2 (gStar_le u)
  by_contra hcon
  push Not at hcon
  have hH : HasHeavy d l (finrank (ZMod p) L) u := ⟨L, rfl, h1, hd, hcon⟩
  have : gStar d l u ≤ finrank (ZMod p) L := by
    unfold gStar
    rw [dite_eq_left ⟨_, hH⟩]
    exact Nat.find_min' _ hH
  omega

omit [DecidableEq β] in
theorem outL_le_add (u : β → Fin d → ZMod p) (L U : Submodule (ZMod p) (Fin d → ZMod p)) :
    outL U u ≤ outL L u + outL U (fun i : {i // u i ∈ L} => u i) := by
  classical
  unfold outL
  rw [← Nat.card_sum]
  refine Nat.card_le_card_of_injective
    (fun i : {i // u i ∉ U} => if h : u i ∈ L then Sum.inr ⟨⟨i, h⟩, i.2⟩ else Sum.inl ⟨i, h⟩) ?_
  intro x y hxy
  by_cases hx : u x ∈ L <;> by_cases hy : u y ∈ L <;> simp [hx, hy] at hxy
  · exact Subtype.ext hxy
  · exact Subtype.ext hxy

omit [DecidableEq β] in
theorem outL_bot (u : β → Fin d → ZMod p) (hu0 : ∀ i, u i ≠ 0) :
    outL ⊥ u = Fintype.card β := by
  have : ∀ i, u i ∉ (⊥ : Submodule (ZMod p) (Fin d → ZMod p)) := fun i h =>
    hu0 i ((Submodule.mem_bot _).1 h)
  unfold outL
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv this), Nat.card_eq_fintype_card]

omit [DecidableEq β] in
theorem step3 {s : ℕ} (H : BDHyp p d l s) (u : β → Fin d → ZMod p) (hu0 : ∀ i, u i ≠ 0)
    {L : Submodule (ZMod p) (Fin d → ZMod p)} (hLdim : finrank (ZMod p) L = gStar d l u)
    (hLh : HeavyOn d l u L) (U : Submodule (ZMod p) (Fin d → ZMod p)) (hUL : U ≤ L) (hUne : U ≠ L) :
    (0.18 : ℝ) * Nat.card {i // u i ∈ L} / l ≤ outL U (fun i : {i // u i ∈ L} => u i) := by
  classical
  have hl1 : 1 ≤ l := by have := H.hl; omega
  have hlR : (50 : ℝ) ≤ l := by exact_mod_cast H.hl
  set mstar := Nat.card {i // u i ∈ L} with hmstar
  rcases Nat.eq_zero_or_pos (finrank (ZMod p) U) with hU0 | hU1
  ·
    have hUbot : U = ⊥ := Submodule.finrank_eq_zero.1 hU0
    subst hUbot
    rw [outL_bot (fun i : {i // u i ∈ L} => u i) (fun i => hu0 i), ← Nat.card_eq_fintype_card,
      ← hmstar]
    have h0 : (0 : ℝ) ≤ mstar := Nat.cast_nonneg _
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hlt : finrank (ZMod p) U < finrank (ZMod p) L :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hUL hUne)
  rw [hLdim] at hlt
  have hmin := gStar_min u U hU1 hlt
  have hadd := outL_le_add u L U
  have hheavy := hLh.2.2
  rw [hLdim] at hheavy
  have hg2 : 2 ≤ gStar d l u := by omega
  have hgd : gStar d l u ≤ d - 1 := by
    have := hLh.2.1
    omega
  have hpred := varth_pred (d := d) (l := l) (g := gStar d l u - 1) (by omega)
  rw [show gStar d l u - 1 + 1 = gStar d l u by omega] at hpred
  have hanti := varth_anti (d := d) (l := l) (show finrank (ZMod p) U ≤ gStar d l u - 1 by omega)
  have hge := varth_ge (d := d) hl1 (gStar d l u)
  have hj : (mstar : ℝ) ≤ Fintype.card β := by
    rw [hmstar, Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_subtype_le _
  have hjnn : (0 : ℝ) ≤ Fintype.card β := Nat.cast_nonneg _
  by_contra hcon
  push Not at hcon
  have h1 : (outL U u : ℝ) ≤ outL L u + outL U (fun i : {i // u i ∈ L} => u i) := by
    exact_mod_cast hadd
  have h2 : (0.18 : ℝ) * mstar / l ≤ 0.18 / l * Fintype.card β := by
    have e : (0.18 : ℝ) * mstar / l = 0.18 / l * mstar := by ring
    rw [e]
    gcongr
  nlinarith

end Heavy

section Step4

variable {l s : ℕ} {β : Type*} [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
theorem rl_ge_restrict {G : Type*} [AddCommGroup G] [DecidableEq G] (l : ℕ) (P : β → Prop)
    [DecidablePred P] (w : β → G) :
    ((Fintype.card {i // P i} : ℝ) / Fintype.card β) ^ (2 * l) * rl l (fun i : {i // P i} => w i) ≤
      rl l w := by
  have hR := Rl_restrict_le l P w
  unfold rl
  rcases Nat.eq_zero_or_pos (Fintype.card β) with h0 | hpos
  · have : (Fintype.card {i // P i} : ℝ) = 0 := by
      have := Fintype.card_subtype_le P
      rw [h0] at this
      have : Fintype.card {i // P i} = 0 := by omega
      exact_mod_cast this
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl
      simp only [mul_zero, pow_zero, div_one, one_mul]
      exact_mod_cast hR
    · rw [this, zero_div, zero_pow (by omega), zero_mul]
      positivity
  have hb : (0 : ℝ) < Fintype.card β := by exact_mod_cast hpos
  rcases Nat.eq_zero_or_pos (Fintype.card {i // P i}) with h0' | hpos'
  · rw [h0']
    simp only [Nat.cast_zero, zero_div]
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl
      simp only [mul_zero, pow_zero, div_one, one_mul]
      exact_mod_cast hR
    · rw [zero_pow (by omega), zero_mul]
      positivity
  have hb' : (0 : ℝ) < Fintype.card {i // P i} := by exact_mod_cast hpos'
  have hR' : (Rl l (fun i : {i // P i} => w i) : ℝ) ≤ Rl l w := by exact_mod_cast hR
  rw [div_pow, mul_pow, mul_pow]
  rw [le_div_iff₀ (by positivity)]
  calc (Fintype.card {i // P i} : ℝ) ^ (2 * l) / (Fintype.card β : ℝ) ^ (2 * l) *
        ((Rl l (fun i : {i // P i} => w i) : ℝ) /
          (2 ^ (2 * l) * (Fintype.card {i // P i} : ℝ) ^ (2 * l))) *
        (2 ^ (2 * l) * (Fintype.card β : ℝ) ^ (2 * l)) = Rl l (fun i : {i // P i} => w i) := by
        field_simp
    _ ≤ Rl l w := hR'

theorem degen_le_of_hs3 (H : BDHyp p d l s) {j : ℝ} (hj : (s : ℝ) ≤ j) :
    j ^ (-(l : ℝ) / 2) * (3 * l / 2 : ℝ) ^ (2 * l) ≤ 0.01 / (p : ℝ) ^ (d - 1) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : (1 : ℝ) ≤ s := by
    have := H.hs4
    have : 1 ≤ s := by have := H.hl; omega
    exact_mod_cast this
  have hj0 : 0 < j := by linarith
  have h1 : (s : ℝ) ^ ((l : ℝ) / 2) ≤ j ^ ((l : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith) hj (by positivity)
  have h2 := H.hs3.trans h1
  have hpd : (0 : ℝ) < (p : ℝ) ^ (d - 1) := by positivity
  have h3 : (3 * l / 2 : ℝ) ^ (2 * l) ≤ j ^ ((l : ℝ) / 2) / (100 * (p : ℝ) ^ (d - 1)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hjj : j ^ (-(l : ℝ) / 2) * j ^ ((l : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hj0]
    have : -(l : ℝ) / 2 + (l : ℝ) / 2 = 0 := by ring
    rw [this, Real.rpow_zero]
  calc j ^ (-(l : ℝ) / 2) * (3 * l / 2 : ℝ) ^ (2 * l)
      ≤ j ^ (-(l : ℝ) / 2) * (j ^ ((l : ℝ) / 2) / (100 * (p : ℝ) ^ (d - 1))) :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hj0.le _)
    _ = 0.01 / (p : ℝ) ^ (d - 1) := by
        rw [mul_div_assoc', hjj]
        ring

theorem tBlock_div (N δ ρ0 : ℝ) (hN : 0 < N) (s l : ℕ) :
    tBlock N δ ρ0 s l / N = δ * ρ0 * √(s : ℝ) / (32 * (1 + δ) * √(π * l)) := by
  unfold tBlock
  field_simp

theorem varpi_mul (hl : 1 ≤ l) (hs : 1 ≤ s) :
    (1 / 100 : ℝ) * varpi l s * √(s : ℝ) / ((1 + 1 / 100) * √(π * l)) = 6 := by
  unfold varpi
  have h1 : 0 < √(π * l) := Real.sqrt_pos.2 (by
    have : (0 : ℝ) < l := by exact_mod_cast hl
    positivity)
  have h2 : 0 < √(s : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hs)
  field_simp

theorem step4_case1 (H : BDHyp p d l s) (u : β → Fin d → ZMod p) (hu0 : ∀ i, u i ≠ 0)
    (hj : s ≤ Fintype.card β) {ρ0 : ℝ} (hρ0 : (1 + 1 / 100) / (p : ℝ) ^ d ≤ ρ0)
    (hu : ρ0 ≤ rhoHat u) (hg : gStar d l u = d) :
    tBlock ((p : ℝ) ^ d) (1 / 100) ρ0 s l * (2 * Fintype.card β : ℝ) ^ (2 * l) / (p : ℝ) ^ d ≤
      Rl' l u := by
  classical
  have hl1 : 1 ≤ l := by have := H.hl; omega
  refine prop_blockdelta_a H.hp2 (by have := H.hd2; omega) hl1 (by norm_num) (by norm_num)
    H.hs1 H.hs2 hρ0 u hj hu fun K hK => ?_
  set U := AddSubgroup.toZModSubmodule p K with hU
  have hmem : ∀ x, x ∈ U ↔ x ∈ K := fun x => Iff.rfl
  have hcard : Nat.card {j // u j ∉ K} = outL U u := rfl
  rw [hcard]
  have hUtop : U ≠ ⊤ := by
    intro h
    apply hK
    rw [eq_top_iff]
    intro x _
    rw [← hmem, h]
    exact Submodule.mem_top
  have hβ : (0 : ℝ) ≤ Fintype.card β := Nat.cast_nonneg _
  have hlR : (50 : ℝ) ≤ l := by exact_mod_cast H.hl
  rcases Nat.eq_zero_or_pos (finrank (ZMod p) U) with h0 | h1
  · have : U = ⊥ := Submodule.finrank_eq_zero.1 h0
    rw [this, outL_bot u hu0]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · have hlt : finrank (ZMod p) U < d := by
      have := Submodule.finrank_lt hUtop
      simpa using this
    have hmin := gStar_min u U h1 (by rw [hg]; exact hlt)
    have hge := varth_ge (d := d) hl1 (finrank (ZMod p) U)
    have : (0.18 : ℝ) * Fintype.card β / l = 0.18 / l * Fintype.card β := by ring
    rw [this]
    nlinarith

omit [DecidableEq β] in
theorem gStar_basic (_H : BDHyp p d l s) (u : β → Fin d → ZMod p) (hg : gStar d l u < d) :
    ∃ L : Submodule (ZMod p) (Fin d → ZMod p), finrank (ZMod p) L = gStar d l u ∧
      HeavyOn d l u L ∧ 1 ≤ gStar d l u ∧ gStar d l u ≤ d - 1 := by
  obtain ⟨L, hLdim, hLh⟩ := gStar_spec u hg
  exact ⟨L, hLdim, hLh, hLdim ▸ hLh.1, by omega⟩

theorem step4_case2 (H : BDHyp p d l s) (u : β → Fin d → ZMod p) (hj : s ≤ Fintype.card β)
    {ρ0 : ℝ} (_hρ0pos : 0 < ρ0) (hg : gStar d l u < d)
    (hρ : ρ0 ≤ varpi l s / (p : ℝ) ^ gStar d l u) :
    tBlock ((p : ℝ) ^ d) (1 / 100) ρ0 s l * (2 * Fintype.card β : ℝ) ^ (2 * l) / (p : ℝ) ^ d ≤
      Rl' l u := by
  obtain ⟨L, hLdim, hLh, hg1, hgd⟩ := gStar_basic H u hg
  set g := gStar d l u with hgdef
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hl1 : 1 ≤ l := by have := H.hl; omega
  have hs1 : 1 ≤ s := by have := H.hs4; omega
  set j : ℝ := (Fintype.card β : ℝ) with hjdef
  have hjs : (s : ℝ) ≤ j := by rw [hjdef]; exact_mod_cast hj
  have hβ1 : 1 ≤ Fintype.card β := le_trans hs1 hj
  have hθ := one_sub_varth_pow_ge H.hd4 H.hl hg1 (d := d)
  have hlh := lem_lineheavy L (varth_pos hl1 _).le (by
    have := varth_le_small H.hd4 H.hl hg1 (d := d)
    linarith) l u hβ1 (by
      have := hLh.2.2
      rw [hLdim] at this
      linarith)
  rw [hLdim] at hlh
  have hpg : (0 : ℝ) < (p : ℝ) ^ g := by positivity
  have hrl : 0.1975 / (p : ℝ) ^ g ≤ rl l u :=
    le_trans (div_le_div_of_nonneg_right hθ hpg.le) hlh
  have hdeg := degen_le_of_hs3 H hjs
  have hpgd : (p : ℝ) ^ g ≤ (p : ℝ) ^ (d - 1) := pow_le_pow_right₀ hp1 hgd
  have hdeg' : 0.01 / (p : ℝ) ^ (d - 1) ≤ 0.01 / (p : ℝ) ^ g :=
    div_le_div_of_nonneg_left (by norm_num) hpg hpgd
  have h3l : 3 * l ≤ 2 * Fintype.card β := by have := H.hs4; omega
  have hdb := degen_bound l hl1 u h3l
  rw [← hjdef] at hdb
  have hN : (0 : ℝ) < (p : ℝ) ^ d := by positivity
  have ht : tBlock ((p : ℝ) ^ d) (1 / 100) ρ0 s l / (p : ℝ) ^ d ≤ 0.1875 / (p : ℝ) ^ g := by
    rw [tBlock_div _ _ _ hN]
    have hπl : 0 < √(π * l) := Real.sqrt_pos.2 (by
      have : (0 : ℝ) < l := by exact_mod_cast hl1
      positivity)
    have hsq : 0 ≤ √(s : ℝ) := Real.sqrt_nonneg _
    calc 1 / 100 * ρ0 * √(s : ℝ) / (32 * (1 + 1 / 100) * √(π * l))
        ≤ 1 / 100 * (varpi l s / (p : ℝ) ^ g) * √(s : ℝ) / (32 * (1 + 1 / 100) * √(π * l)) := by
          gcongr
      _ = (1 / 100 * varpi l s * √(s : ℝ) / ((1 + 1 / 100) * √(π * l))) / 32 / (p : ℝ) ^ g := by
          field_simp
      _ = 0.1875 / (p : ℝ) ^ g := by
          rw [varpi_mul hl1 hs1]
          norm_num
  have h2j : (0 : ℝ) < (2 * j) ^ (2 * l) := by positivity
  calc tBlock ((p : ℝ) ^ d) (1 / 100) ρ0 s l * (2 * j) ^ (2 * l) / (p : ℝ) ^ d
      = tBlock ((p : ℝ) ^ d) (1 / 100) ρ0 s l / (p : ℝ) ^ d * (2 * j) ^ (2 * l) := by ring
    _ ≤ 0.1875 / (p : ℝ) ^ g * (2 * j) ^ (2 * l) := mul_le_mul_of_nonneg_right ht h2j.le
    _ ≤ (rl l u - j ^ (-(l : ℝ) / 2) * (3 * l / 2 : ℝ) ^ (2 * l)) * (2 * j) ^ (2 * l) := by
        apply mul_le_mul_of_nonneg_right _ h2j.le
        have : 0.1875 / (p : ℝ) ^ g = 0.1975 / (p : ℝ) ^ g - 0.01 / (p : ℝ) ^ g := by ring
        linarith
    _ ≤ Rl' l u := hdb

theorem log_20_le (hd4 : d ≤ 4) {g : ℕ} (hgd : g ≤ d - 1) :
    Real.log (20 * (p : ℝ) ^ g) ≤ 0.98 * Real.log (200 * (p : ℝ) ^ d) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hnat : (20 * p ^ g) ^ 50 ≤ (200 * p ^ d) ^ 49 := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    have h1 : p ^ (g * 50) ≤ p ^ (d * 49) := Nat.pow_le_pow_right hp1 (by omega)
    have h2 : (20 : ℕ) ^ 50 ≤ 200 ^ 49 := by norm_num
    exact Nat.mul_le_mul h2 h1
  have hreal : ((20 : ℝ) * (p : ℝ) ^ g) ^ 50 ≤ ((200 : ℝ) * (p : ℝ) ^ d) ^ 49 := by
    exact_mod_cast hnat
  have hpos : (0 : ℝ) < 20 * (p : ℝ) ^ g := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  have hl := Real.log_le_log (by positivity) hreal
  rw [Real.log_pow, Real.log_pow] at hl
  push_cast at hl
  linarith

theorem sqrt_ratio_ge {l s : ℕ} (hl : 1 ≤ l) (hs : 1400 * l ≤ s) : 21 * √(π * l) ≤ √(s : ℝ) := by
  have hsR : (1400 : ℝ) * l ≤ s := by exact_mod_cast hs
  have hpi := Real.pi_lt_d2
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have e : 21 * √(π * l) = √(441 * (π * l)) := by
    rw [show (441 : ℝ) * (π * l) = 21 ^ 2 * (π * l) by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 21 ^ 2), Real.sqrt_sq (by norm_num)]
  rw [e]
  apply Real.sqrt_le_sqrt
  nlinarith

set_option maxHeartbeats 1000000 in
theorem step4_case3 (H : BDHyp p d l s) (u : β → Fin d → ZMod p) (hu0 : ∀ i, u i ≠ 0)
    (hj : s ≤ Fintype.card β) {ρ0 : ℝ} (hρ0pos : 0 < ρ0) (hu : ρ0 ≤ rhoHat u)
    (hg : gStar d l u < d) (hρ : 1.1 / (p : ℝ) ^ gStar d l u ≤ ρ0) :
    tBlock ((p : ℝ) ^ d) (1 / 100) ρ0 s l * (2 * Fintype.card β : ℝ) ^ (2 * l) / (p : ℝ) ^ d ≤
      Rl' l u := by
  classical
  obtain ⟨L, hLdim, hLh, hg1, hgd⟩ := gStar_basic H u hg
  set g := gStar d l u with hgdef
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hl1 : 1 ≤ l := by have := H.hl; omega
  have hlR : (50 : ℝ) ≤ l := by exact_mod_cast H.hl
  have hs1 : 1 ≤ s := by have := H.hs4; omega
  have hsR : (1400 : ℝ) * l ≤ s := by exact_mod_cast H.hs4
  set j : ℝ := (Fintype.card β : ℝ) with hjdef
  have hjs : (s : ℝ) ≤ j := by rw [hjdef]; exact_mod_cast hj
  have hpg : (0 : ℝ) < (p : ℝ) ^ g := by positivity
  have hθ := varth_le_small H.hd4 H.hl hg1 (d := d)
  have hθ0 := (varth_pos (d := d) hl1 g).le
  set mstar := Fintype.card {i // u i ∈ L} with hmstar
  have hsplit : (mstar : ℝ) + outL L u = j := by
    have h2 : outL L u = Fintype.card {i // ¬ u i ∈ L} := by
      rw [outL, Nat.card_eq_fintype_card]
    have h3 : mstar + Fintype.card {i // ¬ u i ∈ L} = Fintype.card β := by
      rw [hmstar, Fintype.card_subtype_compl]
      have := Fintype.card_subtype_le (fun i => u i ∈ L)
      omega
    rw [h2, hjdef]
    exact_mod_cast h3
  have hheavy := hLh.2.2
  rw [hLdim] at hheavy
  have hmj : (1 - varth d l g) * j ≤ mstar := by nlinarith
  have hm98 : 0.984 * (s : ℝ) ≤ mstar := by nlinarith
  have hm1 : 1 ≤ mstar := by
    have : (1 : ℝ) ≤ mstar := by nlinarith
    exact_mod_cast this
  have hU := step3 H u hu0 hLdim hLh
  have hhal := halasz_subspace H.hp2 L (fun i : {i // u i ∈ L} => u i) (fun i => i.2) hl1 hm1
    (fun U hUL hUne => by
      have := hU U hUL hUne
      rwa [Nat.card_eq_fintype_card] at this)
  rw [hLdim] at hhal
  set rstar := rl l (fun i : {i // u i ∈ L} => u i) with hrstar
  have hρu : ρ0 ≤ rhoHat (fun i : {i // u i ∈ L} => u i) :=
    hu.trans (rhoHat_le_restrict (fun i => u i ∈ L) u)
  have hexp : Real.exp (-(mstar : ℝ) / (16 * l)) ≤ ρ0 / 22 := by
    have hlog := log_20_le H.hd4 (p := p) hgd
    have h200 : Real.log (2 * (p : ℝ) ^ d / (1 / 100)) = Real.log (200 * (p : ℝ) ^ d) := by
      congr 1
      ring
    have hs1' := H.hs1
    rw [h200] at hs1'
    have hlog0 : 0 ≤ Real.log (200 * (p : ℝ) ^ d) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ (p : ℝ) ^ d := one_le_pow₀ hp1
      linarith)
    have h1 : Real.log (20 * (p : ℝ) ^ g) ≤ (mstar : ℝ) / (16 * l) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h2 : Real.exp (-(mstar : ℝ) / (16 * l)) ≤ Real.exp (-Real.log (20 * (p : ℝ) ^ g)) := by
      apply Real.exp_le_exp.2
      rw [neg_div]
      linarith
    rw [Real.exp_neg, Real.exp_log (by positivity)] at h2
    have h3 : (1 : ℝ) / (p : ℝ) ^ g ≤ ρ0 / 1.1 := by
      rw [div_le_div_iff₀ hpg (by norm_num)]
      rw [div_le_iff₀ hpg] at hρ
      linarith
    calc Real.exp (-(mstar : ℝ) / (16 * l)) ≤ (20 * (p : ℝ) ^ g)⁻¹ := h2
      _ = (1 / (p : ℝ) ^ g) / 20 := by field_simp
      _ ≤ (ρ0 / 1.1) / 20 := by gcongr
      _ ≤ ρ0 / 22 := by
          rw [div_div]
          apply div_le_div_of_nonneg_left hρ0pos.le (by norm_num) (by norm_num)
  have hinvp : (1 : ℝ) / (p : ℝ) ^ g ≤ ρ0 / 1.1 := by
    rw [div_le_div_iff₀ hpg (by norm_num)]
    rw [div_le_iff₀ hpg] at hρ
    linarith
  have hπl : 0 < √(π * l) := Real.sqrt_pos.2 (by positivity)
  have hmR : (0 : ℝ) < mstar := by exact_mod_cast hm1
  have hsm : 0 < √(mstar : ℝ) := Real.sqrt_pos.2 hmR
  have h8 : ρ0 / 22 ≤ 8 * √(π * l / mstar) * rstar := by
    have : ρ0 ≤ 1 / (p : ℝ) ^ g + 8 * √(π * l / mstar) * rstar + Real.exp (-(mstar : ℝ) / (16 * l)) :=
      hρu.trans hhal
    have h11 : ρ0 / 1.1 + ρ0 / 22 + ρ0 / 22 = ρ0 := by
      field_simp
      ring
    linarith
  have hsq : √(π * l / mstar) = √(π * l) / √(mstar : ℝ) := Real.sqrt_div' _ hmR.le
  rw [hsq] at h8
  have hrstarge : ρ0 * √(mstar : ℝ) / (176 * √(π * l)) ≤ rstar := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hπl)]
    have : ρ0 / 22 * √(mstar : ℝ) ≤ 8 * (√(π * l) / √(mstar : ℝ)) * rstar * √(mstar : ℝ) :=
      mul_le_mul_of_nonneg_right h8 hsm.le
    have e : 8 * (√(π * l) / √(mstar : ℝ)) * rstar * √(mstar : ℝ) = 8 * √(π * l) * rstar := by
      field_simp
    rw [e] at this
    nlinarith
  have hrr := rl_ge_restrict l (fun i => u i ∈ L) u
  rw [← hmstar, ← hjdef, ← hrstar] at hrr
  have hratio : (1 - varth d l g) ≤ (mstar : ℝ) / j := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hpow : (0.1975 : ℝ) ≤ ((mstar : ℝ) / j) ^ (2 * l) :=
    (one_sub_varth_pow_ge H.hd4 H.hl hg1).trans
      (pow_le_pow_left₀ (by linarith) hratio _)
  have hrst0 : 0 ≤ rstar := rl_nonneg l _
  have hrl : 0.1975 * (ρ0 * √(mstar : ℝ) / (176 * √(π * l))) ≤ rl l u := by
    calc 0.1975 * (ρ0 * √(mstar : ℝ) / (176 * √(π * l))) ≤ 0.1975 * rstar :=
          mul_le_mul_of_nonneg_left hrstarge (by norm_num)
      _ ≤ ((mstar : ℝ) / j) ^ (2 * l) * rstar := mul_le_mul_of_nonneg_right hpow hrst0
      _ ≤ rl l u := hrr
  have hsqm : 0.98 * √(s : ℝ) ≤ √(mstar : ℝ) := by
    have : √(0.984 * (s : ℝ)) ≤ √(mstar : ℝ) := Real.sqrt_le_sqrt hm98
    rw [Real.sqrt_mul (by norm_num)] at this
    have h98 : (0.98 : ℝ) ≤ √0.984 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    nlinarith [Real.sqrt_nonneg (s : ℝ)]
  set X := ρ0 * √(s : ℝ) / √(π * l) with hX
  have hA : 21 * ρ0 ≤ X := by
    rw [hX, le_div_iff₀ hπl]
    have h2 := sqrt_ratio_ge hl1 H.hs4
    calc 21 * ρ0 * √(π * l) = ρ0 * (21 * √(π * l)) := by ring
      _ ≤ ρ0 * √(s : ℝ) := mul_le_mul_of_nonneg_left h2 hρ0pos.le
  have hrlX : 0.1975 * 0.98 / 176 * X ≤ rl l u := by
    refine le_trans ?_ hrl
    rw [hX]
    have : ρ0 * (0.98 * √(s : ℝ)) ≤ ρ0 * √(mstar : ℝ) := mul_le_mul_of_nonneg_left hsqm hρ0pos.le
    calc 0.1975 * 0.98 / 176 * (ρ0 * √(s : ℝ) / √(π * l))
        = 0.1975 * (ρ0 * (0.98 * √(s : ℝ)) / (176 * √(π * l))) := by field_simp
      _ ≤ 0.1975 * (ρ0 * √(mstar : ℝ) / (176 * √(π * l))) := by gcongr
  have hdeg := degen_le_of_hs3 H hjs
  have hpgd : (p : ℝ) ^ g ≤ (p : ℝ) ^ (d - 1) := pow_le_pow_right₀ hp1 hgd
  have hdeg' : 0.01 / (p : ℝ) ^ (d - 1) ≤ 0.01 * (ρ0 / 1.1) := by
    calc 0.01 / (p : ℝ) ^ (d - 1) ≤ 0.01 / (p : ℝ) ^ g :=
          div_le_div_of_nonneg_left (by norm_num) hpg hpgd
      _ = 0.01 * (1 / (p : ℝ) ^ g) := by ring
      _ ≤ 0.01 * (ρ0 / 1.1) := by gcongr
  have h3l : 3 * l ≤ 2 * Fintype.card β := by have := H.hs4; omega
  have hdb := degen_bound l hl1 u h3l
  rw [← hjdef] at hdb
  have hN : (0 : ℝ) < (p : ℝ) ^ d := by positivity
  have ht : tBlock ((p : ℝ) ^ d) (1 / 100) ρ0 s l / (p : ℝ) ^ d = X / 3232 := by
    rw [tBlock_div _ _ _ hN, hX]
    field_simp
    ring
  have hj0 : (0 : ℝ) < j := by
    have : (1 : ℝ) ≤ s := by exact_mod_cast hs1
    linarith
  have h2j : (0 : ℝ) < (2 * j) ^ (2 * l) := pow_pos (by linarith) _
  have hX0 : 0 ≤ X := by positivity
  have hdeg2 : j ^ (-(l : ℝ) / 2) * (3 * l / 2 : ℝ) ^ (2 * l) ≤ ρ0 / 110 := by
    have e : (0.01 : ℝ) * (ρ0 / 1.1) = ρ0 / 110 := by
      field_simp
      norm_num
    linarith
  have hρX : ρ0 ≤ X / 21 := by linarith
  have hrl2 : X * (1975 * 98 / (10000 * 100 * 176)) ≤ rl l u := by
    have e : (0.1975 : ℝ) * 0.98 / 176 * X = X * (1975 * 98 / (10000 * 100 * 176)) := by
      norm_num
      ring
    linarith
  calc tBlock ((p : ℝ) ^ d) (1 / 100) ρ0 s l * (2 * j) ^ (2 * l) / (p : ℝ) ^ d
      = tBlock ((p : ℝ) ^ d) (1 / 100) ρ0 s l / (p : ℝ) ^ d * (2 * j) ^ (2 * l) := by ring
    _ = X / 3232 * (2 * j) ^ (2 * l) := by rw [ht]
    _ ≤ (rl l u - j ^ (-(l : ℝ) / 2) * (3 * l / 2 : ℝ) ^ (2 * l)) * (2 * j) ^ (2 * l) := by
        apply mul_le_mul_of_nonneg_right _ h2j.le
        linarith
    _ ≤ Rl' l u := hdb

end Step4

section Step5

variable {l s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem outL_block (b : Finset ι) (y : ι → Fin d → ZMod p) (L : Submodule (ZMod p) (Fin d → ZMod p))
    [DecidablePred (· ∈ L)] :
    outL L (fun x : b => y x) = (b.filter fun x => y x ∉ L).card := by
  unfold outL
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← card_map (Function.Embedding.subtype (· ∈ b))]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨x'.2, hx'⟩
  · rintro ⟨hx, hx'⟩
    exact ⟨⟨x, hx⟩, hx', rfl⟩

noncomputable def memCount (b : Finset ι) (i : ι) (y : ι → Fin d → ZMod p)
    (L : Submodule (ZMod p) (Fin d → ZMod p)) : ℕ :=
  Nat.card {x // x ∈ b.erase i ∧ y x ∉ L}

theorem memCount_eq (b : Finset ι) (i : ι) (y : ι → Fin d → ZMod p)
    (L : Submodule (ZMod p) (Fin d → ZMod p)) [DecidablePred (· ∈ L)] :
    memCount b i y L = ((b.erase i).filter fun x => y x ∉ L).card := by
  unfold memCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext x
  simp

def MemCond (d l g : ℕ) (b : Finset ι) (i : ι) (y : ι → Fin d → ZMod p)
    (L : Submodule (ZMod p) (Fin d → ZMod p)) : Prop :=
  finrank (ZMod p) L = g ∧ (memCount b i y L : ℝ) < varth d l g * b.card

noncomputable def memAOf (P : Submodule (ZMod p) (Fin d → ZMod p) → Prop) :
    Finset (Fin d → ZMod p) := by
  classical
  exact if h : ∃! L, P L then univ.filter (· ∈ Classical.choose h.exists) else ∅

noncomputable def memA (d l g : ℕ) (b : Finset ι) (i : ι) (y : ι → Fin d → ZMod p) :
    Finset (Fin d → ZMod p) :=
  memAOf (MemCond (p := p) d l g b i y)

noncomputable def subMeas (ν : (Fin d → ZMod p) → ℝ) (L : Submodule (ZMod p) (Fin d → ZMod p)) :
    ℝ := by
  classical
  exact ∑ a ∈ univ.filter (· ∈ L), ν a

omit [Fintype ι] in
theorem memCond_local {g : ℕ} {b : Finset ι} {i : ι} {y y' : ι → Fin d → ZMod p}
    (h : ∀ x ∈ b, x ≠ i → y x = y' x) : MemCond (p := p) d l g b i y = MemCond d l g b i y' := by
  funext L
  have : memCount b i y L = memCount b i y' L := by
    unfold memCount
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · rintro ⟨hx, hxL⟩
      refine ⟨hx, ?_⟩
      rwa [← h x (mem_of_mem_erase hx) (ne_of_mem_erase hx)]
    · rintro ⟨hx, hxL⟩
      refine ⟨hx, ?_⟩
      rwa [h x (mem_of_mem_erase hx) (ne_of_mem_erase hx)]
  unfold MemCond
  rw [this]

omit [Fintype ι] in
theorem memA_local {g : ℕ} {b : Finset ι} {i : ι} {y y' : ι → Fin d → ZMod p}
    (h : ∀ x ∈ b, x ≠ i → y x = y' x) : memA (p := p) d l g b i y = memA d l g b i y' := by
  unfold memA
  rw [memCond_local h]

omit [Fintype ι] in
theorem memA_sum_le (ν : (Fin d → ZMod p) → ℝ) {κg : ℝ} (hκ0 : 0 ≤ κg) {g : ℕ}
    (hκ : ∀ L : Submodule (ZMod p) (Fin d → ZMod p), finrank (ZMod p) L = g → subMeas ν L ≤ κg)
    (b : Finset ι) (i : ι) (y : ι → Fin d → ZMod p) : ∑ a ∈ memA (p := p) d l g b i y, ν a ≤ κg := by
  classical
  unfold memA memAOf
  split_ifs with h
  · have hL := (Classical.choose_spec h.exists).1
    have := hκ _ hL
    unfold subMeas at this
    convert this
  · simp [hκ0]

theorem step5 (H : BDHyp p d l s) (b : Finset ι) (y : ι → Fin d → ZMod p) (hy0 : ∀ x, y x ≠ 0)
    (hb : s < b.card) {L : Submodule (ZMod p) (Fin d → ZMod p)}
    (hLdim : finrank (ZMod p) L = gStar d l (fun x : b => y x))
    (hLh : HeavyOn d l (fun x : b => y x) L) {i : ι} (hi : i ∈ b) (hiL : y i ∈ L) :
    y i ∈ memA (p := p) d l (gStar d l (fun x : b => y x)) b i y := by
  classical
  set u := fun x : b => y x with hu
  set g := gStar d l u with hgdef
  have hl1 : 1 ≤ l := by have := H.hl; omega
  have hg1 : 1 ≤ g := hLdim ▸ hLh.1
  have hgd : g ≤ d - 1 := by have := hLh.2.1; omega
  have hθ := varth_le_small H.hd4 H.hl hg1 (d := d)
  have hθge := varth_ge (d := d) hl1 g
  have hjR : (1400 : ℝ) * l < b.card := by
    have : 1400 * l < b.card := lt_of_le_of_lt H.hs4 hb
    exact_mod_cast this
  have hlR : (50 : ℝ) ≤ l := by exact_mod_cast H.hl
  have hcardu : Fintype.card {x // x ∈ b} = b.card := Fintype.card_coe b
  have herase : ∀ M : Submodule (ZMod p) (Fin d → ZMod p),
      (b.filter fun x => y x ∉ M).card ≤ ((b.erase i).filter fun x => y x ∉ M).card + 1 := by
    intro M
    calc (b.filter fun x => y x ∉ M).card ≤ (insert i ((b.erase i).filter fun x => y x ∉ M)).card := by
          refine card_le_card fun x hx => ?_
          rw [mem_filter] at hx
          by_cases hxi : x = i
          · rw [hxi]; exact mem_insert_self _ _
          · exact mem_insert_of_mem (mem_filter.2 ⟨mem_erase.2 ⟨hxi, hx.1⟩, hx.2⟩)
      _ ≤ _ := card_insert_le _ _
  have hLcond : MemCond d l g b i y L := by
    refine ⟨hLdim, ?_⟩
    have h1 : ((b.erase i).filter fun x => y x ∉ L) = b.filter fun x => y x ∉ L := by
      ext x
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨⟨-, hx⟩, h⟩
        exact ⟨hx, h⟩
      · rintro ⟨hx, h⟩
        exact ⟨⟨fun hxi => h (hxi ▸ hiL), hx⟩, h⟩
    rw [memCount_eq, h1, ← outL_block]
    have := hLh.2.2
    rw [hLdim, hcardu] at this
    exact this
  have huniq : ∀ L', MemCond d l g b i y L' → L' = L := by
    intro L' hL'
    by_contra hne
    obtain ⟨hL'dim, hL'c⟩ := hL'
    have hLc := hLcond.2
    rw [memCount_eq] at hL'c hLc
    set L'' := L' ⊓ L with hL''
    have hsub : ((b.erase i).filter fun x => y x ∉ L'') ⊆
        ((b.erase i).filter fun x => y x ∉ L') ∪ ((b.erase i).filter fun x => y x ∉ L) := by
      intro x hx
      rw [mem_filter] at hx
      rw [mem_union, mem_filter, mem_filter]
      by_cases h1 : y x ∈ L'
      · right
        exact ⟨hx.1, fun h2 => hx.2 (Submodule.mem_inf.2 ⟨h1, h2⟩)⟩
      · left
        exact ⟨hx.1, h1⟩
    have hcnt : (((b.erase i).filter fun x => y x ∉ L'').card : ℝ) < 2 * varth d l g * b.card := by
      have := (card_le_card hsub).trans (card_union_le _ _)
      have : (((b.erase i).filter fun x => y x ∉ L'').card : ℝ) ≤
          ((b.erase i).filter fun x => y x ∉ L').card + ((b.erase i).filter fun x => y x ∉ L).card := by
        exact_mod_cast this
      linarith
    have hle : L'' ≤ L := inf_le_right
    have hneq : L'' ≠ L := by
      intro heq
      apply hne
      have hLL' : L ≤ L' := by
        rw [← heq]
        exact inf_le_left
      exact (Submodule.eq_of_le_of_finrank_eq hLL' (by rw [hL'dim, hLdim])).symm
    have hdimlt : finrank (ZMod p) L'' < g := by
      rw [← hLdim]
      exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hneq)
    rcases Nat.eq_zero_or_pos (finrank (ZMod p) L'') with h0 | h1
    ·
      have hbot : L'' = ⊥ := Submodule.finrank_eq_zero.1 h0
      rw [hbot] at hcnt
      have : ((b.erase i).filter fun x => y x ∉ (⊥ : Submodule (ZMod p) (Fin d → ZMod p))) =
          b.erase i := by
        refine filter_true_of_mem fun x _ h => hy0 x ((Submodule.mem_bot _).1 h)
      rw [this, card_erase_of_mem hi] at hcnt
      have hb1 : 1 ≤ b.card := by omega
      push_cast [hb1] at hcnt
      nlinarith
    ·
      have hmin := gStar_min u L'' h1 hdimlt
      rw [outL_block, hcardu] at hmin
      have hg2 : 2 ≤ g := by omega
      have hpred := varth_pred (d := d) (l := l) (g := g - 1) (by omega)
      rw [show g - 1 + 1 = g by omega] at hpred
      have hanti := varth_anti (d := d) (l := l) (show finrank (ZMod p) L'' ≤ g - 1 by omega)
      have he := herase L''
      have he' : ((b.filter fun x => y x ∉ L'').card : ℝ) ≤
          ((b.erase i).filter fun x => y x ∉ L'').card + 1 := by exact_mod_cast he
      have hb0 : (0 : ℝ) ≤ b.card := Nat.cast_nonneg _
      have hA1 : 2.1 * varth d l g * b.card ≤ varth d l (finrank (ZMod p) L'') * b.card := by
        rw [← hpred]
        exact mul_le_mul_of_nonneg_right hanti hb0
      have hA2 : (252 : ℝ) ≤ varth d l g * b.card := by
        have hlpos : (0 : ℝ) < l := by linarith
        have : 0.18 / (l : ℝ) * (1400 * l) = 252 := by field_simp; norm_num
        calc (252 : ℝ) = 0.18 / (l : ℝ) * (1400 * l) := this.symm
          _ ≤ varth d l g * b.card := by
            apply mul_le_mul hθge hjR.le (by positivity) (varth_pos hl1 g).le
      linarith
  have hex : ∃! L', MemCond d l g b i y L' := ⟨L, hLcond, huniq⟩
  have hchoose : Classical.choose hex.exists = L := huniq _ (Classical.choose_spec hex.exists)
  unfold memA memAOf
  rw [dite_eq_left hex, hchoose]
  simp [hiL]

end Step5

section Step6

variable {l s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem window_disjoint (H : BDHyp p d l s) {g g' : ℕ} (hg : 1 ≤ g) (hg'd : g' < d) (hgg : g < g') :
    Disjoint (window p l s g) (window p l s g') := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hd3 : 3 ≤ d := by omega
  have hl1 : 1 ≤ l := by have := H.hl; omega
  have hs1 : 1 ≤ s := by have := H.hs4; omega
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl1
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs1
  have hpv : 1.1 ≤ p * varpi l s := by
    have h1 := H.hs5 hd3
    have hsq : √((s : ℝ) / l) * varpi l s = 606 * √π := by
      unfold varpi
      rw [Real.sqrt_div' _ hlR.le, Real.sqrt_mul Real.pi_pos.le]
      have : 0 < √(l : ℝ) := Real.sqrt_pos.2 hlR
      have : 0 < √(s : ℝ) := Real.sqrt_pos.2 hsR
      field_simp
      ring
    have hv : 0 ≤ varpi l s := by unfold varpi; positivity
    have hpi : 1 ≤ √π := by
      rw [Real.le_sqrt (by norm_num) Real.pi_pos.le]
      linarith [Real.pi_gt_three]
    calc (1.1 : ℝ) ≤ 606 * √π := by linarith
      _ = √((s : ℝ) / l) * varpi l s := hsq.symm
      _ ≤ p * varpi l s := mul_le_mul_of_nonneg_right h1 hv
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨hx1, -⟩ := hx
  obtain ⟨-, hx2⟩ := hx'
  have hpg : (0 : ℝ) < (p : ℝ) ^ g := by positivity
  have h1 : 1.1 / (p : ℝ) ^ g' ≤ 1.1 / (p : ℝ) ^ (g + 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_right₀ hp1 hgg)
  have h2 : 1.1 / (p : ℝ) ^ (g + 1) ≤ varpi l s / (p : ℝ) ^ g := by
    rw [pow_succ, div_le_div_iff₀ (by positivity) hpg]
    nlinarith
  linarith

theorem varth_le_004 (hd4 : d ≤ 4) (hl : 50 ≤ l) (g : ℕ) : varth d l g ≤ 0.04 := by
  unfold varth
  have hl' : (50 : ℝ) ≤ l := by exact_mod_cast hl
  have : (2.1 : ℝ) ^ (d - 1 - g) ≤ 2.1 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem rhoHat_le_restrict_finset' {d : ℕ} (b : Finset ι) (y : ι → Fin d → ZMod p) :
    rhoHat y ≤ rhoHat (fun x : b => y x) := by
  convert rhoHat_le_restrict (fun i => i ∈ b) y

abbrev BDWit (l : ℕ) (ι : Type*) := (Fin (2 * l) × ((Fin (2 * l) → ι) × (Fin (2 * l) → Bool))) ⊕
  (Finset ι × ι)

def bdW (l : ℕ) (win : Bool) : Bool → Finset ι → Finset (BDWit l ι)
  | false, b => (vsW l b).map ⟨Sum.inl, Sum.inl_injective⟩
  | true, b => if win then b.map ⟨fun i => Sum.inr (b, i), fun i i' h => by simpa using h⟩ else ∅

def bdIdx (l : ℕ) : BDWit l ι → ι := Sum.elim vsIdx fun x => x.2

noncomputable def bdA (d l gw : ℕ) : BDWit l ι → (ι → Fin d → ZMod p) → Finset (Fin d → ZMod p) :=
  Sum.elim vsA fun x y => memA d l gw x.1 x.2 y

set_option maxHeartbeats 1000000 in
theorem prop_blockd_core (H : BDHyp p d l s) (ν : (Fin d → ZMod p) → ℝ) (hν0 : ∀ a, 0 ≤ ν a)
    (hν1 : ∑ a, ν a = 1) (hνz : ν 0 = 0) {νmax : ℝ} (hνmax : ∀ a, ν a ≤ νmax)
    {ρ0 : ℝ} (hρ0 : (1 + 1 / 100) / (p : ℝ) ^ d ≤ ρ0) (win : Bool) (gw : ℕ) {κg : ℝ}
    (hκ0 : 0 ≤ κg) (hκ : ∀ L : Submodule (ZMod p) (Fin d → ZMod p), finrank (ZMod p) L = gw →
      subMeas ν L ≤ κg)
    (hwin : ∀ g, 1 ≤ g → g < d → ρ0 ∈ window p l s g → win = true ∧ g = gw) :
    pmeas (fun _ : ι => ν) (fun w => ρ0 ≤ rhoHat w) ≤
      (64 * (1 + 1 / 100) * √(π * l) * νmax / ((1 / 100) * ρ0 * √(s : ℝ)) +
        (if win then 1.1 * κg else 0)) ^ (Fintype.card ι - s) := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hl1 : 1 ≤ l := by have := H.hl; omega
  have hlR : (50 : ℝ) ≤ l := by exact_mod_cast H.hl
  have hs1 : 1 ≤ s := by have := H.hs4; omega
  set N : ℝ := (p : ℝ) ^ d with hN
  have hNpos : 0 < N := by positivity
  have hρ0pos : 0 < ρ0 := lt_of_lt_of_le (by positivity) hρ0
  have hνmax0 : 0 ≤ νmax := (hν0 0).trans (hνmax 0)
  set t := tBlock N (1 / 100) ρ0 s l with ht
  have htpos : 0 < t := by
    rw [ht]
    unfold tBlock
    have : 0 < √(π * l) := Real.sqrt_pos.2 (by positivity)
    have : 0 < √(s : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hs1)
    positivity
  set θw := varth d l gw with hθw
  have hθw : θw ≤ 0.04 := varth_le_004 H.hd4 H.hl gw
  have hθw0 : 0 ≤ θw := (varth_pos hl1 gw).le
  let B : (ι → Fin d → ZMod p) → Prop := fun y => (∀ i, y i ≠ 0) ∧ ρ0 ≤ rhoHat y
  have h1 : pmeas (fun _ : ι => ν) (fun w => ρ0 ≤ rhoHat w) ≤ pmeas (fun _ : ι => ν) B := by
    refine sum_le_sum fun y _ => ?_
    by_cases hy : ρ0 ≤ rhoHat y
    · rw [ite_eq_left hy]
      by_cases hz : ∀ i, y i ≠ 0
      · rw [ite_eq_left ⟨hz, hy⟩]
      · push Not at hz
        obtain ⟨i, hi⟩ := hz
        rw [prod_eq_zero (mem_univ i) (by show ν (y i) = 0; rw [hi, hνz])]
        split_ifs <;> simp
    · rw [ite_eq_right hy]
      split_ifs
      · exact prod_nonneg fun i _ => hν0 _
      · exact le_rfl
  refine h1.trans ?_
  let lam : Bool → ℕ → ℝ := fun τ j => if τ then (1 - θw) * (max j 1 : ℕ) else
    l * t * (2 * (max j 1 : ℕ) : ℝ) ^ (2 * l) / N
  let κ : Bool → ℝ := fun τ => if τ then κg else νmax
  set γ1 := 64 * (1 + 1 / 100) * √(π * l) * νmax / ((1 / 100) * ρ0 * √(s : ℝ)) with hγ1
  have hγ1' : 2 * N * νmax / t = γ1 := by
    rw [ht, hγ1]
    unfold tBlock
    have : 0 < √(π * l) := Real.sqrt_pos.2 (by positivity)
    have : 0 < √(s : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hs1)
    field_simp
    ring
  have hlam : ∀ τ j, 0 < lam τ j := by
    intro τ j
    have : (1 : ℝ) ≤ (max j 1 : ℕ) := by exact_mod_cast le_max_right j 1
    cases τ
    · show 0 < (l : ℝ) * t * (2 * (max j 1 : ℕ) : ℝ) ^ (2 * l) / N
      have : (0 : ℝ) < l := by exact_mod_cast hl1
      positivity
    · show 0 < (1 - θw) * ((max j 1 : ℕ) : ℝ)
      have : 0 < 1 - θw := by linarith
      positivity
  have hidx : ∀ (τ : Bool) (b : Finset ι) (ω : BDWit l ι), ω ∈ bdW l win τ b → bdIdx l ω ∈ b := by
    intro τ b ω hω
    cases τ
    · obtain ⟨ω', hω', rfl⟩ := mem_map.1 hω
      exact vsIdx_mem hω'
    · simp only [bdW] at hω
      split_ifs at hω
      · obtain ⟨i, hi, rfl⟩ := mem_map.1 hω
        exact hi
      · simp at hω
  have hloc : ∀ (τ : Bool) (b : Finset ι) (ω : BDWit l ι), ω ∈ bdW l win τ b →
      ∀ y y' : ι → Fin d → ZMod p,
      (∀ j ∈ b, j ≠ bdIdx l ω → y j = y' j) → bdA (p := p) d l gw ω y = bdA d l gw ω y' := by
    intro τ b ω hω y y' h
    cases τ
    · obtain ⟨ω', hω', rfl⟩ := mem_map.1 hω
      exact vsA_local hω' y y' h
    · simp only [bdW] at hω
      split_ifs at hω
      · obtain ⟨i, hi, rfl⟩ := mem_map.1 hω
        exact memA_local h
      · simp at hω
  have hκb : ∀ (τ : Bool) (b : Finset ι) (ω : BDWit l ι), ω ∈ bdW l win τ b → ∀ y,
      ∑ a ∈ bdA (p := p) d l gw ω y, ν a ≤ κ τ := by
    intro τ b ω hω y
    cases τ
    · obtain ⟨ω', hω', rfl⟩ := mem_map.1 hω
      show ∑ a ∈ vsA ω' y, ν a ≤ νmax
      rw [vsA, sum_singleton]
      exact hνmax _
    · simp only [bdW] at hω
      split_ifs at hω
      · obtain ⟨i, hi, rfl⟩ := mem_map.1 hω
        exact memA_sum_le ν hκ0 hκ b i y
      · simp at hω
  have hκ0' : ∀ τ, 0 ≤ κ τ := by
    intro τ
    cases τ
    · exact hνmax0
    · exact hκ0
  set M := γ1 + (if win then 1.1 * κg else 0) with hM
  have hMb : ∀ b : Finset ι, s < b.card →
      ∑ τ, κ τ * (bdW l win τ b).card / lam τ b.card ≤ M := by
    intro b hb
    have hb1 : 1 ≤ b.card := by omega
    have hmax : (max b.card 1 : ℕ) = b.card := max_eq_left hb1
    have hbR : (1 : ℝ) ≤ b.card := by exact_mod_cast hb1
    rw [Fintype.sum_bool]
    have hf : κ false * (bdW l win false b).card / lam false b.card ≤ γ1 := by
      show νmax * ((vsW l b).map ⟨Sum.inl, Sum.inl_injective⟩).card /
        ((l : ℝ) * t * (2 * (max b.card 1 : ℕ) : ℝ) ^ (2 * l) / N) ≤ γ1
      rw [card_map, hmax, ← hγ1']
      have hc := card_vsW_le l b
      have hc' : ((vsW l b).card : ℝ) ≤ 2 * l * (b.card : ℝ) ^ (2 * l) * 4 ^ l := by
        exact_mod_cast hc
      have hpow : (2 * (b.card : ℝ)) ^ (2 * l) = 4 ^ l * (b.card : ℝ) ^ (2 * l) := by
        rw [mul_pow, pow_mul]
        norm_num
      have hl0 : (0 : ℝ) < l := by exact_mod_cast hl1
      rw [hpow, div_le_div_iff₀ (by positivity) htpos]
      calc νmax * ((vsW l b).card : ℝ) * t
          ≤ νmax * (2 * l * (b.card : ℝ) ^ (2 * l) * 4 ^ l) * t := by gcongr
        _ = 2 * N * νmax * (l * t * (4 ^ l * (b.card : ℝ) ^ (2 * l)) / N) := by
            field_simp
    have htrue : κ true * (bdW l win true b).card / lam true b.card ≤
        (if win then 1.1 * κg else 0) := by
      show κg * (bdW l win true b).card / ((1 - θw) * ((max b.card 1 : ℕ) : ℝ)) ≤ _
      rw [hmax]
      cases win
      · have hW : bdW (ι := ι) l false true b = ∅ := by rw [bdW, ite_eq_right Bool.false_ne_true]
        rw [hW, card_empty, Nat.cast_zero, mul_zero, zero_div, ite_eq_right Bool.false_ne_true]
      · rw [bdW, ite_eq_left rfl, card_map]
        have h1θ : 0 < 1 - θw := by linarith
        rw [div_le_iff₀ (mul_pos h1θ (by linarith))]
        have hfac : 0 ≤ κg * b.card * (1.1 * (1 - θw) - 1) :=
          mul_nonneg (mul_nonneg hκ0 (by linarith)) (by linarith)
        have : κg * b.card ≤ 1.1 * κg * ((1 - θw) * b.card) := by nlinarith
        exact this
    linarith
  have hBw : ∀ y, B y → ∀ b : Finset ι, s < b.card → ∃ τ, lam τ b.card ≤
      ((bdW l win τ b).filter fun ω => y (bdIdx l ω) ∈ bdA (p := p) d l gw ω y).card := by
    intro y hy b hb
    have hb1 : 1 ≤ b.card := by omega
    have hmax : (max b.card 1 : ℕ) = b.card := max_eq_left hb1
    set u := fun x : b => y x with hu
    have hu0 : ∀ x, u x ≠ 0 := fun x => hy.1 x
    have hρu : ρ0 ≤ rhoHat u := hy.2.trans (rhoHat_le_restrict_finset' b y)
    have hjb : s ≤ Fintype.card {x // x ∈ b} := by rw [Fintype.card_coe]; omega
    have hcb : Fintype.card {x // x ∈ b} = b.card := Fintype.card_coe b
    have hvan : t * (2 * b.card : ℝ) ^ (2 * l) / N ≤ Rl' l u → ∃ τ, lam τ b.card ≤
        ((bdW l win τ b).filter fun ω => y (bdIdx l ω) ∈ bdA (p := p) d l gw ω y).card := by
      intro hR
      refine ⟨false, ?_⟩
      show (l : ℝ) * t * (2 * (max b.card 1 : ℕ) : ℝ) ^ (2 * l) / N ≤ _
      rw [hmax]
      have hcnt : (((bdW l win false b).filter fun ω => y (bdIdx l ω) ∈ bdA (p := p) d l gw ω y).card) =
          ((vsW l b).filter fun ω => y (vsIdx ω) ∈ vsA ω y).card := by
        simp only [bdW]
        rw [filter_map, card_map]
        rfl
      rw [hcnt]
      have h2 := card_valid_vsW_ge (G := Fin d → ZMod p) l b y
      have h2' : (l : ℝ) * (Rl' l u : ℝ) ≤
          (((vsW l b).filter fun ω => y (vsIdx ω) ∈ vsA ω y).card : ℝ) := by exact_mod_cast h2
      calc (l : ℝ) * t * (2 * (b.card : ℝ)) ^ (2 * l) / N
          = l * (t * (2 * (b.card : ℝ)) ^ (2 * l) / N) := by ring
        _ ≤ l * (Rl' l u : ℝ) := mul_le_mul_of_nonneg_left hR (by positivity)
        _ ≤ _ := h2'
    have hgle := gStar_le (d := d) (l := l) u
    rcases eq_or_lt_of_le hgle with hgd | hgd
    ·
      apply hvan
      have := step4_case1 H u hu0 hjb hρ0 hρu hgd
      rwa [hcb] at this
    by_cases hc2 : ρ0 ≤ varpi l s / (p : ℝ) ^ gStar d l u
    · apply hvan
      have := step4_case2 H u hjb hρ0pos hgd hc2
      rwa [hcb] at this
    by_cases hc3 : 1.1 / (p : ℝ) ^ gStar d l u ≤ ρ0
    · apply hvan
      have := step4_case3 H u hu0 hjb hρ0pos hρu hgd hc3
      rwa [hcb] at this
    push Not at hc2 hc3
    obtain ⟨L, hLdim, hLh, hg1, hgd'⟩ := gStar_basic H u hgd
    obtain ⟨hwin1, hwin2⟩ := hwin _ hg1 hgd ⟨hc2, hc3⟩
    refine ⟨true, ?_⟩
    show (1 - θw) * ((max b.card 1 : ℕ) : ℝ) ≤ _
    rw [hmax]
    subst hwin1
    have hcnt : ((b.filter fun i => y i ∈ L).card : ℝ) ≤
        (((bdW l true true b).filter fun ω => y (bdIdx l ω) ∈ bdA (p := p) d l gw ω y).card : ℝ) := by
      have : (b.filter fun i => y i ∈ L) ⊆ b.filter fun i => y i ∈ memA (p := p) d l gw b i y := by
        intro i hi
        rw [mem_filter] at hi ⊢
        refine ⟨hi.1, ?_⟩
        rw [← hwin2]
        exact step5 H b y hy.1 hb hLdim hLh hi.1 hi.2
      have h3 : (((bdW l true true b).filter fun ω => y (bdIdx l ω) ∈ bdA (p := p) d l gw ω y).card) =
          (b.filter fun i => y i ∈ memA (p := p) d l gw b i y).card := by
        simp only [bdW, ite_true]
        rw [filter_map, card_map]
        rfl
      rw [h3]
      exact_mod_cast card_le_card this
    have hsplit : ((b.filter fun i => y i ∈ L).card : ℝ) + outL L u = b.card := by
      rw [hu, outL_block]
      have := card_filter_add_card_filter_not (s := b) (fun i => y i ∈ L)
      exact_mod_cast this
    have hheavy := hLh.2.2
    rw [hLdim, hcb, hwin2] at hheavy
    have hθeq : varth d l gw = θw := rfl
    rw [hθeq] at hheavy
    nlinarith
  have hch := lem_chains (bdW l win) (bdIdx l) (bdA (p := p) d l gw) lam (fun _ : ι => ν)
    (fun _ a => hν0 a) (fun _ => hν1) hlam hidx hloc κ hκb hκ0' s (fun _ => M) hMb B hBw
  rw [prod_const, Nat.card_Ioc] at hch
  exact hch

theorem subMeas_le_one (ν : (Fin d → ZMod p) → ℝ) (hν0 : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1)
    (L : Submodule (ZMod p) (Fin d → ZMod p)) : subMeas ν L ≤ 1 := by
  classical
  unfold subMeas
  rw [← hν1]
  convert sum_le_sum_of_subset_of_nonneg (filter_subset (· ∈ L) univ) fun a _ _ => hν0 a

theorem prop_blockd (H : BDHyp p d l s) (ν : (Fin d → ZMod p) → ℝ) (hν0 : ∀ a, 0 ≤ ν a)
    (hν1 : ∑ a, ν a = 1) (hνz : ν 0 = 0) {νmax : ℝ} (hνmax : ∀ a, ν a ≤ νmax)
    {ρ0 : ℝ} (hρ0 : (1 + 1 / 100) / (p : ℝ) ^ d ≤ ρ0) :
    (∀ g g', 1 ≤ g → g < g' → g' < d → Disjoint (window p l s g) (window p l s g')) ∧
    (∀ g, 1 ≤ g → g < d → ρ0 ∈ window p l s g → ∀ κg : ℝ, 0 ≤ κg →
      (∀ L : Submodule (ZMod p) (Fin d → ZMod p), finrank (ZMod p) L = g → subMeas ν L ≤ κg) →
      pmeas (fun _ : ι => ν) (fun w => ρ0 ≤ rhoHat w) ≤
        (64 * (1 + 1 / 100) * √(π * l) * νmax / ((1 / 100) * ρ0 * √(s : ℝ)) + 1.1 * κg) ^
          (Fintype.card ι - s)) ∧
    ((∀ g, 1 ≤ g → g < d → ρ0 ∉ window p l s g) →
      pmeas (fun _ : ι => ν) (fun w => ρ0 ≤ rhoHat w) ≤
        (64 * (1 + 1 / 100) * √(π * l) * νmax / ((1 / 100) * ρ0 * √(s : ℝ))) ^
          (Fintype.card ι - s)) := by
  have hdisj : ∀ g g', 1 ≤ g → g < g' → g' < d → Disjoint (window p l s g) (window p l s g') :=
    fun g g' hg hgg hg'd => window_disjoint H hg hg'd hgg
  refine ⟨hdisj, ?_, ?_⟩
  · intro g hg hgd hρ κg hκ0 hκ
    have := prop_blockd_core (ι := ι) H ν hν0 hν1 hνz hνmax hρ0 true g hκ0 hκ (by
      intro g' hg' hg'd hρ'
      refine ⟨rfl, ?_⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Set.disjoint_left.1 (hdisj g' g hg' h hgd) hρ' hρ
      · exact Set.disjoint_left.1 (hdisj g g' hg h hg'd) hρ hρ')
    simpa using this
  · intro hno
    have := prop_blockd_core (ι := ι) H ν hν0 hν1 hνz hνmax hρ0 false 0 (κg := 1) zero_le_one
      (fun L _ => subMeas_le_one ν hν0 hν1 L) (fun g hg hgd hρ => absurd hρ (hno g hg hgd))
    simpa using this

end Step6

end DGS
