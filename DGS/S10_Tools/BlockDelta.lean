module

public import DGS.S10_Tools.Halasz
public import DGS.S10_Tools.FJLS

@[expose] public section

open Finset
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime]

noncomputable def tBlock (N δ ρ0 : ℝ) (s l : ℕ) : ℝ :=
  N * δ * ρ0 * √(s : ℝ) / (32 * (1 + δ) * √(π * l))

theorem Rl'_map {G H : Type*} [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : G →+ H) (hf : Function.Injective f) (l : ℕ)
    (w : ι → G) : Rl' l (fun j => f (w j)) = Rl' l w := by
  unfold Rl' vanSet
  have h : (univ.filter fun x : (Fin (2 * l) → ι) × (Fin (2 * l) → Bool) =>
      sgnSumIdx (fun j => f (w j)) x = 0) = univ.filter fun x => sgnSumIdx w x = 0 := by
    refine filter_congr fun x _ => ?_
    unfold sgnSumIdx
    rw [show ∑ r, sgnZ (x.2 r) • f (w (x.1 r)) = f (∑ r, sgnZ (x.2 r) • w (x.1 r)) by
      simp [map_sum, map_zsmul]]
    exact map_eq_zero_iff f hf
  rw [h]

theorem Rl'_toV1 {ι : Type*} [Fintype ι] [DecidableEq ι] (l : ℕ) (y : ι → ZMod p) :
    Rl' l (fun j => toV1 (y j)) = Rl' l y := by
  unfold Rl' vanSet
  have h : (univ.filter fun x : (Fin (2 * l) → ι) × (Fin (2 * l) → Bool) =>
      sgnSumIdx (fun j => toV1 (y j)) x = 0) = univ.filter fun x => sgnSumIdx y x = 0 := by
    refine filter_congr fun x _ => ?_
    unfold sgnSumIdx
    constructor
    · intro hx
      have := congrFun hx 0
      simpa [toV1, Finset.sum_apply] using this
    · intro hx
      funext i
      simpa [toV1, Finset.sum_apply] using hx
  rw [h]

theorem rhoHatP_le_restrict_finset {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Finset ι)
    (y : ι → ZMod p) : rhoHatP y ≤ rhoHatP (fun j : b => y j) := by
  convert rhoHatP_le_restrict (fun i => i ∈ b) y

theorem log_two_N_div_ge {N δ : ℝ} (hN : 3 ≤ N) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    5 / 6 ≤ Real.log (2 * N / δ) := by
  have h1 : 0 < 2 * N / δ := by positivity
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have h3 : (2 * N / δ)⁻¹ ≤ 1 / 6 := by
    rw [inv_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

theorem prop_blockdelta_a (hp2 : p ≠ 2) {g : ℕ} (hg : 1 ≤ g) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {l s : ℕ} (hl : 1 ≤ l) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hs1 : 16 * l * Real.log (2 * (p : ℝ) ^ g / δ) ≤ s)
    (hs2 : 32 * (1 + δ) / δ * √(π * l) * (p : ℝ) ^ g * (3 * l / 2 : ℝ) ^ (2 * l) ≤
      (s : ℝ) ^ (((l : ℝ) + 1) / 2))
    {ρ0 : ℝ} (hρ0 : (1 + δ) / (p : ℝ) ^ g ≤ ρ0)
    (w : ι → Fin g → ZMod p) (hj : s ≤ Fintype.card ι) (hw : ρ0 ≤ rhoHat w)
    (hsub : ∀ K : AddSubgroup (Fin g → ZMod p), K ≠ ⊤ →
      (0.18 : ℝ) * Fintype.card ι / l ≤ Nat.card {j // w j ∉ K}) :
    tBlock ((p : ℝ) ^ g) δ ρ0 s l * (2 * Fintype.card ι : ℝ) ^ (2 * l) / (p : ℝ) ^ g ≤
      Rl' l w := by
  set N : ℝ := (p : ℝ) ^ g with hNdef
  set j : ℝ := (Fintype.card ι : ℝ) with hjdef
  have hp3 : (3 : ℝ) ≤ p := by
    have h1 := (Fact.out : p.Prime).two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hN3 : 3 ≤ N := by
    rw [hNdef]
    calc (3 : ℝ) ≤ p := hp3
      _ = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ g := pow_le_pow_right₀ (by linarith) hg
  have hNpos : 0 < N := by linarith
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlog := log_two_N_div_ge hN3 hδ0 hδ1
  have hsR : (40 / 3 : ℝ) * l ≤ s := by nlinarith
  have hjs : (s : ℝ) ≤ j := by rw [hjdef]; exact_mod_cast hj
  have hs0 : (1 : ℝ) ≤ s := by nlinarith
  have hj1 : 1 ≤ Fintype.card ι := by
    have : (1 : ℝ) ≤ Fintype.card ι := by linarith
    exact_mod_cast this
  have hjpos : 0 < j := by linarith
  have hρ0pos : 0 < ρ0 := lt_of_lt_of_le (by positivity) hρ0
  have hNρ : 1 / N ≤ ρ0 / (1 + δ) := by
    rw [div_le_div_iff₀ hNpos (by linarith)]
    rw [div_le_iff₀ hNpos] at hρ0
    linarith
  have hexp : Real.exp (-j / (16 * l)) ≤ δ / (2 * N) := by
    have h1 : Real.log (2 * N / δ) ≤ j / (16 * l) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h2 : Real.exp (-j / (16 * l)) ≤ Real.exp (-Real.log (2 * N / δ)) := by
      apply Real.exp_le_exp.2
      rw [neg_div]
      linarith
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div] at h2
    exact h2
  have hH := prop_halasz hp2 w hl hj1 hsub
  rw [← hNdef, ← hjdef] at hH
  set r := rl l w with hr
  have h3 : δ * ρ0 / (2 * (1 + δ)) ≤ 8 * √(π * l / j) * r := by
    have e1 : 1 / N + δ / (2 * N) = (1 + δ / 2) * (1 / N) := by ring
    have e2 : (1 + δ / 2) * (1 / N) ≤ (1 + δ / 2) * (ρ0 / (1 + δ)) :=
      mul_le_mul_of_nonneg_left hNρ (by linarith)
    have e3 : ρ0 - (1 + δ / 2) * (ρ0 / (1 + δ)) = δ * ρ0 / (2 * (1 + δ)) := by
      field_simp
      ring
    linarith
  have hsq : √(π * l / j) = √(π * l) / √j := by
    rw [Real.sqrt_div' _ hjpos.le]
  have hπl : 0 < √(π * l) := Real.sqrt_pos.2 (by positivity)
  have hsj : 0 < √j := Real.sqrt_pos.2 hjpos
  have h4 : δ * ρ0 * √j / (16 * (1 + δ) * √(π * l)) ≤ r := by
    rw [hsq] at h3
    rw [div_le_iff₀ (by positivity)]
    have : δ * ρ0 / (2 * (1 + δ)) * √j ≤ 8 * (√(π * l) / √j) * r * √j :=
      mul_le_mul_of_nonneg_right h3 hsj.le
    have e : 8 * (√(π * l) / √j) * r * √j = 8 * √(π * l) * r := by
      field_simp
    rw [e] at this
    have e2 : δ * ρ0 * √j = 2 * (1 + δ) * (δ * ρ0 / (2 * (1 + δ)) * √j) := by
      field_simp
    rw [e2]
    nlinarith
  have h5 : j ^ (-(l : ℝ) / 2) * (3 * l / 2 : ℝ) ^ (2 * l) ≤
      δ * ρ0 * √j / (32 * (1 + δ) * √(π * l)) := by
    have hjl : (s : ℝ) ^ (((l : ℝ) + 1) / 2) ≤ j ^ (((l : ℝ) + 1) / 2) :=
      Real.rpow_le_rpow (by linarith) hjs (by positivity)
    have h6 : (3 * l / 2 : ℝ) ^ (2 * l) ≤
        j ^ (((l : ℝ) + 1) / 2) * δ / (32 * (1 + δ) * √(π * l) * N) := by
      rw [le_div_iff₀ (by positivity)]
      have : 32 * (1 + δ) / δ * √(π * l) * N * (3 * l / 2 : ℝ) ^ (2 * l) ≤
          j ^ (((l : ℝ) + 1) / 2) := hs2.trans hjl
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hδ0] at this
      linarith
    have hjj : j ^ (-(l : ℝ) / 2) * j ^ (((l : ℝ) + 1) / 2) = √j := by
      rw [← Real.rpow_add hjpos, Real.sqrt_eq_rpow]
      congr 1
      ring
    have hA : 0 ≤ j ^ (-(l : ℝ) / 2) := Real.rpow_nonneg hjpos.le _
    calc j ^ (-(l : ℝ) / 2) * (3 * l / 2 : ℝ) ^ (2 * l)
        ≤ j ^ (-(l : ℝ) / 2) * (j ^ (((l : ℝ) + 1) / 2) * δ / (32 * (1 + δ) * √(π * l) * N)) :=
          mul_le_mul_of_nonneg_left h6 hA
      _ = √j * δ / (32 * (1 + δ) * √(π * l) * N) := by
          rw [← hjj]
          ring
      _ ≤ δ * ρ0 * √j / (32 * (1 + δ) * √(π * l)) := by
          have h1N : 1 / N ≤ ρ0 := hNρ.trans (div_le_self hρ0pos.le (by linarith))
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : √j * δ * (32 * (1 + δ) * √(π * l)) * 1 ≤
              √j * δ * (32 * (1 + δ) * √(π * l)) * (ρ0 * N) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_iff₀ hNpos] at h1N
            linarith
          nlinarith
  have h3l : 3 * l ≤ 2 * Fintype.card ι := by
    have : (3 : ℝ) * l ≤ 2 * Fintype.card ι := by
      rw [← hjdef]
      linarith
    exact_mod_cast this
  have hdeg := degen_bound l hl w h3l
  rw [← hjdef, ← hr] at hdeg
  have hsqs : √(s : ℝ) ≤ √j := Real.sqrt_le_sqrt hjs
  have hpow0 : 0 < (2 * j) ^ (2 * l) := by positivity
  calc tBlock N δ ρ0 s l * (2 * j) ^ (2 * l) / N
      = δ * ρ0 * √(s : ℝ) / (32 * (1 + δ) * √(π * l)) * (2 * j) ^ (2 * l) := by
        rw [tBlock]
        field_simp
    _ ≤ δ * ρ0 * √j / (32 * (1 + δ) * √(π * l)) * (2 * j) ^ (2 * l) := by
        gcongr
    _ = (δ * ρ0 * √j / (16 * (1 + δ) * √(π * l)) -
          δ * ρ0 * √j / (32 * (1 + δ) * √(π * l))) * (2 * j) ^ (2 * l) := by
        congr 1
        field_simp
        ring
    _ ≤ (r - j ^ (-(l : ℝ) / 2) * (3 * l / 2 : ℝ) ^ (2 * l)) * (2 * j) ^ (2 * l) := by
        gcongr
    _ ≤ Rl' l w := hdeg

theorem toV1_not_mem_of_ne_top {K : AddSubgroup (Fin 1 → ZMod p)} (hK : K ≠ ⊤) {y : ZMod p}
    (hy : y ≠ 0) : toV1 y ∉ K := by
  intro hmem
  apply hK
  rw [eq_top_iff]
  intro v _
  have : v = (v 0 * y⁻¹).val • toV1 y := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp only [Pi.smul_apply, toV1, nsmul_eq_mul, ZMod.natCast_zmod_val]
    rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
  rw [this]
  exact AddSubgroup.nsmul_mem K hmem _

theorem prop_blockdelta_b (hp2 : p ≠ 2) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {l s : ℕ} (hl : 1 ≤ l) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hs1 : 16 * l * Real.log (2 * (p : ℝ) / δ) ≤ s)
    (hs2 : 32 * (1 + δ) / δ * √(π * l) * (p : ℝ) * (3 * l / 2 : ℝ) ^ (2 * l) ≤
      (s : ℝ) ^ (((l : ℝ) + 1) / 2))
    {ρ0 : ℝ} (hρ0 : (1 + δ) / (p : ℝ) ≤ ρ0)
    (ν : ZMod p → ℝ) (hν0 : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1) (hνz : ν 0 = 0) {νmax : ℝ}
    (hνmax : ∀ a, ν a ≤ νmax) :
    pmeas (fun _ : ι => ν) (fun y => ρ0 ≤ rhoG y) ≤ pmeas (fun _ : ι => ν) (fun y => ρ0 ≤ rhoHatP y) ∧
    pmeas (fun _ : ι => ν) (fun y => ρ0 ≤ rhoHatP y) ≤
      (64 * (1 + δ) * √(π * l) * νmax / (δ * ρ0 * √(s : ℝ))) ^ (Fintype.card ι - s) := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨pmeas_mono _ (fun _ a => hν0 a) fun y hy => hy.trans (rhoG_le_rhoHatP y), ?_⟩
  have hp3 : (3 : ℝ) ≤ p := by
    have h1 := (Fact.out : p.Prime).two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlog := log_two_N_div_ge hp3 hδ0 hδ1
  have hs0 : (1 : ℝ) ≤ s := by nlinarith
  have hρ0pos : 0 < ρ0 := lt_of_lt_of_le (by positivity) hρ0
  let B : (ι → ZMod p) → Prop := fun y => (∀ i, y i ≠ 0) ∧ ρ0 ≤ rhoHatP y
  have h1 : pmeas (fun _ : ι => ν) (fun y => ρ0 ≤ rhoHatP y) ≤ pmeas (fun _ : ι => ν) B := by
    refine sum_le_sum fun y _ => ?_
    by_cases hy : ρ0 ≤ rhoHatP y
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
  have ht : 0 < tBlock (p : ℝ) δ ρ0 s l := by
    unfold tBlock
    have : 0 < √(π * l) := Real.sqrt_pos.2 (by positivity)
    have : 0 < √(s : ℝ) := Real.sqrt_pos.2 (by linarith)
    positivity
  have h2 := cor_fjls ν hν0 hν1 hνmax hl s ht B ?_
  · rw [ZMod.card] at h2
    convert h2 using 2
    unfold tBlock
    have : 0 < √(π * l) := Real.sqrt_pos.2 (by positivity)
    have : 0 < √(s : ℝ) := Real.sqrt_pos.2 (by linarith)
    field_simp
    ring
  · intro y hy b hb
    rw [ZMod.card]
    set w : {x // x ∈ b} → Fin 1 → ZMod p := fun j => toV1 (y j) with hw
    have hρb : ρ0 ≤ rhoHat w := by
      rw [hw, rhoHat_toV1]
      exact hy.2.trans (rhoHatP_le_restrict_finset b y)
    have hsub : ∀ K : AddSubgroup (Fin 1 → ZMod p), K ≠ ⊤ →
        (0.18 : ℝ) * Fintype.card {x // x ∈ b} / l ≤ Nat.card {j // w j ∉ K} := by
      intro K hK
      have hall : ∀ j : {x // x ∈ b}, w j ∉ K := fun j => toV1_not_mem_of_ne_top hK (hy.1 j)
      have : Nat.card {j // w j ∉ K} = Fintype.card {x // x ∈ b} := by
        rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_eq_fintype_card]
      rw [this]
      have hb0 : (0 : ℝ) ≤ Fintype.card {x // x ∈ b} := Nat.cast_nonneg _
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hbs : s ≤ Fintype.card {x // x ∈ b} := by rw [Fintype.card_coe]; omega
    have ha := prop_blockdelta_a (g := 1) hp2 le_rfl hl hδ0 hδ1 (by simpa using hs1)
      (by simpa using hs2) (by simpa using hρ0) w hbs hρb hsub
    rw [hw, Rl'_toV1, Fintype.card_coe, pow_one] at ha
    exact ha

end DGS
