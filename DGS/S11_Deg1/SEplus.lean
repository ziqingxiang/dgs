module

public import DGS.S11_Deg1.GaussLaw
public import DGS.S10_Tools.BlockDelta
public import DGS.S10_Tools.SeqExp

@[expose] public section

open Finset Matrix
open scoped Real

namespace DGS

noncomputable def cSE : ℝ := 1 / 100000

theorem cSE_pos : 0 < cSE := by norm_num [cSE]

variable {p : ℕ} [Fact p.Prime]

section RhoStar

variable {n h : ℕ}

noncomputable def rhoStar (hh : 0 < h) (B : Fin h → Finset (Fin n)) (y : Fin n → ZMod p) : ℝ :=
  univ.inf' ⟨⟨0, hh⟩, mem_univ _⟩ fun i => rhoG (fun j : B i => y j)

theorem rhoStar_nonneg (hh : 0 < h) (B : Fin h → Finset (Fin n)) (y : Fin n → ZMod p) :
    0 ≤ rhoStar hh B y :=
  (le_inf'_iff _ _).2 fun _i _ => rhoG_nonneg _

theorem rhoStar_le_one (hh : 0 < h) (B : Fin h → Finset (Fin n)) (y : Fin n → ZMod p) :
    rhoStar hh B y ≤ 1 :=
  (inf'_le _ (mem_univ ⟨0, hh⟩)).trans (rhoG_le_one _)

theorem le_rhoStar_iff (hh : 0 < h) (B : Fin h → Finset (Fin n)) (y : Fin n → ZMod p) (t : ℝ) :
    t ≤ rhoStar hh B y ↔ ∀ i, t ≤ rhoG (fun j : B i => y j) := by
  unfold rhoStar
  exact (Finset.le_inf'_iff _ _).trans ⟨fun h i => h i (mem_univ i), fun h i _ => h i⟩

theorem eig_iff_sum (ω : Pairs n → Bool) (μ : ZMod p) (y : Fin n → ZMod p) :
    (seidelOf ω).map (Int.castRingHom (ZMod p)) *ᵥ y = μ • y ↔
      ∀ i, ∑ j, seidelOf ω i j • y j = (μ • y) i := by
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  simp [mulVec, dotProduct, zsmul_eq_mul]

theorem prob_eig_le_rhoStar {k : ℕ} (hh : 0 < h) (B : Fin h → Finset (Fin n))
    (hBk : ∀ i, (B i).card = k) (μ : ZMod p) (y : Fin n → ZMod p) :
    prob (fun ω : Pairs n → Bool => (seidelOf ω).map (Int.castRingHom (ZMod p)) *ᵥ y = μ • y) ≤
      rhoStar hh B y ^ (n - k) := by
  obtain ⟨i, -, hi⟩ := exists_mem_eq_inf' ⟨⟨0, hh⟩, mem_univ _⟩ (fun i => rhoG (fun j : B i => y j))
  have h1 := lem_seqexp_block y (μ • y) (B i)
  rw [hBk i] at h1
  unfold rhoStar
  rw [hi]
  exact le_trans (le_of_eq (prob_congr fun ω => eig_iff_sum ω μ y)) h1

end RhoStar

theorem level_bound {t ζ X : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hζ : 0 ≤ ζ) (_hX0 : 0 ≤ X) (hX1 : X ≤ 1)
    {N H n : ℕ} (hX : X ≤ (ζ / t) ^ H) (hN : N ≤ n) :
    (2 * t) ^ N * X ≤ 2 ^ n * ζ ^ (min N H) := by
  have h2 : (2 : ℝ) ^ N ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hN
  have htM : t ^ N ≤ t ^ (min N H) := pow_le_pow_of_le_one ht0.le ht1 (min_le_left _ _)
  rw [mul_pow]
  rcases le_or_gt ζ t with hζt | hζt
  ·
    have hq0 : 0 ≤ ζ / t := div_nonneg hζ ht0.le
    have hq1 : ζ / t ≤ 1 := (div_le_one ht0).2 hζt
    have hXM : X ≤ (ζ / t) ^ (min N H) :=
      hX.trans (pow_le_pow_of_le_one hq0 hq1 (min_le_right _ _))
    have e : t ^ N * (ζ / t) ^ (min N H) = t ^ (N - min N H) * ζ ^ (min N H) := by
      have h1 : t ^ N = t ^ (N - min N H) * t ^ (min N H) := by
        rw [← pow_add, Nat.sub_add_cancel (min_le_left _ _)]
      rw [h1, div_pow]
      have : t ^ (min N H) ≠ 0 := pow_ne_zero _ ht0.ne'
      field_simp
    have htN : t ^ (N - min N H) ≤ 1 := pow_le_one₀ ht0.le ht1
    calc 2 ^ N * t ^ N * X ≤ 2 ^ N * t ^ N * (ζ / t) ^ (min N H) :=
          mul_le_mul_of_nonneg_left hXM (by positivity)
      _ = 2 ^ N * (t ^ (N - min N H) * ζ ^ (min N H)) := by rw [mul_assoc, e]
      _ ≤ 2 ^ n * (1 * ζ ^ (min N H)) := by
          gcongr
      _ = 2 ^ n * ζ ^ (min N H) := by ring
  ·
    have htζ : t ^ (min N H) ≤ ζ ^ (min N H) := pow_le_pow_left₀ ht0.le hζt.le _
    calc 2 ^ N * t ^ N * X ≤ 2 ^ N * t ^ N * 1 := mul_le_mul_of_nonneg_left hX1 (by positivity)
      _ ≤ 2 ^ n * ζ ^ (min N H) := by
          rw [mul_one]
          exact mul_le_mul h2 (htM.trans htζ) (by positivity) (by positivity)

set_option maxHeartbeats 1000000 in
theorem prob_eigD_le (hp2 : p ≠ 2) {n l s k h A : ℕ} (hl : 1 ≤ l)
    (hs1 : 16 * l * Real.log (2 * (p : ℝ) / (1 / 100)) ≤ s)
    (hs2 : 32 * (1 + 1 / 100) / (1 / 100) * √(π * l) * (p : ℝ) * (3 * l / 2 : ℝ) ^ (2 * l) ≤
      (s : ℝ) ^ (((l : ℝ) + 1) / 2))
    (μ : ZMod p) (D : Finset (Fin n)) (hh : 0 < h) (B : Fin h → Finset (Fin n))
    (hBD : ∀ i, B i ⊆ D) (hBk : ∀ i, (B i).card = k)
    (hBdisj : Pairwise fun i i' => Disjoint (B i) (B i')) (hA : (p : ℝ) < 2 ^ A) :
    prob (fun ω : Pairs n → Bool => ∃ y : Fin n → ZMod p, (∀ j, y j ≠ 0 ↔ j ∈ D) ∧
        (seidelOf ω).map (Int.castRingHom (ZMod p)) *ᵥ y = μ • y ∧
        (normSqLift y : ℝ) ≤ cSE * n * (p : ℝ) ^ 2) ≤
      Real.exp ((n : ℝ) / 2) *
        (gaussMu0 p (1 / (2 * cSE * p ^ 2)) ^ D.card * ((1 + 1 / 100) / p) ^ (n - k) +
          A * (2 ^ n * (gaussMu0 p (1 / (2 * cSE * p ^ 2)) ^ D.card *
            (6464 * √(π * l) * (1.001 / gaussMu0 p (1 / (2 * cSE * p ^ 2))) / √(s : ℝ)) ^
              (min (n - k) (h * (k - s)))))) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set σ : ℝ := 1 / (2 * cSE * p ^ 2) with hσ
  have hσ0 : 0 < σ := by have := cSE_pos; positivity
  set μ0 := gaussMu0 p σ with hμ0
  have hμ0pos : 0 < μ0 := gaussMu0_pos hσ0
  obtain ⟨-, -, -, -, hcl⟩ := lem_gauss (p := p) (c := cSE) cSE_pos (by norm_num [cSE])
  set νmax : ℝ := 1.001 / μ0 with hνmax
  have hνle : ∀ a, gaussLaw p σ a ≤ νmax := gaussLaw_le hσ0 hcl
  set R2 : ℝ := cSE * n * (p : ℝ) ^ 2 with hR2
  have hσR : σ * R2 = (n : ℝ) / 2 := by
    rw [hσ, hR2]
    have := cSE_pos
    field_simp
  set ρs : (Fin n → ZMod p) → ℝ := rhoStar hh B with hρs
  set r0 : ℝ := (1 + 1 / 100) / p with hr0
  have hr0pos : 0 < r0 := by positivity
  set ζ : ℝ := 6464 * √(π * l) * νmax / √(s : ℝ) with hζ
  have hζ0 : 0 ≤ ζ := by positivity
  have hstep2 : prob (fun ω : Pairs n → Bool => ∃ y : Fin n → ZMod p, (∀ j, y j ≠ 0 ↔ j ∈ D) ∧
        (seidelOf ω).map (Int.castRingHom (ZMod p)) *ᵥ y = μ • y ∧ (normSqLift y : ℝ) ≤ R2) ≤
      ∑ y ∈ univ.filter (fun y : Fin n → ZMod p => ∀ j, y j ≠ 0 ↔ j ∈ D),
        (if (normSqLift y : ℝ) ≤ R2 then 1 else 0) * ρs y ^ (n - k) := by
    have hsub : ∀ ω : Pairs n → Bool, (∃ y : Fin n → ZMod p, (∀ j, y j ≠ 0 ↔ j ∈ D) ∧
        (seidelOf ω).map (Int.castRingHom (ZMod p)) *ᵥ y = μ • y ∧ (normSqLift y : ℝ) ≤ R2) →
        ∃ y ∈ univ.filter (fun y : Fin n → ZMod p => (∀ j, y j ≠ 0 ↔ j ∈ D) ∧
          (normSqLift y : ℝ) ≤ R2),
          (seidelOf ω).map (Int.castRingHom (ZMod p)) *ᵥ y = μ • y := by
      rintro ω ⟨y, hy1, hy2, hy3⟩
      exact ⟨y, mem_filter.2 ⟨mem_univ _, hy1, hy3⟩, hy2⟩
    refine (prob_mono hsub).trans ((prob_exists_le_sum _ _).trans ?_)
    rw [← filter_filter, sum_filter]
    refine sum_le_sum fun y _ => ?_
    split_ifs with hy
    · rw [one_mul]
      exact prob_eig_le_rhoStar hh B hBk μ y
    · exact le_of_eq (by ring)
  have hstep3 : ∑ y ∈ univ.filter (fun y : Fin n → ZMod p => ∀ j, y j ≠ 0 ↔ j ∈ D),
        (if (normSqLift y : ℝ) ≤ R2 then 1 else 0) * ρs y ^ (n - k) ≤
      Real.exp ((n : ℝ) / 2) * (μ0 ^ D.card * pexp (lawD p σ D) (fun y => ρs y ^ (n - k))) := by
    calc ∑ y ∈ univ.filter (fun y : Fin n → ZMod p => ∀ j, y j ≠ 0 ↔ j ∈ D),
          (if (normSqLift y : ℝ) ≤ R2 then 1 else 0) * ρs y ^ (n - k)
        ≤ ∑ y ∈ univ.filter (fun y : Fin n → ZMod p => ∀ j, y j ≠ 0 ↔ j ∈ D),
            Real.exp (σ * R2) * (Real.exp (-σ * (normSqLift y : ℝ)) * ρs y ^ (n - k)) := by
          refine sum_le_sum fun y _ => ?_
          rw [← mul_assoc, ← Real.exp_add]
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (rhoStar_nonneg hh B y) _)
          split_ifs with hy
          · apply Real.one_le_exp
            nlinarith
          · exact (Real.exp_pos _).le
      _ = Real.exp (σ * R2) * ∑ y ∈ univ.filter (fun y : Fin n → ZMod p => ∀ j, y j ≠ 0 ↔ j ∈ D),
            Real.exp (-σ * (normSqLift y : ℝ)) * ρs y ^ (n - k) := by rw [mul_sum]
      _ ≤ Real.exp (σ * R2) * (μ0 ^ D.card * pexp (lawD p σ D) (fun y => ρs y ^ (n - k))) := by
          have h3 := sum_exp_normSqLift_le (p := p) hσ0 D (fun y => ρs y ^ (n - k))
            (fun y => pow_nonneg (rhoStar_nonneg hh B y) _)
          rw [← hμ0] at h3
          have h4 : ∑ y ∈ univ.filter (fun y : Fin n → ZMod p => ∀ j, y j ≠ 0 ↔ j ∈ D),
              Real.exp (-σ * (normSqLift y : ℝ)) * ρs y ^ (n - k) ≤
              μ0 ^ D.card * pexp (lawD p σ D) (fun y => ρs y ^ (n - k)) := by
            convert h3 using 2
            ext y
            simp
          exact mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
      _ = _ := by rw [hσR]
  have hlev := pexp_pow_le_levels (lawD p σ D) (fun j a => lawD_nonneg hσ0 D j a)
    (fun j => sum_lawD hσ0 D j) ρs (fun y => rhoStar_nonneg hh B y) (fun y => rhoStar_le_one hh B y)
    hr0pos (n - k) A (by
      rw [hr0, ← mul_div_assoc, lt_div_iff₀ hp]
      have h2A : (0 : ℝ) < 2 ^ A := by positivity
      nlinarith)
  have hlevel : ∀ a ∈ range A, (2 * (2 ^ a * r0)) ^ (n - k) *
      pexp (lawD p σ D) (fun y => if 2 ^ a * r0 ≤ ρs y then 1 else 0) ≤
      2 ^ n * ζ ^ (min (n - k) (h * (k - s))) := by
    intro a _
    set t : ℝ := 2 ^ a * r0 with ht
    have ht0 : 0 < t := by positivity
    have hX0 : 0 ≤ pexp (lawD p σ D) (fun y => if t ≤ ρs y then 1 else 0) :=
      pexp_nonneg _ (fun j a => lawD_nonneg hσ0 D j a) fun y => by split_ifs <;> norm_num
    by_cases ht1 : t ≤ 1
    ·
      have hblock : ∀ i, pexp (fun j : B i => lawD p σ D j)
          (fun x => if t ≤ rhoG x then 1 else 0) ≤ min 1 ((ζ / t) ^ (k - s)) := by
        intro i
        have hlaw : (fun j : B i => lawD p σ D j) = fun _ => gaussLaw p σ :=
          funext fun j => lawD_of_mem (hBD i j.2)
        rw [hlaw, ← pmeas_eq_pexp]
        refine le_min (pmeas_le_one _ (fun _ a => gaussLaw_nonneg hσ0 a) (fun _ => sum_gaussLaw hσ0) _)
          ?_
        have hbd := prop_blockdelta_b (ι := B i) hp2 hl (by norm_num) (by norm_num) hs1 hs2
          (ρ0 := t) (by
            rw [ht, ← hr0]
            have : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
            nlinarith)
          (gaussLaw p σ) (gaussLaw_nonneg hσ0) (sum_gaussLaw hσ0) gaussLaw_zero hνle
        refine hbd.1.trans (hbd.2.trans (le_of_eq ?_))
        rw [Fintype.card_coe, hBk i, hζ]
        congr 1
        field_simp
        ring
      have hprod : pexp (lawD p σ D) (fun y => if t ≤ ρs y then 1 else 0) =
          ∏ i, pexp (fun j : B i => lawD p σ D j) (fun x => if t ≤ rhoG x then 1 else 0) := by
        rw [← pexp_blocks (lawD p σ D) (fun j => sum_lawD hσ0 D j) B hBdisj
          (fun i x => if t ≤ rhoG x then 1 else 0)]
        congr 1
        funext y
        rw [prod_boole]
        simp only [hρs, le_rhoStar_iff hh B y t, mem_univ, true_imp_iff]
      have hX1 : pexp (lawD p σ D) (fun y => if t ≤ ρs y then 1 else 0) ≤ 1 := by
        rw [hprod]
        exact prod_le_one₀ (fun i _ => pexp_nonneg (fun j : B i => lawD p σ D j)
          (fun j a => lawD_nonneg hσ0 D j a) (F := fun x => if t ≤ rhoG x then 1 else 0)
          fun x => by split_ifs <;> norm_num) fun i _ => (hblock i).trans (min_le_left _ _)
      have hX : pexp (lawD p σ D) (fun y => if t ≤ ρs y then 1 else 0) ≤ (ζ / t) ^ (h * (k - s)) := by
        rw [hprod, mul_comm, pow_mul]
        calc ∏ i, pexp (fun j : B i => lawD p σ D j) (fun x => if t ≤ rhoG x then 1 else 0)
            ≤ ∏ _i : Fin h, (ζ / t) ^ (k - s) :=
              prod_le_prod₀ (fun i _ => pexp_nonneg (fun j : B i => lawD p σ D j)
                (fun j a => lawD_nonneg hσ0 D j a) (F := fun x => if t ≤ rhoG x then 1 else 0)
                fun x => by split_ifs <;> norm_num) fun i _ => (hblock i).trans (min_le_right _ _)
          _ = ((ζ / t) ^ (k - s)) ^ h := by rw [prod_const, card_univ, Fintype.card_fin]
      exact level_bound ht0 ht1 hζ0 hX0 hX1 hX (Nat.sub_le n k)
    ·
      push Not at ht1
      have h0 : pexp (lawD p σ D) (fun y => if t ≤ ρs y then 1 else 0) = 0 := by
        rw [show (fun y => if t ≤ ρs y then (1 : ℝ) else 0) = fun _ => 0 from funext fun y => by
          rw [ite_eq_right (not_le.2 (lt_of_le_of_lt (rhoStar_le_one hh B y) ht1))]]
        unfold pexp
        simp
      rw [h0, mul_zero]
      positivity
  have hsum : ∑ a ∈ range A, (2 * (2 ^ a * r0)) ^ (n - k) *
      pexp (lawD p σ D) (fun y => if 2 ^ a * r0 ≤ ρs y then 1 else 0) ≤
      A * (2 ^ n * ζ ^ (min (n - k) (h * (k - s)))) := by
    refine (sum_le_sum hlevel).trans (le_of_eq ?_)
    rw [sum_const, card_range, nsmul_eq_mul]
  calc _ ≤ _ := hstep2
    _ ≤ _ := hstep3
    _ ≤ Real.exp ((n : ℝ) / 2) * (μ0 ^ D.card * (r0 ^ (n - k) +
          A * (2 ^ n * ζ ^ (min (n - k) (h * (k - s)))))) := by
        gcongr
        exact hlev.trans (add_le_add le_rfl hsum)
    _ = _ := by ring

end DGS
