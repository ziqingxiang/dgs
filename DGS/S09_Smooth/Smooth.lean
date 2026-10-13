module

public import DGS.S08_Two.TwoLarge
public import DGS.S07_Small.FirstMoment
public import DGS.S07_Small.Tight
public import DGS.S05_Local.ShortCol
public import DGS.S04_Reduction.LargeDegrees
public import DGS.S03_Prelim.SuppD
public import DGS.Main

@[expose] public section

open Matrix Polynomial Filter Topology Real

namespace DGS

theorem eventually_mul_log_pow_le_rpow (C : ℝ) (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, C * (log n) ^ k ≤ (n : ℝ) ^ c := by
  rcases le_or_gt C 0 with hC | hC
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 0 ≤ (log n) ^ k := pow_nonneg (Real.log_nonneg hn1) k
    have h2 : 0 ≤ (n : ℝ) ^ c := Real.rpow_nonneg (by linarith) c
    nlinarith
  · have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hc).comp_tendsto tendsto_natCast_atTop_atTop
    have h2 := h.def (show (0 : ℝ) < 1 / C by positivity)
    filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
    simp only [Function.comp_apply, Real.norm_eq_abs] at hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hlog : 0 ≤ log n := Real.log_nonneg hn1'
    rw [abs_of_nonneg (Real.rpow_nonneg hlog _), abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      Real.rpow_natCast] at hn
    calc C * log n ^ k ≤ C * (1 / C * (n : ℝ) ^ c) := by gcongr
      _ = (n : ℝ) ^ c := by field_simp

theorem eventually_L1 {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 3 * logb 2 n ≤ (n : ℝ) ^ δ / (log n) ^ 2 := by
  filter_upwards [eventually_mul_log_pow_le_rpow (3 / log 2) 3 hδ, eventually_ge_atTop 2] with n hn hn2
  have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hlog : 0 < log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  rw [le_div_iff₀ (by positivity), Real.logb]
  calc 3 * (log n / log 2) * log n ^ 2 = 3 / log 2 * log n ^ 3 := by ring
    _ ≤ _ := hn

theorem eventually_L2 {ε δ : ℝ} (hδ : 0 < δ) (hεδ : ε = 2 * δ) :
    ∀ᶠ n : ℕ in atTop, 3 * (n : ℝ) ^ (1 / 2 - ε) * logb 2 n ≤ (n : ℝ) ^ (1 / 2 - δ) / log n := by
  filter_upwards [eventually_mul_log_pow_le_rpow (3 / log 2) 2 hδ, eventually_ge_atTop 2] with n hn hn2
  have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have e : (n : ℝ) ^ (1 / 2 - δ) = (n : ℝ) ^ (1 / 2 - ε) * (n : ℝ) ^ δ := by
    rw [← Real.rpow_add hn0, hεδ]
    congr 1
    ring
  rw [le_div_iff₀ hlog, e, Real.logb]
  have hp : 0 < (n : ℝ) ^ (1 / 2 - ε) := Real.rpow_pos_of_pos hn0 _
  calc 3 * (n : ℝ) ^ (1 / 2 - ε) * (log n / log 2) * log n
      = (n : ℝ) ^ (1 / 2 - ε) * (3 / log 2 * log n ^ 2) := by ring
    _ ≤ (n : ℝ) ^ (1 / 2 - ε) * (n : ℝ) ^ δ := by gcongr

theorem tendsto_sq_mul_half_pow :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (n / 2)) atTop (𝓝 0) := by
  have hr : |(1 / 2 : ℝ)| < 1 := by norm_num
  have h2 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr
  have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr
  have h0 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 hr
  have hf : Tendsto (fun q : ℕ => 4 * ((q : ℝ) ^ 2 * (1 / 2 : ℝ) ^ q) + 4 * ((q : ℝ) ^ 1 * (1 / 2 : ℝ) ^ q) +
      (q : ℝ) ^ 0 * (1 / 2 : ℝ) ^ q) atTop (𝓝 0) := by
    simpa using ((h2.const_mul 4).add (h1.const_mul 4)).add h0
  have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun n hn => by omega⟩
  have hg := hf.comp hdiv
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hg
  simp only [Function.comp_apply]
  have hn : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    exact_mod_cast this
  have h0' : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (n / 2) := by positivity
  have hsq : (n : ℝ) ^ 2 ≤ (2 * ((n / 2 : ℕ) : ℝ) + 1) ^ 2 := by
    gcongr
  calc (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (n / 2)
      ≤ (2 * ((n / 2 : ℕ) : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (n / 2) := by gcongr
    _ = _ := by ring

def pairsT (B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (B + 1) ×ˢ Finset.Icc 1 B).filter fun x => x.1.Prime

theorem mem_pairsT {B : ℕ} {x : ℕ × ℕ} :
    x ∈ pairsT B ↔ x.1.Prime ∧ x.1 ≤ B ∧ 1 ≤ x.2 ∧ x.2 ≤ B := by
  simp only [pairsT, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨h4, by omega, h2, h3⟩
  · rintro ⟨h4, h1, h2, h3⟩
    exact ⟨⟨by omega, h2, h3⟩, h4⟩

variable {n : ℕ}

def EvX5a (B a : ℕ) (ω : Pairs n → Bool) : Prop :=
  ∃ x ∈ pairsT B, ∃ β : (ZMod x.1)[X], β.Monic ∧ Irreducible β ∧ β.natDegree = x.2 ∧
    β ^ a ∣ (modP x.1 (symOf 1 0 ω)).charpoly

def EvX5b (B h : ℕ) (ω : Pairs n → Bool) : Prop :=
  ∃ x ∈ pairsT B, ∃ hp : Fact x.1.Prime, @EventX x.1 hp x.2 h n (symOf 1 0 ω)

def EvX6 (ω : Pairs n → Bool) : Prop :=
  ¬ ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 8)) → ¬ (p : ℤ) ∣ 1 - 0 →
      ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) →
      ∀ g : (ZMod p)[X], g.Monic → g.natDegree = d →
      ∀ y : Fin n → ZMod p, y ≠ 0 → aeval (modP p (symOf 1 0 ω)) g *ᵥ y = 0 →
        (n : ℝ) / (4 * (d + 1)) < ((Finset.univ.filter fun i => y i ≠ 0).card : ℝ)

theorem prob_X1_le (hOT : ORourkeTouriStatement) {η : ℝ} (hη : 0 < η) : ∀ᶠ n : ℕ in atTop,
    prob (fun ω : Pairs n → Bool => ¬ Controllable (graphOf ω)) ≤ η := by
  have h2 : Tendsto (fun n : ℕ => prob (fun ω : Pairs n → Bool => ¬ Controllable (graphOf ω)))
      atTop (𝓝 0) := by
    have : (fun n : ℕ => prob (fun ω : Pairs n → Bool => ¬ Controllable (graphOf ω))) =
        fun n => 1 - probG n Controllable := by
      funext n
      rw [probG_eq_prob_graphOf, prob_compl]
    rw [this]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (thm_OT hOT)
  exact ((tendsto_order.1 h2).2 η hη).mono fun n h => h.le

theorem prob_X3_le (hTV : TaoVuStatement) {η : ℝ} (hη : 0 < η) : ∀ᶠ n : ℕ in atTop,
    prob (fun ω : Pairs n → Bool => ∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 * logb 2 n ≤ (d : ℝ) ∧
      E p d (graphOf ω)) ≤ η := by
  have h := thm_largedegrees hTV
  unfold Thm22 at h
  have h2 : Tendsto (fun n : ℕ => prob (fun ω : Pairs n → Bool => ∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧
      3 * logb 2 n ≤ (d : ℝ) ∧ E p d (graphOf ω))) atTop (𝓝 0) := by
    refine h.congr fun n => ?_
    rw [probG_eq_prob_graphOf]
  exact ((tendsto_order.1 h2).2 η hη).mono fun n h => h.le

theorem prob_X6_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, prob (fun ω : Pairs n → Bool => EvX6 ω) ≤ η := by
  have hexp : ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ) / 8) ≤ η := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (show (0 : ℝ) < 8 by norm_num))
    have h2 := (tendsto_order.1 this).2 η hη
    filter_upwards [h2] with n hn
    simp only [Function.comp] at hn
    rw [show -(n : ℝ) / 8 = -((n : ℝ) / 8) by ring]
    exact hn.le
  filter_upwards [lem_suppd 1 0, hexp] with n h1 h2
  exact h1.trans h2

theorem prob_X5a_le (B : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ a : ℕ, ∀ᶠ n : ℕ in atTop, prob (fun ω : Pairs n → Bool => EvX5a B a ω) ≤ η := by
  classical
  set N := (pairsT B).card with hN
  set η' := η / (N + 1) with hη'
  have hη'0 : 0 < η' := by positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (2 * (m : ℝ) + 1) / (2 : ℝ) ^ m * (B : ℝ) ^ B ≤ η' / 2 := by
    have h := (tendsto_two_mul_add_one_div_pow (p := 2) (by norm_num)).mul_const ((B : ℝ) ^ B)
    rw [zero_mul] at h
    obtain ⟨m, hm⟩ := ((tendsto_order.1 h).2 (η' / 2) (by positivity)).exists
    exact ⟨m, by exact_mod_cast hm.le⟩
  refine ⟨2 * m, ?_⟩
  have hpair : ∀ x ∈ pairsT B, ∀ᶠ n : ℕ in atTop, prob (fun ω : Pairs n → Bool =>
      ∃ β : (ZMod x.1)[X], β.Monic ∧ Irreducible β ∧ β.natDegree = x.2 ∧
        β ^ (2 * m) ∣ (modP x.1 (symOf 1 0 ω)).charpoly) ≤ η' := by
    intro x hx
    obtain ⟨hp, hpB, hd1, hdB⟩ := mem_pairsT.1 hx
    have : Fact x.1.Prime := ⟨hp⟩
    have h := prop_tight_a x.1 hd1 (2 * m) (show 0 < η' / 2 by positivity)
    filter_upwards [h] with n hn
    have e : prob (fun ω : Pairs n → Bool => ∃ β : (ZMod x.1)[X], β.Monic ∧ Irreducible β ∧
        β.natDegree = x.2 ∧ β ^ (2 * m) ∣ (modP x.1 (symOf 1 0 ω)).charpoly) =
        prob (fun ω : Pairs n → Bool => ∃ β ∈ irrSet x.1 x.2,
          β ^ (2 * m) ∣ (modP x.1 (symOf 1 0 ω)).charpoly) := by
      refine prob_congr fun ω => ?_
      constructor
      · rintro ⟨β, h1, h2, h3, h4⟩
        exact ⟨β, mem_irrSet_iff.2 ⟨h1, h2, h3⟩, h4⟩
      · rintro ⟨β, hβ, h4⟩
        obtain ⟨h1, h2, h3⟩ := mem_irrSet_iff.1 hβ
        exact ⟨β, h1, h2, h3, h4⟩
    rw [e]
    refine hn.trans ?_
    have hk : 2 * m / 2 = m := by omega
    rw [hk]
    have hπ : (piCount x.1 x.2 : ℝ) ≤ (B : ℝ) ^ B := by
      have h1 := piCount_le x.1 x.2
      have h2 : x.1 ^ x.2 ≤ B ^ B :=
        (Nat.pow_le_pow_left hpB _).trans (Nat.pow_le_pow_right (by omega) hdB)
      exact_mod_cast h1.trans h2
    have hpow : (2 : ℝ) ^ m ≤ (x.1 : ℝ) ^ (m * x.2) := by
      have h1 : (2 : ℝ) ≤ x.1 := by exact_mod_cast hp.two_le
      calc (2 : ℝ) ^ m ≤ (x.1 : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) h1 m
        _ ≤ (x.1 : ℝ) ^ (m * x.2) := pow_le_pow_right₀ (by linarith) (Nat.le_mul_of_pos_right m hd1)
    have h3 : (((2 * m : ℕ) : ℝ) + 1) * piCount x.1 x.2 * ((x.1 : ℝ) ^ (m * x.2))⁻¹ ≤ η' / 2 := by
      calc (((2 * m : ℕ) : ℝ) + 1) * piCount x.1 x.2 * ((x.1 : ℝ) ^ (m * x.2))⁻¹
          ≤ (2 * (m : ℝ) + 1) * (B : ℝ) ^ B * ((2 : ℝ) ^ m)⁻¹ := by
            push_cast
            gcongr
        _ = (2 * (m : ℝ) + 1) / (2 : ℝ) ^ m * (B : ℝ) ^ B := by ring
        _ ≤ η' / 2 := hm
    linarith
  rw [← Filter.eventually_all_finset] at hpair
  filter_upwards [hpair] with n hn
  have hle := prob_exists_le_sum (pairsT B) (fun (x : ℕ × ℕ) (ω : Pairs n → Bool) =>
    ∃ β : (ZMod x.1)[X], β.Monic ∧ Irreducible β ∧ β.natDegree = x.2 ∧
      β ^ (2 * m) ∣ (modP x.1 (symOf 1 0 ω)).charpoly)
  calc prob (fun ω : Pairs n → Bool => EvX5a B (2 * m) ω)
      ≤ ∑ x ∈ pairsT B, prob (fun ω : Pairs n → Bool => ∃ β : (ZMod x.1)[X], β.Monic ∧
          Irreducible β ∧ β.natDegree = x.2 ∧ β ^ (2 * m) ∣ (modP x.1 (symOf 1 0 ω)).charpoly) := hle
    _ ≤ ∑ _x ∈ pairsT B, η' := Finset.sum_le_sum hn
    _ = N * η' := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ η := by
        rw [hη', mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

theorem prob_X5b_le (B : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ h : ℕ, 1 ≤ h ∧ ∀ᶠ n : ℕ in atTop, prob (fun ω : Pairs n → Bool => EvX5b B h ω) ≤ η := by
  classical
  set N := (pairsT B).card with hN
  set η' := η / (N + 1) with hη'
  have hη'0 : 0 < η' := by positivity
  have hE : ∀ x ∈ pairsT B, ∀ᶠ E : ℕ in atTop, ∀ hp : Fact x.1.Prime, ∀ᶠ n : ℕ in atTop,
      prob (fun ω : Pairs n → Bool => @EventX x.1 hp x.2 E n (symOf 1 0 ω)) ≤ η' := by
    intro x hx
    obtain ⟨hp, -, hd1, -⟩ := mem_pairsT.1 hx
    have : Fact x.1.Prime := ⟨hp⟩
    obtain ⟨E0, hE0⟩ := prop_tight_b x.1 hd1 hη'0
    filter_upwards [eventually_ge_atTop E0] with E hE _
    exact hE0 E hE
  rw [← Filter.eventually_all_finset] at hE
  obtain ⟨h, hh⟩ := (hE.and (eventually_ge_atTop 1)).exists
  refine ⟨h, hh.2, ?_⟩
  have hn : ∀ x ∈ pairsT B, ∀ᶠ n : ℕ in atTop, prob (fun ω : Pairs n → Bool =>
      ∃ hp : Fact x.1.Prime, @EventX x.1 hp x.2 h n (symOf 1 0 ω)) ≤ η' := by
    intro x hx
    obtain ⟨hp, -, -, -⟩ := mem_pairsT.1 hx
    filter_upwards [hh.1 x hx ⟨hp⟩] with n hn
    refine le_trans (prob_mono fun ω h' => ?_) hn
    obtain ⟨_, h''⟩ := h'
    exact h''
  rw [← Filter.eventually_all_finset] at hn
  filter_upwards [hn] with n hn
  have hle := prob_exists_le_sum (pairsT B) (fun (x : ℕ × ℕ) (ω : Pairs n → Bool) =>
    ∃ hp : Fact x.1.Prime, @EventX x.1 hp x.2 h n (symOf 1 0 ω))
  calc prob (fun ω : Pairs n → Bool => EvX5b B h ω)
      ≤ ∑ x ∈ pairsT B, prob (fun ω : Pairs n → Bool =>
          ∃ hp : Fact x.1.Prime, @EventX x.1 hp x.2 h n (symOf 1 0 ω)) := hle
    _ ≤ ∑ _x ∈ pairsT B, η' := Finset.sum_le_sum hn
    _ = N * η' := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ η := by
        rw [hη', mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

def L0 (B h : ℕ) : ℕ := (B ^ (h - 1)) ^ B

def dstar (B a : ℕ) : ℕ := a * B * (B * B ^ B)

theorem smooth_incl (hn : 1 ≤ n) {ε δ : ℝ} (_hεδ : ε = 2 * δ) {q₀ d₀ B a h : ℕ}
    (hB : q₀ + d₀ + 2 ≤ B) (hd₀ : 2 ≤ d₀)
    (L1 : 3 * logb 2 n ≤ (n : ℝ) ^ δ / (log n) ^ 2)
    (L2 : 3 * (n : ℝ) ^ (1 / 2 - ε) * logb 2 n ≤ (n : ℝ) ^ (1 / 2 - δ) / log n)
    (L3 : (B : ℝ) ≤ exp ((n : ℝ) ^ ((1 : ℝ) / 8)))
    (L4 : (dstar B a : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4))
    (L5 : ((L0 B h ^ 2 : ℕ) : ℝ) < (n : ℝ) / (4 * (dstar B a + 1)))
    (ω : Pairs n → Bool)
    (hQ : ∃ Q ∈ QG (graphOf ω), ¬ IsPermMatrix Q ∧
      ∀ p : ℕ, p.Prime → p ∣ level Q → (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε)) :
    ¬ Controllable (graphOf ω) ∨
      ((∃ p d : ℕ, (p, d) ∈ Rn δ n ∧ p ≠ 2 ∧ q₀ < p ^ d ∧ IsLocalFailure p d (symOf 1 0 ω)) ∨
      ((∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 * logb 2 n ≤ (d : ℝ) ∧ E p d (graphOf ω)) ∨
      (E2 d₀ (symOf 1 0 ω) ∨ (EvX5a B a ω ∨ (EvX5b B h ω ∨ EvX6 ω))))) := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hX1, hX2, hX3, hX4, hX5a, hX5b, hX6⟩ := hcon
  obtain ⟨Q, hQG, hperm, hsmall⟩ := hQ
  set A := symOf 1 0 ω with hAdef
  have hA : A.IsSymm := symOf_isSymm ω
  have hadj : adj (graphOf ω) = A := adj_graphOf ω
  have hW : (walkMatrix A).det ≠ 0 := by
    have := not_not.1 hX1
    rw [Controllable, hadj] at this
    exact this
  have hQm : IsMateMatrix A Q := by
    have := isMateMatrix_of_mem_QG hQG
    rwa [hadj] at this
  have hℓ1 : level Q ≠ 1 := fun h1 => hperm ((thm_wangxu_perm_iff_level hQG).2 h1)
  have hℓ0 : level Q ≠ 0 := (level_pos Q).ne'
  have hF : ∀ p : ℕ, ∀ hp : Fact p.Prime, p ∣ level Q → ∀ β ∈ Fset A Q p,
      β.Monic ∧ Irreducible β ∧ (p, β.natDegree) ∈ pairsT B := by
    intro p hp hpℓ β hβ
    have hβf := (mem_Fset.1 hβ).1
    have hβm := monic_of_mem_factorsSet hβf
    have hβi := irreducible_of_mem_factorsSet hβf
    have hd1 : 1 ≤ β.natDegree := hβi.natDegree_pos
    suffices hpd : p ≤ B ∧ β.natDegree ≤ B from
      ⟨hβm, hβi, mem_pairsT.2 ⟨hp.out, hpd.1, hd1, hpd.2⟩⟩
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨by omega, ?_⟩
      by_contra hdeg
      push Not at hdeg
      exact prop_twolarge_mates hA hn hW hX4 hβm hβi (by omega) hQm hβ
    ·
      obtain ⟨U, hU, hUt, hUiso, hUe⟩ := levellocal_iii hA hn hW hQm hβ
      have hUd : Module.finrank (ZMod p) U = β.natDegree := by
        obtain ⟨β', hβ', hd'⟩ := exists_hasType (modP p A) U hU
        rw [hd', hasType_unique (modP p A) U hU hβ' hUt]
      have hLF : IsLocalFailure p β.natDegree A := ⟨U, hU, hUd, hUiso, hUe⟩
      have hd3 : (β.natDegree : ℝ) < 3 * logb 2 n := by
        by_contra h3
        push Not at h3
        exact hX3 ⟨p, β.natDegree, hp.out, hp2, h3, by rw [E, hadj]; exact hLF⟩
      have hpn := hsmall p hp.out hpℓ
      have hR : (p, β.natDegree) ∈ Rn δ n := by
        refine ⟨hp.out, hd1, hd3.le.trans L1, ?_⟩
        push_cast
        have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        calc (p : ℝ) * β.natDegree ≤ (n : ℝ) ^ (1 / 2 - ε) * (3 * logb 2 n) :=
              mul_le_mul hpn hd3.le (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          _ = 3 * (n : ℝ) ^ (1 / 2 - ε) * logb 2 n := by ring
          _ ≤ _ := L2
      have hpq : p ^ β.natDegree ≤ q₀ := by
        by_contra hq
        push Not at hq
        exact hX2 ⟨p, β.natDegree, hR, hp2, hq, hLF⟩
      have h1 : p ≤ p ^ β.natDegree := Nat.le_self_pow (by omega) p
      have h2 : β.natDegree < p ^ β.natDegree := Nat.lt_pow_self hp.out.one_lt
      omega
  have hpB : ∀ p : ℕ, p.Prime → p ∣ level Q → p ≤ B := by
    intro p hpP hpℓ
    have hp : Fact p.Prime := ⟨hpP⟩
    obtain ⟨β, hβ⟩ := (levellocal_i_a hA hn hW hQm).1 hpℓ
    exact (mem_pairsT.1 (hF p hp hpℓ β hβ).2.2).2.1
  have hV : ∀ p : ℕ, ∀ hp : Fact p.Prime, p ∣ level Q → (level Q).factorization p ≤ h - 1 := by
    intro p hp hpℓ
    refine levellocal_i_b hA hn hW hQm (h - 1) fun β hβ y hy => ?_
    obtain ⟨hβm, hβi, hT⟩ := hF p hp hpℓ β hβ
    by_contra hy'
    exact hX5b ⟨(p, β.natDegree), hT, hp, hW, β, mem_irrSet_iff.2 ⟨hβm, hβi, rfl⟩, y, hy, hy'⟩
  have hB1 : 1 ≤ B := by omega
  have hLev : level Q ≤ L0 B h := by
    have hfac := Nat.prod_factorization_pow_eq_self hℓ0
    have hsupp : ∀ p ∈ (level Q).factorization.support, p.Prime ∧ p ∣ level Q := by
      intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      exact ⟨hp.1, hp.2.1⟩
    have hcard : (level Q).factorization.support.card ≤ B := by
      have hsub : (level Q).factorization.support ⊆ Finset.Icc 1 B := by
        intro p hp
        obtain ⟨hpP, hpℓ⟩ := hsupp p hp
        exact Finset.mem_Icc.2 ⟨hpP.one_lt.le, hpB p hpP hpℓ⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    rw [← hfac, Finsupp.prod]
    calc ∏ p ∈ (level Q).factorization.support, p ^ (level Q).factorization p
        ≤ ∏ _p ∈ (level Q).factorization.support, B ^ (h - 1) := by
          refine Finset.prod_le_prod fun p hp => ?_
          obtain ⟨hpP, hpℓ⟩ := hsupp p hp
          have : Fact p.Prime := ⟨hpP⟩
          calc p ^ (level Q).factorization p ≤ B ^ (level Q).factorization p :=
                Nat.pow_le_pow_left (hpB p hpP hpℓ) _
            _ ≤ B ^ (h - 1) := Nat.pow_le_pow_right hB1 (hV p ⟨hpP⟩ hpℓ)
      _ = (B ^ (h - 1)) ^ (level Q).factorization.support.card := Finset.prod_const _
      _ ≤ (B ^ (h - 1)) ^ B := Nat.pow_le_pow_right (pow_pos hB1 _) hcard
  obtain ⟨p, hpP, hpℓ⟩ := Nat.exists_prime_and_dvd hℓ1
  have hp : Fact p.Prime := ⟨hpP⟩
  obtain ⟨j, hwt0, hwt, hg⟩ := lem_shortcol hn hW hQm hpℓ
  set g := ∏ β ∈ Fset A Q p, β ^ mult (redP p A.charpoly) β with hgdef
  set y := redVec p (levelCol Q j) with hydef
  have hφm : (redP p A.charpoly).Monic := (charpoly_monic A).map _
  have hmult : ∀ β ∈ Fset A Q p, mult (redP p A.charpoly) β < a := by
    intro β hβ
    obtain ⟨hβm, hβi, hT⟩ := hF p hp hpℓ β hβ
    by_contra hge
    push Not at hge
    apply hX5a
    refine ⟨(p, β.natDegree), hT, β, hβm, hβi, rfl, ?_⟩
    rw [charpoly_modP_eq]
    exact (pow_dvd_pow β hge).trans (pow_mult_dvd hφm (mem_Fset.1 hβ).1)
  have hFcard : (Fset A Q p).card ≤ B * B ^ B := by
    have hsub : Fset A Q p ⊆ (Finset.Icc 1 B).biUnion (fun d => irrSet p d) := by
      intro β hβ
      obtain ⟨hβm, hβi, hT⟩ := hF p hp hpℓ β hβ
      obtain ⟨-, -, hd1, hdB⟩ := mem_pairsT.1 hT
      exact Finset.mem_biUnion.2 ⟨β.natDegree, Finset.mem_Icc.2 ⟨hd1, hdB⟩,
        mem_irrSet_iff.2 ⟨hβm, hβi, rfl⟩⟩
    have hpB' := hpB p hpP hpℓ
    calc (Fset A Q p).card ≤ ((Finset.Icc 1 B).biUnion (fun d => irrSet p d)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ d ∈ Finset.Icc 1 B, (irrSet p d).card := Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ Finset.Icc 1 B, B ^ B := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hdB := (Finset.mem_Icc.1 hd).2
          exact (piCount_le p d).trans
            ((Nat.pow_le_pow_left hpB' _).trans (Nat.pow_le_pow_right hB1 hdB))
      _ = B * B ^ B := by rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]
  have hmon : ∀ β ∈ Fset A Q p, (β ^ mult (redP p A.charpoly) β).Monic :=
    fun β hβ => (monic_of_mem_factorsSet (mem_Fset.1 hβ).1).pow _
  have hgm : g.Monic := monic_prod_of_monic _ _ hmon
  have hgdeg : g.natDegree ≤ dstar B a := by
    rw [hgdef, natDegree_prod_of_monic _ _ hmon]
    calc ∑ β ∈ Fset A Q p, (β ^ mult (redP p A.charpoly) β).natDegree
        ≤ ∑ _β ∈ Fset A Q p, a * B := Finset.sum_le_sum fun β hβ => by
          rw [natDegree_pow]
          obtain ⟨-, -, hT⟩ := hF p hp hpℓ β hβ
          obtain ⟨-, -, -, hdB⟩ := mem_pairsT.1 hT
          exact Nat.mul_le_mul (hmult β hβ).le hdB
      _ = (Fset A Q p).card * (a * B) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (B * B ^ B) * (a * B) := Nat.mul_le_mul_right _ hFcard
      _ = dstar B a := by unfold dstar; ring
  have hy0 : y ≠ 0 := by
    intro h0
    rw [Finset.card_pos] at hwt0
    obtain ⟨i, hi⟩ := hwt0
    rw [Finset.mem_filter] at hi
    exact hi.2 (by rw [h0]; rfl)
  have hg1 : 1 ≤ g.natDegree := by
    by_contra h0
    push Not at h0
    have hg1 : g = 1 := hgm.natDegree_eq_zero.1 (by omega)
    apply hy0
    have := hg
    rw [hg1, map_one, one_mulVec] at this
    exact this
  have hconcl := not_not.1 hX6
  have hpe : (p : ℝ) ≤ exp ((n : ℝ) ^ ((1 : ℝ) / 8)) :=
    le_trans (by exact_mod_cast hpB p hpP hpℓ) L3
  have hp1 : ¬ (p : ℤ) ∣ 1 - 0 := by
    rw [sub_zero]
    intro h1
    exact hpP.not_dvd_one (by exact_mod_cast h1)
  have hgd : (g.natDegree : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) :=
    le_trans (by exact_mod_cast hgdeg) L4
  have hlow := hconcl p hpP hpe hp1 g.natDegree hg1 hgd g hgm rfl y hy0 hg
  have hup : ((Finset.univ.filter fun i => y i ≠ 0).card : ℝ) ≤ ((L0 B h ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hwt.trans (Nat.pow_le_pow_left hLev 2)
  have hden : (n : ℝ) / (4 * (dstar B a + 1)) ≤ (n : ℝ) / (4 * (g.natDegree + 1)) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity)
    have : (g.natDegree : ℝ) ≤ dstar B a := by exact_mod_cast hgdeg
    linarith
  linarith

theorem thm_smooth (hTV : TaoVuStatement) (hOT : ORourkeTouriStatement) : Thm23 := by
  intro ε hε0 hε1
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 4 := by linarith
  have hεδ : ε = 2 * δ := by ring
  rw [tendsto_order]
  refine ⟨fun b hb => Eventually.of_forall fun n => lt_of_lt_of_le hb (prob_nonneg _), fun b hb => ?_⟩
  set η := b / 16 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨q₀, hq₀⟩ := thm_firstmoment_tail hδ0 hδ1 hη0
  obtain ⟨C, hC⟩ := prop_twolarge
  obtain ⟨d₀, hd₀2, hd₀⟩ : ∃ d₀ : ℕ, 2 ≤ d₀ ∧ 4 * (1 / 2 : ℝ) ^ d₀ ≤ η := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 4
    rw [mul_zero] at h
    obtain ⟨d, hd⟩ := (((tendsto_order.1 h).2 η hη0).and (eventually_ge_atTop 2)).exists
    exact ⟨d, hd.2, hd.1.le⟩
  set B := q₀ + d₀ + 2 with hB
  obtain ⟨a, ha⟩ := prob_X5a_le B hη0
  obtain ⟨h, hh1, hh⟩ := prob_X5b_le B hη0
  have hCn : ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (n / 2) ≤ η := by
    have h1 := tendsto_sq_mul_half_pow.const_mul C
    rw [mul_zero] at h1
    filter_upwards [(tendsto_order.1 h1).2 η hη0] with n hn
    rw [mul_assoc]
    exact hn.le
  have hL3 : ∀ᶠ n : ℕ in atTop, (B : ℝ) ≤ exp ((n : ℝ) ^ ((1 : ℝ) / 8)) :=
    (tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      tendsto_natCast_atTop_atTop)).eventually_ge_atTop _
  have hL4 : ∀ᶠ n : ℕ in atTop, (dstar B a : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hL5 : ∀ᶠ n : ℕ in atTop, ((L0 B h ^ 2 : ℕ) : ℝ) < (n : ℝ) / (4 * (dstar B a + 1)) :=
    (tendsto_natCast_atTop_atTop.atTop_div_const (by positivity)).eventually_gt_atTop _
  filter_upwards [hq₀, ha, hh, prob_X1_le hOT hη0, prob_X3_le hTV hη0, prob_X6_le hη0, hCn,
    eventually_L1 hδ0, eventually_L2 hδ0 hεδ, hL3, hL4, hL5, eventually_ge_atTop 1] with
    n h2 h5a h5b h1 h3 h6 hCn' hL1 hL2 hL3' hL4' hL5' hn
  have h4 : prob (fun ω : Pairs n → Bool => E2 d₀ (symOf 1 0 ω)) ≤ 2 * η := by
    have := hC n hn d₀ hd₀2
    linarith
  rw [probG_eq_prob_graphOf]
  have hsub := smooth_incl hn hεδ (le_refl B) hd₀2 hL1 hL2 hL3' hL4' hL5'
  have hle := prob_mono hsub
  have o1 := prob_or_le (fun ω : Pairs n → Bool => ¬ Controllable (graphOf ω))
    (fun ω : Pairs n → Bool =>
      (∃ p d : ℕ, (p, d) ∈ Rn δ n ∧ p ≠ 2 ∧ q₀ < p ^ d ∧ IsLocalFailure p d (symOf 1 0 ω)) ∨
      ((∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 * logb 2 n ≤ (d : ℝ) ∧ E p d (graphOf ω)) ∨
      (E2 d₀ (symOf 1 0 ω) ∨ (EvX5a B a ω ∨ (EvX5b B h ω ∨ EvX6 ω)))))
  have o2 := prob_or_le
    (fun ω : Pairs n → Bool =>
      ∃ p d : ℕ, (p, d) ∈ Rn δ n ∧ p ≠ 2 ∧ q₀ < p ^ d ∧ IsLocalFailure p d (symOf 1 0 ω))
    (fun ω : Pairs n → Bool =>
      (∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 * logb 2 n ≤ (d : ℝ) ∧ E p d (graphOf ω)) ∨
      (E2 d₀ (symOf 1 0 ω) ∨ (EvX5a B a ω ∨ (EvX5b B h ω ∨ EvX6 ω))))
  have o3 := prob_or_le
    (fun ω : Pairs n → Bool => ∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 * logb 2 n ≤ (d : ℝ) ∧ E p d (graphOf ω))
    (fun ω : Pairs n → Bool => E2 d₀ (symOf 1 0 ω) ∨ (EvX5a B a ω ∨ (EvX5b B h ω ∨ EvX6 ω)))
  have o4 := prob_or_le (fun ω : Pairs n → Bool => E2 d₀ (symOf 1 0 ω))
    (fun ω : Pairs n → Bool => EvX5a B a ω ∨ (EvX5b B h ω ∨ EvX6 ω))
  have o5 := prob_or_le (fun ω : Pairs n → Bool => EvX5a B a ω)
    (fun ω : Pairs n → Bool => EvX5b B h ω ∨ EvX6 ω)
  have o6 := prob_or_le (fun ω : Pairs n → Bool => EvX5b B h ω) (fun ω : Pairs n → Bool => EvX6 ω)
  have hfin : prob (fun ω : Pairs n → Bool => ∃ Q ∈ QG (graphOf ω), ¬ IsPermMatrix Q ∧
      ∀ p : ℕ, p.Prime → p ∣ level Q → (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε)) ≤ 8 * η := by
    linarith
  linarith

end DGS
