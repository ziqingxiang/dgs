module

public import DGS.S07_Small.Frames
public import Mathlib.Analysis.PSeries

@[expose] public section

open Matrix Polynomial Filter Topology

namespace DGS

theorem lem_fourier_b_gen {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (p : ℕ) [Fact p.Prime] (E q m : ℕ) [NeZero q], q = p ^ E → 1 ≤ E → 1 ≤ m →
      (m : ℝ) ≤ (n : ℝ) ^ δ / Real.log n ^ 2 →
      ((q * m : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ) / Real.log n →
      ∀ Y : Matrix (Fin n) (Fin m) (ZMod q),
        IsRobust (sDelta δ n) (Y.map (ZMod.cast : ZMod q → ZMod p)) →
      ∀ Z : Matrix (Fin n) (Fin m) (ZMod q),
        prob (fun ω : Pairs n → Bool => modP q (symOf 1 0 ω) * Y = Z) ≤
          (1 + ε n) * (((q : ℝ) ^ (n * m))⁻¹ * (antisymm m q).card) := by
  obtain ⟨ε, hε, hev⟩ := lem_fourier_b hδ0 hδ1
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hev] with n hn
  intro p _ E q m _ hq hE hm hmδ hqm Y hY Z
  subst hq
  have h := hn p E m hE hm hmδ hqm Y hY Z
  convert h using 4
  push_cast
  rw [← pow_mul, mul_assoc]

def NoShort (δ : ℝ) (n : ℕ) (ω : Pairs n → Bool) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ g : (ZMod p)[X], g.Monic → (p, g.natDegree) ∈ Rn δ n →
    ∀ z : Fin n → ZMod p, 0 < wt z → wt z < sDelta δ n → aeval (modP p (symOf 1 0 ω)) g *ᵥ z ≠ 0

theorem prob_not_noShort {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∀ᶠ n : ℕ in atTop, prob (fun ω : Pairs n → Bool => ¬ NoShort δ n ω) ≤ Real.exp (-(n : ℝ) / 8) :=
  prop_shortany hδ0 hδ1

variable {p : ℕ} [hp : Fact p.Prime]

open Classical in
noncomputable def admFrames (p : ℕ) [Fact p.Prime] (δ : ℝ) (n d : ℕ) :
    Finset (Matrix (Fin n) (Fin d) (ZMod p)) :=
  Finset.univ.filter fun V => IsRobust (sDelta δ n) V ∧ Vᵀ * V = 0 ∧ Vᵀ *ᵥ (fun _ => 1) = 0

theorem pow_mulVec_mem_of_invariant {F : Type*} [Field F] {n : ℕ} {M : Matrix (Fin n) (Fin n) F}
    {U : Submodule F (Fin n → F)} (hU : IsInvariant M U) {u : Fin n → F} (hu : u ∈ U) (j : ℕ) :
    M ^ j *ᵥ u ∈ U := by
  induction j with
  | zero => simpa using hu
  | succ j ih => rw [pow_succ', ← mulVec_mulVec]; exact hU _ ih

theorem frames_count_ge {δ : ℝ} {n d : ℕ} (hd1 : 1 ≤ d) (hR : (p, d) ∈ Rn δ n)
    (ω : Pairs n → Bool) (hE : IsLocalFailure p d (symOf 1 0 ω)) (hN : NoShort δ n ω) :
    (p : ℝ) ^ d - 1 ≤ ∑ β ∈ irrSet p d,
      (((admFrames p δ n d).filter fun V => modP p (symOf 1 0 ω) * V = V * compMat β d).card : ℝ) := by
  classical
  set A := modP p (symOf 1 0 ω) with hA
  obtain ⟨U, hU, hUd, hiso, horth⟩ := hE
  obtain ⟨β, hβ, hUβ⟩ := exists_hasType A U hU
  have hβd : β.natDegree = d := by rw [← hUβ, hUd]
  have hβmem : β ∈ irrSet p d := mem_irrSet_iff.2 ⟨hβ.1, hβ.2.1, hβd⟩
  set Us := (Finset.univ.filter fun u : Fin n → ZMod p => u ∈ U).erase 0 with hUs
  have hUs_card : (Us.card : ℝ) = (p : ℝ) ^ d - 1 := by
    have h1 : (Finset.univ.filter fun u : Fin n → ZMod p => u ∈ U).card = p ^ d := by
      rw [← Fintype.card_subtype, Module.card_eq_pow_finrank (K := ZMod p) (V := U), ZMod.card,
        hUd]
    have h0 : (0 : Fin n → ZMod p) ∈ Finset.univ.filter fun u : Fin n → ZMod p => u ∈ U := by
      simp [U.zero_mem]
    have h2 := Finset.card_erase_add_one h0
    rw [h1] at h2
    have h3 : ((Us.card + 1 : ℕ) : ℝ) = ((p ^ d : ℕ) : ℝ) := by rw [hUs, h2]
    push_cast at h3
    linarith
  have hmaps : ∀ u ∈ Us, krylovN A u d ∈
      (admFrames p δ n d).filter fun V => A * V = V * compMat β d := by
    intro u hu
    rw [hUs, Finset.mem_erase, Finset.mem_filter] at hu
    obtain ⟨hu0, -, huU⟩ := hu
    have hβu : aeval A β *ᵥ u = 0 := hβ.2.2 u huU
    simp only [Finset.mem_filter, admFrames, Finset.mem_univ, true_and]
    refine ⟨⟨?_, ?_, ?_⟩, mul_krylovN A u hβ.1 hβd hβu⟩
    ·
      intro c hc
      have hz0 : krylovN A u d *ᵥ c ≠ 0 := fun h =>
        hc (krylovN_mulVec_eq_zero hu0 hβ.2.1 hβd hβu h)
      have hzU : krylovN A u d *ᵥ c ∈ U := krylovN_mulVec_mem hU.1 huU c
      have hβz : aeval A β *ᵥ (krylovN A u d *ᵥ c) = 0 := hβ.2.2 _ hzU
      by_contra hlt
      push Not at hlt
      have hwt : 0 < wt (krylovN A u d *ᵥ c) := by
        obtain ⟨i, hi⟩ : ∃ i, (krylovN A u d *ᵥ c) i ≠ 0 := by
          by_contra h; push Not at h; exact hz0 (funext h)
        exact Finset.card_pos.2 ⟨i, by simp [hi]⟩
      exact hN p hp.out β hβ.1 (by rw [hβd]; exact hR) _ hwt hlt hβz
    ·
      ext i j
      have hi := pow_mulVec_mem_of_invariant hU.1 huU i
      have hj := pow_mulVec_mem_of_invariant hU.1 huU j
      rw [Matrix.mul_apply, Matrix.zero_apply]
      exact hiso _ hi _ hj
    ·
      funext i
      have hi := pow_mulVec_mem_of_invariant hU.1 huU i
      have h := horth _ hi
      show ∑ k, (krylovN A u d)ᵀ i k * 1 = 0
      simp only [transpose_apply, mul_one]
      show ∑ k, (A ^ (i : ℕ) *ᵥ u) k = 0
      rw [← h]
      simp only [dotProduct, ones, one_mul]
      rfl
  have hinj : Set.InjOn (fun u => krylovN A u d) Us := by
    intro u _ u' _ h
    funext k
    have h0 := congrArg (fun V : Matrix (Fin n) (Fin d) (ZMod p) => V k ⟨0, hd1⟩) h
    simpa [krylovN] using h0
  calc (p : ℝ) ^ d - 1 = Us.card := hUs_card.symm
    _ = (Us.image fun u => krylovN A u d).card := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ ((admFrames p δ n d).filter fun V => A * V = V * compMat β d).card := by
        exact_mod_cast Finset.card_le_card (fun V hV => by
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hV
          exact hmaps u hu)
    _ ≤ ∑ β' ∈ irrSet p d,
          (((admFrames p δ n d).filter fun V => A * V = V * compMat β' d).card : ℝ) :=
        Finset.single_le_sum (f := fun β' =>
          (((admFrames p δ n d).filter fun V => A * V = V * compMat β' d).card : ℝ))
          (fun _ _ => by positivity) hβmem

noncomputable def cFirst (p d : ℕ) [Fact p.Prime] : ℝ :=
  (piCount p d : ℝ) / ((p : ℝ) ^ (2 * d) * ((p : ℝ) ^ d - 1))

theorem card_tor2_odd (hp2 : p ≠ 2) : Fintype.card (Tor2 p) = 1 := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 this with h1 | h1
    · exact hp.out.one_lt.ne' h1
    · exact hp2 h1
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, add_zero 0⟩, fun x => Subtype.ext ?_⟩
  have h := x.2
  rw [← two_mul] at h
  exact (mul_eq_zero.1 h).resolve_left h2ne

theorem card_antisymm_odd_one (hp2 : p ≠ 2) (m : ℕ) : (antisymm m p).card = p ^ (m * (m - 1) / 2) := by
  rw [card_antisymm, card_tor2_odd hp2, one_pow, mul_one]

theorem kd_eq (d : ℕ) : d * (d + 3) / 2 = d * (d - 1) / 2 + 2 * d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have h : d * (d + 3) = d * (d - 1) + 2 * (2 * d) := by
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [h, Nat.add_mul_div_left _ _ (by norm_num)]

theorem tendsto_eps_first {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (1 + |ε n|) * (1 + (2 : ℝ) ^ (-(n : ℝ) / 4)) - 1) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 + |ε n|) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hε.abs
  have h2 : Tendsto (fun n : ℕ => (2 : ℝ) ^ (-(n : ℝ) / 4)) atTop (𝓝 0) := by
    have hc : (2 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have hc0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
    have h3 := tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc
    refine h3.congr fun n => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  have h4 : Tendsto (fun n : ℕ => 1 + (2 : ℝ) ^ (-(n : ℝ) / 4)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add h2
  simpa using (h1.mul h4).sub_const 1

theorem eventually_kd_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∀ᶠ n : ℕ in atTop, 2 * ((n : ℝ) ^ δ) ^ 2 ≤ n / 4 := by
  filter_upwards [eventually_ge_atTop 64] with n hn
  have hN : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ n := by linarith
  have hNpos : (0 : ℝ) < n := by linarith
  have h1 : ((n : ℝ) ^ δ) ^ 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have h2 : (8 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have : (8 : ℝ) = (64 : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [show (64 : ℝ) = 8 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this]
    exact Real.rpow_le_rpow (by norm_num) hN (by norm_num)
  have h3 : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = n := by
    rw [← Real.rpow_add hNpos]; norm_num
  nlinarith

theorem prob_E_and_N_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop, ∀ (p d : ℕ) [Fact p.Prime],
      (p, d) ∈ Rn δ n → p ≠ 2 →
      prob (fun ω : Pairs n → Bool => IsLocalFailure p d (symOf 1 0 ω) ∧ NoShort δ n ω) ≤
        cFirst p d * (1 + ε n) := by
  obtain ⟨ε, hε, hev⟩ := lem_fourier_b_gen hδ0 (by linarith : δ < 1 / 2)
  refine ⟨fun n => (1 + |ε n|) * (1 + (2 : ℝ) ^ (-(n : ℝ) / 4)) - 1, tendsto_eps_first hε, ?_⟩
  have hLev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hev, eventually_kd_le hδ0 hδ1, hLev, eventually_ge_atTop 1]
    with n hn hkn hLn hn1
  intro p d hpf hR hp2
  classical
  obtain ⟨-, hd1, hdR, hpdR⟩ := hR
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hp3 : 3 ≤ p := by
    have := hpf.out.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p; simp_all
    · exact h
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < p := by linarith
  have hQ : (3 : ℝ) ≤ (p : ℝ) ^ d :=
    hpR.trans (by simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p) hd1)
  have hq1 : (0 : ℝ) < (p : ℝ) ^ d - 1 := by linarith
  set 𝒱 := admFrames p δ n d with h𝒱
  set Ir := irrSet p d with hIr
  set X : (Pairs n → Bool) → ℝ := fun ω => ((p : ℝ) ^ d - 1)⁻¹ * ∑ β ∈ Ir,
    (((𝒱.filter fun V => modP p (symOf 1 0 ω) * V = V * compMat β d).card : ℕ) : ℝ) with hX
  have hind : ∀ ω : Pairs n → Bool,
      (if IsLocalFailure p d (symOf 1 0 ω) ∧ NoShort δ n ω then (1 : ℝ) else 0) ≤ X ω := by
    intro ω
    split_ifs with h
    · rw [hX, le_inv_mul_iff₀ hq1, mul_one]
      exact frames_count_ge hd1 ⟨hpf.out, hd1, hdR, hpdR⟩ ω h.1 h.2
    · exact mul_nonneg (inv_nonneg.2 hq1.le) (Finset.sum_nonneg fun _ _ => by positivity)
  set b : ℝ := (1 + |ε n|) * (((p : ℝ) ^ (n * d))⁻¹ * (p : ℝ) ^ (d * (d - 1) / 2)) with hb
  have hsingle : ∀ β ∈ Ir, ∀ V ∈ 𝒱,
      prob (fun ω : Pairs n → Bool => modP p (symOf 1 0 ω) * V = V * compMat β d) ≤ b := by
    intro β _ V hV
    simp only [h𝒱, admFrames, Finset.mem_filter, Finset.mem_univ, true_and] at hV
    have hrob : IsRobust (sDelta δ n) (V.map (ZMod.cast : ZMod p → ZMod p)) := by
      have : V.map (ZMod.cast : ZMod p → ZMod p) = V := by
        ext i j; exact ZMod.cast_id p (V i j)
      rw [this]; exact hV.1
    have h := hn p 1 p d (pow_one p).symm le_rfl hd1 hdR hpdR V hrob (V * compMat β d)
    rw [card_antisymm_odd_one hp2] at h
    push_cast at h
    refine h.trans ?_
    rw [hb]
    gcongr
    exact le_abs_self _
  have hexp : prob (fun ω : Pairs n → Bool => IsLocalFailure p d (symOf 1 0 ω) ∧ NoShort δ n ω) ≤
      ((p : ℝ) ^ d - 1)⁻¹ * ∑ β ∈ Ir, ∑ V ∈ 𝒱,
        prob (fun ω : Pairs n → Bool => modP p (symOf 1 0 ω) * V = V * compMat β d) := by
    rw [← expect_indicator]
    refine (expect_mono hind).trans (le_of_eq ?_)
    rw [hX, expect_const_mul, expect_sum]
    congr 1
    refine Finset.sum_congr rfl fun β _ => ?_
    have h1 : ∀ ω : Pairs n → Bool,
        (((𝒱.filter fun V => modP p (symOf 1 0 ω) * V = V * compMat β d).card : ℕ) : ℝ) =
          ∑ V ∈ 𝒱, (if modP p (symOf 1 0 ω) * V = V * compMat β d then (1 : ℝ) else 0) := by
      intro ω; rw [Finset.card_filter]; push_cast; rfl
    simp_rw [h1]
    rw [expect_sum]
    exact Finset.sum_congr rfl fun V _ => expect_indicator _
  have hcount : (𝒱.card : ℝ) ≤ (p : ℝ) ^ (n * d) / (p : ℝ) ^ (d * (d + 3) / 2) +
      (p : ℝ) ^ (n * d) * ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
    have h1 := lem_gram_b_count (r := d) hp2 n
    have h2 : 𝒱.card ≤ (Finset.univ.filter fun V : Matrix (Fin n) (Fin d) (ZMod p) =>
        Vᵀ * V = 0 ∧ Vᵀ *ᵥ (fun _ => 1) = 0).card :=
      Finset.card_le_card fun V hV => by
        simp only [h𝒱, admFrames, Finset.mem_filter, Finset.mem_univ, true_and] at hV ⊢
        exact hV.2
    have h3 := (abs_le.1 h1).2
    have h4 : (𝒱.card : ℝ) ≤ ((Finset.univ.filter fun V : Matrix (Fin n) (Fin d) (ZMod p) =>
        Vᵀ * V = 0 ∧ Vᵀ *ᵥ (fun _ => 1) = 0).card : ℝ) := by exact_mod_cast h2
    linarith
  have hkd : (d * (d + 3) / 2 : ℕ) ≤ (n : ℝ) / 4 := by
    have h1 : (d : ℝ) ≤ (n : ℝ) ^ δ :=
      hdR.trans (div_le_self (by positivity) (by nlinarith))
    have h2 : ((d * (d + 3) / 2 : ℕ) : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by
      have h3 : d * (d + 3) / 2 ≤ 2 * d ^ 2 := by
        have : d * (d + 3) ≤ 4 * d ^ 2 := by nlinarith
        omega
      exact_mod_cast h3
    have h4 : (d : ℝ) ^ 2 ≤ ((n : ℝ) ^ δ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    linarith
  have hsmall : (p : ℝ) ^ (d * (d + 3) / 2) * ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ n ≤
      (2 : ℝ) ^ (-(n : ℝ) / 4) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 : ℝ))), ← Real.rpow_mul hp0.le,
      ← Real.rpow_natCast (p : ℝ) (d * (d + 3) / 2), ← Real.rpow_add hp0]
    calc (p : ℝ) ^ (((d * (d + 3) / 2 : ℕ) : ℝ) + -(1 / 2 : ℝ) * n) ≤ (p : ℝ) ^ (-(n : ℝ) / 4) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ (2 : ℝ) ^ (-(n : ℝ) / 4) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hsum : ∑ β ∈ Ir, ∑ V ∈ 𝒱,
      prob (fun ω : Pairs n → Bool => modP p (symOf 1 0 ω) * V = V * compMat β d) ≤
      (piCount p d : ℝ) * (𝒱.card * b) := by
    calc ∑ β ∈ Ir, ∑ V ∈ 𝒱,
          prob (fun ω : Pairs n → Bool => modP p (symOf 1 0 ω) * V = V * compMat β d)
        ≤ ∑ _β ∈ Ir, ∑ _V ∈ 𝒱, b := Finset.sum_le_sum fun β hβ => Finset.sum_le_sum fun V hV =>
          hsingle β hβ V hV
      _ = (piCount p d : ℝ) * (𝒱.card * b) := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, piCount, hIr]
  have hPpos : (0 : ℝ) < (p : ℝ) ^ (n * d) := by positivity
  have hK : (p : ℝ) ^ (d * (d + 3) / 2) = (p : ℝ) ^ (d * (d - 1) / 2) * (p : ℝ) ^ (2 * d) := by
    rw [kd_eq, pow_add]
  have hDpos : (0 : ℝ) < (p : ℝ) ^ (d * (d - 1) / 2) := by positivity
  have h2dpos : (0 : ℝ) < (p : ℝ) ^ (2 * d) := by positivity
  calc prob (fun ω : Pairs n → Bool => IsLocalFailure p d (symOf 1 0 ω) ∧ NoShort δ n ω)
      ≤ ((p : ℝ) ^ d - 1)⁻¹ * ((piCount p d : ℝ) * (𝒱.card * b)) :=
        hexp.trans (mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hq1.le))
    _ ≤ ((p : ℝ) ^ d - 1)⁻¹ * ((piCount p d : ℝ) *
          (((p : ℝ) ^ (n * d) / (p : ℝ) ^ (d * (d + 3) / 2) +
            (p : ℝ) ^ (n * d) * ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ n) * b)) := by
        gcongr
    _ = cFirst p d * ((1 + |ε n|) * (1 + (p : ℝ) ^ (d * (d + 3) / 2) *
          ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ n)) := by
        rw [hb, cFirst, hK]
        field_simp
    _ ≤ cFirst p d * (1 + ((1 + |ε n|) * (1 + (2 : ℝ) ^ (-(n : ℝ) / 4)) - 1)) := by
        have hc0 : 0 ≤ cFirst p d := by
          rw [cFirst]; exact div_nonneg (Nat.cast_nonneg _) (by positivity)
        rw [add_sub_cancel]
        gcongr

theorem thm_firstmoment {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop, ∀ (p d : ℕ) [Fact p.Prime],
      (p, d) ∈ Rn δ n → p ≠ 2 →
      prob (fun ω : Pairs n → Bool => IsLocalFailure p d (symOf 1 0 ω)) ≤
        cFirst p d * (1 + ε n) + Real.exp (-(n : ℝ) / 8) := by
  obtain ⟨ε, hε, hev⟩ := prob_E_and_N_le hδ0 hδ1
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hev, prob_not_noShort hδ0 hδ1] with n hn hN
  intro p d _ hR hp2
  calc prob (fun ω : Pairs n → Bool => IsLocalFailure p d (symOf 1 0 ω))
      ≤ prob (fun ω : Pairs n → Bool =>
          (IsLocalFailure p d (symOf 1 0 ω) ∧ NoShort δ n ω) ∨ ¬ NoShort δ n ω) :=
        prob_mono fun ω h => by
          by_cases hN' : NoShort δ n ω
          · exact Or.inl ⟨h, hN'⟩
          · exact Or.inr hN'
    _ ≤ _ := (prob_or_le _ _).trans (add_le_add (hn p d hR hp2) hN)

theorem eventually_mem_Rn {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) {p d : ℕ} (hp : p.Prime)
    (hd : 1 ≤ d) : ∀ᶠ n : ℕ in atTop, (p, d) ∈ Rn δ n := by
  have h1 := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) hδ0).bound
    (show (0 : ℝ) < 1 / ((d : ℝ) + 1) by positivity))
  have h2 := ((isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 - δ by linarith)).bound
    (show (0 : ℝ) < 1 / (((p * d : ℕ) : ℝ) + 1) by positivity))
  have h1' := tendsto_natCast_atTop_atTop.eventually h1
  have h2' := tendsto_natCast_atTop_atTop.eventually h2
  have hLev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [h1', h2', hLev, eventually_ge_atTop 1] with n hn1 hn2 hL hn
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log n := by linarith
  have hA : 0 ≤ (n : ℝ) ^ δ := by positivity
  have hB : 0 ≤ (n : ℝ) ^ (1 / 2 - δ) := by positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 _), Real.norm_of_nonneg hA,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hn1
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hB] at hn2
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨hp, hd, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have h3 : (d : ℝ) * Real.log n ^ 2 ≤ ((d : ℝ) + 1) * Real.log n ^ 2 := by nlinarith
    have h4 : ((d : ℝ) + 1) * Real.log n ^ 2 ≤ (n : ℝ) ^ δ := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at hn1
      linarith
    linarith
  · rw [le_div_iff₀ (by positivity)]
    have h3 : ((p * d : ℕ) : ℝ) * Real.log n ≤ (((p * d : ℕ) : ℝ) + 1) * Real.log n := by nlinarith
    have h4 : (((p * d : ℕ) : ℝ) + 1) * Real.log n ≤ (n : ℝ) ^ (1 / 2 - δ) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at hn2
      linarith
    linarith

theorem thm_firstmoment_limsup {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (p d : ℕ) [hpf : Fact p.Prime]
    (hp2 : p ≠ 2) (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, prob (fun ω : Pairs n → Bool => IsLocalFailure p d (symOf 1 0 ω)) ≤
      cFirst p d + η := by
  obtain ⟨ε, hε, hev⟩ := thm_firstmoment hδ0 hδ1
  have hc0 : 0 ≤ cFirst p d := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpf.out.one_lt
    have : (1 : ℝ) < (p : ℝ) ^ d := one_lt_pow₀ hp1 (by omega)
    rw [cFirst]; exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have h1 : Tendsto (fun n : ℕ => cFirst p d * ε n + Real.exp (-(n : ℝ) / 8)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) / 8)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_div_const (show (0 : ℝ) < 8 by norm_num))
      refine this.congr fun n => ?_
      simp only [Function.comp]; ring_nf
    simpa using (hε.const_mul (cFirst p d)).add h2
  filter_upwards [hev, eventually_mem_Rn hδ0 (by linarith) hpf.out hd,
    (tendsto_order.1 h1).2 η hη] with n hn hR hsmall
  have := hn p d hR hp2
  nlinarith

theorem cFirst_le {p d : ℕ} [hpf : Fact p.Prime] (hd : 1 ≤ d) :
    cFirst p d ≤ 2 / (((p ^ d : ℕ) : ℝ)) ^ 2 := by
  have hp1 : (2 : ℝ) ≤ p := by exact_mod_cast hpf.out.two_le
  have hq : (2 : ℝ) ≤ (p : ℝ) ^ d :=
    hp1.trans (by simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p) hd)
  have hπ : (piCount p d : ℝ) ≤ (p : ℝ) ^ d := by exact_mod_cast piCount_le p d
  rw [cFirst, pow_mul']
  push_cast
  set Q := (p : ℝ) ^ d with hQdef
  have hpos1 : 0 < Q ^ 2 * (Q - 1) := mul_pos (by positivity) (by linarith)
  rw [div_le_div_iff₀ hpos1 (by positivity)]
  have h1 := mul_le_mul_of_nonneg_right hπ (sq_nonneg Q)
  have h2 := mul_le_mul_of_nonneg_left hq (sq_nonneg Q)
  nlinarith

theorem thm_firstmoment_tail {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) {η : ℝ} (hη : 0 < η) :
    ∃ q0 : ℕ, ∀ᶠ n : ℕ in atTop, prob (fun ω : Pairs n → Bool => ∃ p d : ℕ,
      (p, d) ∈ Rn δ n ∧ p ≠ 2 ∧ q0 < p ^ d ∧ IsLocalFailure p d (symOf 1 0 ω)) ≤ η := by
  classical
  obtain ⟨ε, hε, hev⟩ := prob_E_and_N_le hδ0 hδ1
  obtain ⟨q0, hq0⟩ : ∃ q0 : ℕ, 8 / ((q0 : ℝ) + 1) ≤ η / 2 := by
    obtain ⟨k, hk⟩ := exists_nat_gt (16 / η)
    refine ⟨k, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    have : 16 < η * k := by rwa [div_lt_iff₀ hη, mul_comm] at hk
    nlinarith
  refine ⟨q0, ?_⟩
  have hexp : ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ) / 8) ≤ η / 2 := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (show (0 : ℝ) < 8 by norm_num))
    have h2 := (tendsto_order.1 this).2 (η / 2) (by linarith)
    filter_upwards [h2] with n hn
    simp only [Function.comp] at hn
    rw [show -(n : ℝ) / 8 = -((n : ℝ) / 8) by ring]
    exact hn.le
  have hε1 : ∀ᶠ n : ℕ in atTop, ε n ≤ 1 := (tendsto_order.1 hε).2 1 one_pos |>.mono fun n h => h.le
  have hLev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hev, prob_not_noShort hδ0 hδ1, hexp, hε1, hLev, eventually_ge_atTop 1]
    with n hn hN hexpn hεn hLn hn1
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set S := ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    fun pd : ℕ × ℕ => pd ∈ Rn δ n ∧ pd.1 ≠ 2 ∧ q0 < pd.1 ^ pd.2 with hS
  have hbound : ∀ pd : ℕ × ℕ, pd ∈ Rn δ n → pd.1 ≤ n ∧ pd.2 ≤ n := by
    rintro ⟨p, d⟩ ⟨hp, hd1, hdR, hpdR⟩
    have h1 : ((p * d : ℕ) : ℝ) ≤ n := by
      refine hpdR.trans ((div_le_self (by positivity) hLn).trans ?_)
      calc (n : ℝ) ^ (1 / 2 - δ) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = n := Real.rpow_one _
    have h2 : p * d ≤ n := by exact_mod_cast h1
    have hp1 := hp.one_lt
    constructor
    · nlinarith
    · nlinarith
  have hsub : ∀ ω : Pairs n → Bool, (∃ p d : ℕ, (p, d) ∈ Rn δ n ∧ p ≠ 2 ∧ q0 < p ^ d ∧
      IsLocalFailure p d (symOf 1 0 ω)) → ¬ NoShort δ n ω ∨
        ∃ pd ∈ S, IsLocalFailure pd.1 pd.2 (symOf 1 0 ω) ∧ NoShort δ n ω := by
    rintro ω ⟨p, d, hR, hp2, hq, hE⟩
    by_cases hN' : NoShort δ n ω
    · right
      refine ⟨(p, d), ?_, hE, hN'⟩
      obtain ⟨hpn, hdn⟩ := hbound (p, d) hR
      simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, hR, hp2, hq⟩
    · exact Or.inl hN'
  have hterm : ∀ pd ∈ S, prob (fun ω : Pairs n → Bool =>
      IsLocalFailure pd.1 pd.2 (symOf 1 0 ω) ∧ NoShort δ n ω) ≤ 2 * (2 / (((pd.1 ^ pd.2 : ℕ) : ℝ)) ^ 2) := by
    intro pd hpd
    simp only [hS, Finset.mem_filter] at hpd
    obtain ⟨-, hR, hp2, -⟩ := hpd
    have : Fact pd.1.Prime := ⟨hR.1⟩
    have h1 := hn pd.1 pd.2 hR hp2
    have h2 := cFirst_le (p := pd.1) (d := pd.2) hR.2.1
    have hc0 : 0 ≤ cFirst pd.1 pd.2 := by
      have hp1 : (1 : ℝ) < pd.1 := by exact_mod_cast hR.1.one_lt
      have : (1 : ℝ) < (pd.1 : ℝ) ^ pd.2 := one_lt_pow₀ hp1 (by have := hR.2.1; omega)
      rw [cFirst]; exact div_nonneg (Nat.cast_nonneg _) (by positivity)
    calc _ ≤ cFirst pd.1 pd.2 * (1 + ε n) := h1
      _ ≤ cFirst pd.1 pd.2 * 2 := mul_le_mul_of_nonneg_left (by linarith) hc0
      _ ≤ (2 / (((pd.1 ^ pd.2 : ℕ) : ℝ)) ^ 2) * 2 := mul_le_mul_of_nonneg_right h2 (by norm_num)
      _ = _ := by ring
  have hinj : Set.InjOn (fun pd : ℕ × ℕ => pd.1 ^ pd.2) S := by
    rintro ⟨p, d⟩ hpd ⟨p', d'⟩ hpd' h
    simp only [hS, Finset.coe_filter, Set.mem_ofPred_eq] at hpd hpd'
    obtain ⟨-, ⟨hp, hd, -⟩, -⟩ := hpd
    obtain ⟨-, ⟨hp', hd', -⟩, -⟩ := hpd'
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj' hp hp' (by omega) (by omega) h
    exact Prod.ext h1 h2
  have himg : S.image (fun pd : ℕ × ℕ => pd.1 ^ pd.2) ⊆ Finset.Ioo q0 (n ^ n + 1) := by
    intro t ht
    obtain ⟨⟨p, d⟩, hpd, rfl⟩ := Finset.mem_image.1 ht
    simp only [hS, Finset.mem_filter] at hpd
    obtain ⟨-, hR, -, hq⟩ := hpd
    obtain ⟨hpn, hdn⟩ := hbound (p, d) hR
    rw [Finset.mem_Ioo]
    refine ⟨hq, Nat.lt_succ_of_le ?_⟩
    calc p ^ d ≤ n ^ d := Nat.pow_le_pow_left hpn d
      _ ≤ n ^ n := Nat.pow_le_pow_right (by omega) hdn
  have hsum : ∑ pd ∈ S, 2 * (2 / (((pd.1 ^ pd.2 : ℕ) : ℝ)) ^ 2) ≤ η / 2 := by
    calc ∑ pd ∈ S, 2 * (2 / (((pd.1 ^ pd.2 : ℕ) : ℝ)) ^ 2)
        = ∑ t ∈ S.image (fun pd : ℕ × ℕ => pd.1 ^ pd.2), 2 * (2 / ((t : ℝ)) ^ 2) :=
          (Finset.sum_image (f := fun t : ℕ => 2 * (2 / ((t : ℝ)) ^ 2)) hinj).symm
      _ ≤ ∑ t ∈ Finset.Ioo q0 (n ^ n + 1), 2 * (2 / ((t : ℝ)) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => by positivity
      _ = 4 * ∑ t ∈ Finset.Ioo q0 (n ^ n + 1), (((t : ℝ)) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ ≤ 4 * (2 / ((q0 : ℝ) + 1)) := by
          gcongr
          exact sum_Ioo_inv_sq_le q0 (n ^ n + 1)
      _ ≤ η / 2 := by
          calc 4 * (2 / ((q0 : ℝ) + 1)) = 8 / ((q0 : ℝ) + 1) := by ring
            _ ≤ η / 2 := hq0
  calc prob (fun ω : Pairs n → Bool => ∃ p d : ℕ,
        (p, d) ∈ Rn δ n ∧ p ≠ 2 ∧ q0 < p ^ d ∧ IsLocalFailure p d (symOf 1 0 ω))
      ≤ prob (fun ω : Pairs n → Bool => ¬ NoShort δ n ω ∨
          ∃ pd ∈ S, IsLocalFailure pd.1 pd.2 (symOf 1 0 ω) ∧ NoShort δ n ω) := prob_mono hsub
    _ ≤ prob (fun ω : Pairs n → Bool => ¬ NoShort δ n ω) + prob (fun ω : Pairs n → Bool =>
          ∃ pd ∈ S, IsLocalFailure pd.1 pd.2 (symOf 1 0 ω) ∧ NoShort δ n ω) := prob_or_le _ _
    _ ≤ η / 2 + ∑ pd ∈ S, prob (fun ω : Pairs n → Bool =>
          IsLocalFailure pd.1 pd.2 (symOf 1 0 ω) ∧ NoShort δ n ω) :=
        add_le_add (hN.trans hexpn) (prob_exists_le_sum S _)
    _ ≤ η / 2 + ∑ pd ∈ S, 2 * (2 / (((pd.1 ^ pd.2 : ℕ) : ℝ)) ^ 2) :=
        add_le_add le_rfl (Finset.sum_le_sum hterm)
    _ ≤ η / 2 + η / 2 := add_le_add le_rfl hsum
    _ = η := by ring

end DGS
