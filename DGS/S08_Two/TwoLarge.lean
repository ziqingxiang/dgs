module

public import DGS.S08_Two.BadBound
public import DGS.S07_Small.IrrCount

@[expose] public section

open Matrix Polynomial Module

namespace DGS

variable {n : ℕ}

local notation "V" => Fin n → ZMod 2
local notation "Mat" => Matrix (Fin n) (Fin n) (ZMod 2)

def E2 (d₀ : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (walkMatrix A).det ≠ 0 ∧ ∃ β : (ZMod 2)[X], β.Monic ∧ Irreducible β ∧ d₀ ≤ β.natDegree ∧
    TTpart A 2 β ≠ ⊥ ∧ ¬ IsChainComponent A 2 β

section Step1

variable {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hd : ∀ i, A i i = 0) (hn : 1 ≤ n)
include hA hd hn

theorem omega_vanish_of {β : (ZMod 2)[X]} (hβm : β.Monic) (hβ : Irreducible β)
    (hβμ : β ∣ muVec (modP 2 A) (ones n (ZMod 2))) {γ' : (ZMod 2)[X]} (hγ' : ¬ β ∣ γ')
    (hc : ∀ t, omegaF A ((muVec (modP 2 A) (ones n (ZMod 2)) ^ 2 /ₘ β * γ' ^ 2) * t) = 0)
    (r : (ZMod 2)[X]) :
    omegaF A (muVec (modP 2 A) (ones n (ZMod 2)) ^ 2 /ₘ β * r) = 0 := by
  set μ := muVec (modP 2 A) (ones n (ZMod 2)) with hμ
  have hcop : IsCoprime β (γ' ^ 2) := by
    rw [Irreducible.coprime_iff_not_dvd hβ]
    intro h
    exact hγ' (hβ.prime.dvd_of_dvd_pow h)
  obtain ⟨u, v, huv⟩ := hcop
  have hq := (quot_spec hβm ((muVec_monic _ _).pow 2) (hβμ.trans (dvd_pow_self μ two_ne_zero))).1
  have e : μ ^ 2 /ₘ β * r = (μ ^ 2 /ₘ β * γ' ^ 2) * (v * r) + μ ^ 2 * (u * r) := by
    calc μ ^ 2 /ₘ β * r = μ ^ 2 /ₘ β * r * (u * β + v * γ' ^ 2) := by rw [huv, mul_one]
      _ = (μ ^ 2 /ₘ β * γ' ^ 2) * (v * r) + (β * (μ ^ 2 /ₘ β)) * (u * r) := by ring
      _ = _ := by rw [hq]
  rw [e, omegaF_add hA hd hn, hc, lem_Lambda_iii hA hd hn, add_zero]

theorem twolarge_step1 {d₀ : ℕ} (hd₀ : 2 ≤ d₀) (hE : E2 d₀ A) :
    d₀ ≤ (n + 1) / 2 - (muVec (modP 2 A) (ones n (ZMod 2))).natDegree ∨
      ∃ β : (ZMod 2)[X], β.Monic ∧ Irreducible β ∧ d₀ ≤ β.natDegree ∧ ZEv (modP 2 A) β := by
  obtain ⟨hW, β, hβm, hβ, hβd, hT, hnc⟩ := hE
  set μ := muVec (modP 2 A) (ones n (ZMod 2)) with hμ
  by_cases hj : d₀ ≤ (n + 1) / 2 - μ.natDegree
  · exact Or.inl hj
  right
  refine ⟨β, hβm, hβ, hβd, ?_⟩
  have hγ := (lem_Ttwo_c hA hd hn hW hβm hβ).1 hT
  obtain ⟨-, γ', hγ'm, hγ'd, hfac⟩ := lem_krylovlaw_a hA hd
  rw [← hμ] at hγ'd hfac
  have hγ' : ¬ β ∣ γ' := by
    intro h
    have := natDegree_le_of_dvd h hγ'm.ne_zero
    omega
  have hβgo : β ∣ gamo A := dvd_mul_of_dvd_right hγ _
  rw [hfac] at hβgo
  have hβμ : β ∣ μ := (hβ.prime.dvd_or_dvd hβgo).resolve_right hγ'
  have hq := (quot_spec hβm ((muVec_monic _ _).pow 2) (hβμ.trans (dvd_pow_self μ two_ne_zero))).1
  have hc : (μ ^ 2 /ₘ β * γ' ^ 2) * β = gamo A ^ 2 := by
    rw [hfac, mul_pow]
    calc (μ ^ 2 /ₘ β * γ' ^ 2) * β = (β * (μ ^ 2 /ₘ β)) * γ' ^ 2 := by ring
      _ = μ ^ 2 * γ' ^ 2 := by rw [hq]
  have hω : ∀ t, omegaF A ((μ ^ 2 /ₘ β * γ' ^ 2) * t) = 0 := by
    intro t
    by_contra h
    exact hnc (lem_wangLC hA hd hn hW hβm hβ hγ hc ⟨t, h⟩).1
  refine ⟨hβμ, fun r _ => ?_⟩
  set f := μ ^ 2 /ₘ β * r with hf
  have hf0 : omegaF A f = 0 := omega_vanish_of hA hd hn hβm hβ hβμ hγ' hω r
  have hodd : n % 2 = 1 → (contract 2 f).coeff 0 = 0 := by
    intro hodd
    rw [coeff_contract two_ne_zero, zero_mul]
    have hXμ := X_dvd_muVec (modP_two_transpose hA) (modP_two_diag hd) hodd
    have hXβ : ¬ X ∣ β := by
      intro h
      have := natDegree_le_of_dvd (irreducible_X.dvd_symm hβ h) X_ne_zero
      rw [natDegree_X] at this
      omega
    have hX : X ∣ μ ^ 2 /ₘ β := by
      have h1 : X ∣ β * (μ ^ 2 /ₘ β) := by
        rw [hq]
        exact hXμ.trans (dvd_pow_self μ two_ne_zero)
      exact (prime_X.dvd_or_dvd h1).resolve_left hXβ
    exact X_dvd_iff.1 (hX.mul_right r)
  have := lem_Lambda_ii hA hd hn (contract 2 f) (contract 2 (divX f)) hodd
  rw [← sq_decomp f, hf0] at this
  exact this.symm

end Step1

theorem prob_Z_le (hn : 1 ≤ n) {β : (ZMod 2)[X]} (hβm : β.Monic) (hβ : Irreducible β) (hβX : β ≠ X) :
    prob (fun ω : Pairs n → Bool => ZEv (modP 2 (symOf 1 0 ω)) β ∧
        ¬ BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2)))) ≤
      2 * (1 / 4 : ℝ) ^ β.natDegree := by
  rw [prob_eq_alt (fun M => ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2))))]
  have h := step3_count hβm hβ hn hβX
  have hd1 : 1 ≤ β.natDegree := hβ.natDegree_pos
  have hApos : (0 : ℝ) < Nat.card {M : Mat // IsAlt M} := by
    have : Nonempty {M : Mat // IsAlt M} := ⟨⟨0, transpose_zero, fun i => rfl⟩⟩
    exact_mod_cast Nat.card_pos
  rw [div_le_iff₀ hApos]
  have h' : (Nat.card {M : Mat // IsAlt M ∧ ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2)))} : ℝ) *
      2 ^ (2 * β.natDegree - 1) ≤ Nat.card {M : Mat // IsAlt M} := by exact_mod_cast h
  have e : (2 : ℝ) ^ (2 * β.natDegree - 1) * (2 * (1 / 4 : ℝ) ^ β.natDegree) = 1 := by
    obtain ⟨d', hd'⟩ : ∃ d', β.natDegree = d' + 1 := ⟨β.natDegree - 1, by omega⟩
    rw [hd', show 2 * (d' + 1) - 1 = 2 * d' + 1 by omega]
    have e1 : (2 : ℝ) ^ (2 * d' + 1) * (2 * (1 / 4 : ℝ) ^ (d' + 1)) =
        ((2 : ℝ) ^ 2 * (1 / 4)) ^ (d' + 1) := by
      rw [mul_pow, ← pow_mul]
      ring
    rw [e1]
    norm_num
  have h2 : (0 : ℝ) ≤ 2 * (1 / 4 : ℝ) ^ β.natDegree := by positivity
  calc (Nat.card {M : Mat // IsAlt M ∧ ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2)))} : ℝ)
      = (Nat.card {M : Mat // IsAlt M ∧ ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2)))} : ℝ) *
          2 ^ (2 * β.natDegree - 1) * (2 * (1 / 4 : ℝ) ^ β.natDegree) := by
        rw [mul_assoc, e, mul_one]
    _ ≤ 2 * (1 / 4 : ℝ) ^ β.natDegree * Nat.card {M : Mat // IsAlt M} := by
        rw [mul_comm (2 * (1 / 4 : ℝ) ^ β.natDegree)]
        exact mul_le_mul_of_nonneg_right h' h2

theorem sum_irr_bound {d₀ : ℕ} (hd₀ : 2 ≤ d₀) (N : ℕ) :
    ∑ d ∈ Finset.Icc d₀ N, (piCount 2 d : ℝ) * (2 * (1 / 4 : ℝ) ^ d) ≤ 2 * (1 / 2 : ℝ) ^ d₀ := by
  have h1 : ∀ d ∈ Finset.Icc d₀ N, (piCount 2 d : ℝ) * (2 * (1 / 4 : ℝ) ^ d) ≤ (1 / 2 : ℝ) ^ d := by
    intro d hd
    have hd2 : 2 ≤ d := le_trans hd₀ (Finset.mem_Icc.1 hd).1
    have hπ := piCount_le_div 2 (d := d) (by omega)
    push_cast at hπ
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hd2' : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have e1 : (2 : ℝ) ^ d * (1 / 4 : ℝ) ^ d = (1 / 2 : ℝ) ^ d := by
      rw [← mul_pow]
      norm_num
    calc (piCount 2 d : ℝ) * (2 * (1 / 4 : ℝ) ^ d)
        ≤ (2 : ℝ) ^ d / d * (2 * (1 / 4 : ℝ) ^ d) := by gcongr
      _ = 2 / d * ((2 : ℝ) ^ d * (1 / 4 : ℝ) ^ d) := by ring
      _ = 2 / d * (1 / 2 : ℝ) ^ d := by rw [e1]
      _ ≤ 1 * (1 / 2 : ℝ) ^ d := by
          gcongr
          rw [div_le_one hdpos]
          exact hd2'
      _ = (1 / 2 : ℝ) ^ d := one_mul _
  calc ∑ d ∈ Finset.Icc d₀ N, (piCount 2 d : ℝ) * (2 * (1 / 4 : ℝ) ^ d)
      ≤ ∑ d ∈ Finset.Icc d₀ N, (1 / 2 : ℝ) ^ d := Finset.sum_le_sum h1
    _ = ∑ k ∈ Finset.range (N + 1 - d₀), (1 / 2 : ℝ) ^ (d₀ + k) := by
        rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    _ = (1 / 2 : ℝ) ^ d₀ * ∑ k ∈ Finset.range (N + 1 - d₀), (1 / 2 : ℝ) ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => pow_add _ _ _
    _ ≤ (1 / 2 : ℝ) ^ d₀ * 2 := by
        gcongr
        exact sum_geometric_two_le _
    _ = 2 * (1 / 2 : ℝ) ^ d₀ := mul_comm _ _

noncomputable def irrRange (d₀ n : ℕ) : Finset (ZMod 2)[X] :=
  (Finset.Icc d₀ n).biUnion (fun d => irrSet 2 d)

theorem mem_irrRange {d₀ n : ℕ} {β : (ZMod 2)[X]} :
    β ∈ irrRange d₀ n ↔ β.Monic ∧ Irreducible β ∧ d₀ ≤ β.natDegree ∧ β.natDegree ≤ n := by
  classical
  rw [irrRange, Finset.mem_biUnion]
  constructor
  · rintro ⟨d, hd, hβ⟩
    obtain ⟨h1, h2, h3⟩ := mem_irrSet_iff.1 hβ
    rw [Finset.mem_Icc] at hd
    exact ⟨h1, h2, h3 ▸ hd.1, h3 ▸ hd.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨β.natDegree, Finset.mem_Icc.2 ⟨h3, h4⟩, mem_irrSet_iff.2 ⟨h1, h2, rfl⟩⟩

theorem twolarge_incl (hn : 1 ≤ n) {d₀ : ℕ} (hd₀ : 2 ≤ d₀) (ω : Pairs n → Bool)
    (hE : E2 d₀ (symOf 1 0 ω)) :
    d₀ ≤ (n + 1) / 2 - (muVec (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))).natDegree ∨
      (BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))) ∨
        ∃ β ∈ irrRange d₀ n, ZEv (modP 2 (symOf 1 0 ω)) β ∧
          ¬ BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2)))) := by
  rcases twolarge_step1 (symOf_isSymm ω) (fun i => symOf_apply_self 1 0 ω i) hn hd₀ hE with
    h | ⟨β, hβm, hβ, hβd, hZ⟩
  · exact Or.inl h
  · right
    by_cases hB : BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2)))
    · exact Or.inl hB
    · right
      refine ⟨β, mem_irrRange.2 ⟨hβm, hβ, hβd, ?_⟩, hZ, hB⟩
      exact (natDegree_le_of_dvd hZ.1 (muVec_monic _ _).ne_zero).trans (natDegree_muVec_le _)

theorem prob_union_Z_le (hn : 1 ≤ n) {d₀ : ℕ} (hd₀ : 2 ≤ d₀) :
    prob (fun ω : Pairs n → Bool => ∃ β ∈ irrRange d₀ n, ZEv (modP 2 (symOf 1 0 ω)) β ∧
      ¬ BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2)))) ≤ 2 * (1 / 2 : ℝ) ^ d₀ := by
  classical
  have hdisj : ((Finset.Icc d₀ n : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun d => irrSet 2 d) := by
    intro d _ d' _ hne
    refine Finset.disjoint_left.2 fun β h1 h2 => hne ?_
    exact (mem_irrSet_iff.1 h1).2.2.symm.trans (mem_irrSet_iff.1 h2).2.2
  have hsum : ∑ β ∈ irrRange d₀ n, 2 * (1 / 4 : ℝ) ^ β.natDegree =
      ∑ d ∈ Finset.Icc d₀ n, (piCount 2 d : ℝ) * (2 * (1 / 4 : ℝ) ^ d) := by
    rw [irrRange, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_congr rfl fun β hβ => by rw [(mem_irrSet_iff.1 hβ).2.2],
      Finset.sum_const, nsmul_eq_mul, piCount]
  calc prob (fun ω : Pairs n → Bool => ∃ β ∈ irrRange d₀ n, ZEv (modP 2 (symOf 1 0 ω)) β ∧
        ¬ BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))))
      ≤ ∑ β ∈ irrRange d₀ n, prob (fun ω : Pairs n → Bool => ZEv (modP 2 (symOf 1 0 ω)) β ∧
        ¬ BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2)))) := prob_exists_le_sum _ _
    _ ≤ ∑ β ∈ irrRange d₀ n, 2 * (1 / 4 : ℝ) ^ β.natDegree := by
        refine Finset.sum_le_sum fun β hβT => ?_
        obtain ⟨hβm, hβ, hdeg, -⟩ := mem_irrRange.1 hβT
        have hβX : β ≠ X := by
          rintro rfl
          rw [natDegree_X] at hdeg
          omega
        exact prob_Z_le hn hβm hβ hβX
    _ = ∑ d ∈ Finset.Icc d₀ n, (piCount 2 d : ℝ) * (2 * (1 / 4 : ℝ) ^ d) := hsum
    _ ≤ 2 * (1 / 2 : ℝ) ^ d₀ := sum_irr_bound hd₀ n

theorem prop_twolarge :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ d₀ : ℕ, 2 ≤ d₀ →
      prob (fun ω : Pairs n → Bool => E2 d₀ (symOf 1 0 ω)) ≤
        4 * (1 / 2 : ℝ) ^ d₀ + C * n ^ 2 * (1 / 2 : ℝ) ^ (n / 2) := by
  obtain ⟨C, hC⟩ := lem_condlaw_ii
  refine ⟨C, fun n hn d₀ hd₀ => ?_⟩
  have hj := lem_krylovlaw_b hn d₀
  have hB := hC n hn
  have hZ := prob_union_Z_le hn hd₀
  have h4 : (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ d₀ ≤ 2 * (1 / 2 : ℝ) ^ d₀ := by
    have h1 : (1 / 4 : ℝ) ^ d₀ ≤ (1 / 2 : ℝ) ^ d₀ := by
      gcongr
      norm_num
    have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ d₀ := by positivity
    linarith
  have h1 := prob_mono (twolarge_incl hn hd₀)
  have h2 := prob_or_le (fun ω : Pairs n → Bool =>
      d₀ ≤ (n + 1) / 2 - (muVec (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))).natDegree)
    (fun ω : Pairs n → Bool => BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))) ∨
      ∃ β ∈ irrRange d₀ n, ZEv (modP 2 (symOf 1 0 ω)) β ∧
        ¬ BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))))
  have h3 := prob_or_le (fun ω : Pairs n → Bool => BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))))
    (fun ω : Pairs n → Bool => ∃ β ∈ irrRange d₀ n, ZEv (modP 2 (symOf 1 0 ω)) β ∧
        ¬ BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))))
  linarith

theorem prop_twolarge_mates {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hn : 1 ≤ n)
    (hW : (walkMatrix A).det ≠ 0) {d₀ : ℕ} (hE : ¬ E2 d₀ A) {β : (ZMod 2)[X]} (hβm : β.Monic)
    (hβ : Irreducible β) (hβd : d₀ ≤ β.natDegree) {Q : Matrix (Fin n) (Fin n) ℚ}
    (hQ : IsMateMatrix A Q) : β ∉ Fset A Q 2 := by
  intro hF
  have hnc := (levellocal_ii hA hn hW hQ hF).2.1
  apply hE
  refine ⟨hW, β, hβm, hβ, hβd, ?_, hnc⟩
  intro hbot
  apply hnc
  intro 𝔄 𝔅 h1 h2
  rw [hbot] at h1 h2
  left
  rw [le_bot_iff.1 h1]
  exact bot_le

end DGS
