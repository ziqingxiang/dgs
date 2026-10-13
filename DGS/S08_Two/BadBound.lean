module

public import DGS.S08_Two.Split

@[expose] public section

open Matrix Polynomial Module

namespace DGS

def gsum (t : ℕ) : ℕ := ∑ j ∈ Finset.range t, (j + 1)

theorem gsum_succ (t : ℕ) : gsum (t + 1) = gsum t + (t + 1) := Finset.sum_range_succ _ _

theorem theta_pos (t : ℕ) : 0 < theta t := Finset.prod_pos fun _ _ => by positivity

theorem theta_upper_aux (s : ℕ) : theta (s + 1) + 3 * 2 ^ gsum s ≤ 3 * 2 ^ gsum (s + 1) := by
  induction s with
  | zero => simp [theta, gsum]
  | succ s ih =>
    have hθ : theta (s + 1 + 1) = theta (s + 1) * (2 * 2 ^ (s + 1) + 1) := by
      rw [theta_succ, pow_succ]
      ring
    have hG1 : 2 ^ gsum (s + 1) = 2 ^ gsum s * 2 ^ (s + 1) := by rw [gsum_succ, pow_add]
    have hG2 : 2 ^ gsum (s + 1 + 1) = 2 ^ gsum s * 2 ^ (s + 1) * (2 * 2 ^ (s + 1)) := by
      rw [gsum_succ, pow_add, hG1, pow_succ]
      ring
    rw [hθ, hG1, hG2]
    rw [hG1] at ih
    have h := Nat.mul_le_mul_right (2 * 2 ^ (s + 1) + 1) ih
    generalize 2 ^ gsum s = X at *
    generalize 2 ^ (s + 1) = Y at *
    nlinarith [h]

theorem theta_le (t : ℕ) : theta t ≤ 3 * 2 ^ gsum t := by
  rcases t with - | s
  · simp [theta, gsum]
  · have := theta_upper_aux s
    omega

theorem theta_add_ge (t s : ℕ) :
    theta t * 2 ^ (∑ j ∈ Finset.range s, (t + j + 1)) ≤ theta (t + s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, pow_add, ← mul_assoc, show t + (s + 1) = t + s + 1 by ring, theta_succ]
    exact Nat.mul_le_mul ih (Nat.le_succ _)

theorem sum_range_add_eq (a' b' : ℕ) :
    ∑ j ∈ Finset.range (b' + 1), (a' + j + 1) = (a' + 1) * (b' + 1) + gsum b' := by
  induction b' with
  | zero => simp [gsum]
  | succ b ih =>
    rw [Finset.sum_range_succ, ih, gsum_succ]
    ring

theorem theta_ratio (a' b' : ℕ) :
    theta a' * theta b' * 2 ^ ((a' + 1) * (b' + 1)) ≤ 3 * theta (a' + b' + 1) := by
  have h1 := theta_le b'
  have h2 := theta_add_ge a' (b' + 1)
  rw [sum_range_add_eq, show a' + (b' + 1) = a' + b' + 1 by ring] at h2
  calc theta a' * theta b' * 2 ^ ((a' + 1) * (b' + 1))
      ≤ theta a' * (3 * 2 ^ gsum b') * 2 ^ ((a' + 1) * (b' + 1)) := by gcongr
    _ = 3 * (theta a' * 2 ^ ((a' + 1) * (b' + 1) + gsum b')) := by rw [pow_add]; ring
    _ ≤ 3 * theta (a' + b' + 1) := by gcongr

theorem large_n_cond {n : ℕ} (hn : 59 ≤ n) : 8 * n ^ 2 ≤ 2 ^ ((n + 1) / 2 / 2) := by
  have key : ∀ q, 15 ≤ q → 8 * (4 * q + 2) ^ 2 ≤ 2 ^ q := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base => norm_num
    | succ q hq ih =>
      rw [pow_succ 2 q]
      generalize 2 ^ q = X at *
      nlinarith [ih, hq, Nat.mul_le_mul hq hq]
  have hq15 : 15 ≤ (n + 1) / 2 / 2 := by omega
  have hnq : n ≤ 4 * ((n + 1) / 2 / 2) + 2 := by omega
  calc 8 * n ^ 2 ≤ 8 * (4 * ((n + 1) / 2 / 2) + 2) ^ 2 := by gcongr
    _ ≤ 2 ^ ((n + 1) / 2 / 2) := key _ hq15

theorem term_bound {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (hab : (m + 1) / 2 + (n - m + 1) / 2 = (n + 1) / 2) (H : 8 * n ^ 2 ≤ 2 ^ ((n + 1) / 2 / 2)) :
    (n.choose m : ℝ) * (1 / 2 : ℝ) ^ ((m + 1) / 2 * ((n - m + 1) / 2)) ≤
      8 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) * (1 / 2 : ℝ) ^ m := by
  obtain ⟨a', ha'⟩ : ∃ a', (m + 1) / 2 = a' + 1 := ⟨(m + 1) / 2 - 1, by omega⟩
  obtain ⟨b', hb'⟩ : ∃ b', (n - m + 1) / 2 = b' + 1 := ⟨(n - m + 1) / 2 - 1, by omega⟩
  have hκ : (n + 1) / 2 = a' + b' + 2 := by omega
  have hab' : a' ≤ b' := by omega
  have hm2 : m ≤ 2 * a' + 2 := by omega
  have hqb : (n + 1) / 2 / 2 ≤ b' + 1 := by omega
  rw [ha', hb', hκ]
  have hC : (n.choose m : ℝ) ≤ (n : ℝ) ^ (2 * a' + 2) := by
    have h1 : (n.choose m : ℝ) ≤ (n : ℝ) ^ m := by exact_mod_cast Nat.choose_le_pow n m
    exact h1.trans (pow_le_pow_right₀ (by exact_mod_cast hn) hm2)
  have hq : (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ b' ≤ 1 / 4 := by
    have h4 : 4 * n ^ 2 ≤ 2 ^ b' := by
      have h5 : 2 ^ ((n + 1) / 2 / 2) ≤ 2 ^ (b' + 1) := Nat.pow_le_pow_right (by norm_num) hqb
      rw [pow_succ] at h5
      omega
    have h4' : (4 : ℝ) * n ^ 2 ≤ 2 ^ b' := by exact_mod_cast h4
    have h2 : (0 : ℝ) < 2 ^ b' := by positivity
    rw [_root_.one_div_pow, mul_one_div, div_le_div_iff₀ h2 (by norm_num)]
    linarith
  have hq0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ b' := by positivity
  calc (n.choose m : ℝ) * (1 / 2 : ℝ) ^ ((a' + 1) * (b' + 1))
      ≤ (n : ℝ) ^ (2 * a' + 2) * (1 / 2 : ℝ) ^ ((a' + 1) * (b' + 1)) := by gcongr
    _ = (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (a' + b' + 1) * ((n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ b') ^ a' := by
        ring
    _ ≤ (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (a' + b' + 1) * (1 / 4 : ℝ) ^ a' := by gcongr
    _ ≤ (n : ℝ) ^ 2 * (2 * (1 / 2 : ℝ) ^ (a' + b' + 2)) * (4 * (1 / 2 : ℝ) ^ m) := by
        have e1 : (1 / 2 : ℝ) ^ (a' + b' + 1) = 2 * (1 / 2 : ℝ) ^ (a' + b' + 2) := by
          rw [pow_succ (1 / 2 : ℝ) (a' + b' + 1)]
          ring
        have e2 : (1 / 4 : ℝ) ^ a' ≤ 4 * (1 / 2 : ℝ) ^ m := by
          have e3 : (1 / 4 : ℝ) ^ a' = 4 * (1 / 2 : ℝ) ^ (2 * a' + 2) := by
            rw [pow_add, pow_mul, show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]
            ring
          rw [e3]
          have : (1 / 2 : ℝ) ^ (2 * a' + 2) ≤ (1 / 2 : ℝ) ^ m :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hm2
          linarith
        rw [e1]
        gcongr
    _ = 8 * n ^ 2 * (1 / 2 : ℝ) ^ (a' + b' + 2) * (1 / 2 : ℝ) ^ m := by ring

theorem sum_split_bound {n : ℕ} (hn : 1 ≤ n) (H : 8 * n ^ 2 ≤ 2 ^ ((n + 1) / 2 / 2)) :
    ∑ S ∈ splitSupports n, (1 / 2 : ℝ) ^ (kap S * kap Sᶜ) ≤
      32 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) := by
  classical
  set g : ℕ → ℝ := fun m => if 1 ≤ m ∧ m < n ∧ m / 2 + (n - m) / 2 = n / 2 then
    (1 / 2 : ℝ) ^ ((m + 1) / 2 * ((n - m + 1) / 2)) else 0 with hg
  have h1 : ∑ S ∈ splitSupports n, (1 / 2 : ℝ) ^ (kap S * kap Sᶜ) =
      ∑ S : Finset (Fin n), g S.card := by
    rw [splitSupports, Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hc : Sᶜ.card = n - S.card := by rw [Finset.card_compl, Fintype.card_fin]
    have e1 : S.Nonempty ↔ 1 ≤ S.card := by rw [← Finset.card_pos]; rfl
    have e2 : S ≠ Finset.univ ↔ S.card < n := by
      rw [← Finset.card_lt_iff_ne_univ, Fintype.card_fin]
    simp only [hg, kap, hc]
    by_cases h : S.Nonempty ∧ S ≠ Finset.univ ∧ S.card / 2 + (n - S.card) / 2 = n / 2
    · rw [ite_eq_left h, ite_eq_left ⟨e1.1 h.1, e2.1 h.2.1, h.2.2⟩]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨e1.2 h'.1, e2.2 h'.2.1, h'.2.2⟩)]
  rw [h1]
  have h2 : ∑ S : Finset (Fin n), g S.card =
      ∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * g m := by
    rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
  rw [h2]
  have h3 : ∀ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * g m ≤
      8 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) * ((1 / 2 : ℝ) ^ m + (1 / 2 : ℝ) ^ (n - m)) := by
    intro m hm
    rw [Finset.mem_range] at hm
    simp only [hg]
    split_ifs with hc
    · obtain ⟨hm1, hmn, hcond⟩ := hc
      have hab : (m + 1) / 2 + (n - m + 1) / 2 = (n + 1) / 2 := by omega
      rw [mul_add]
      by_cases h2m : 2 * m ≤ n
      · have := term_bound hn hm1 h2m hab H
        have h0 : (0 : ℝ) ≤ 8 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) * (1 / 2 : ℝ) ^ (n - m) := by
          positivity
        linarith
      · have hm' : 1 ≤ n - m := by omega
        have h2m' : 2 * (n - m) ≤ n := by omega
        have hnm : n - (n - m) = m := by omega
        have hab' : (n - m + 1) / 2 + (n - (n - m) + 1) / 2 = (n + 1) / 2 := by
          rw [hnm]
          omega
        have := term_bound hn hm' h2m' hab' H
        rw [Nat.choose_symm (by omega), hnm, mul_comm ((n - m + 1) / 2)] at this
        have h0 : (0 : ℝ) ≤ 8 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) * (1 / 2 : ℝ) ^ m := by
          positivity
        linarith
    · rw [mul_zero]
      positivity
  have hrefl : ∑ m ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (n - m) =
      ∑ m ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ m := by
    have := Finset.sum_range_reflect (fun m => (1 / 2 : ℝ) ^ m) (n + 1)
    simp only [Nat.add_sub_cancel] at this
    exact this
  calc ∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * g m
      ≤ ∑ m ∈ Finset.range (n + 1), 8 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) *
          ((1 / 2 : ℝ) ^ m + (1 / 2 : ℝ) ^ (n - m)) := Finset.sum_le_sum h3
    _ = 8 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) * (∑ m ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ m +
          ∑ m ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (n - m)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 8 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) * (2 + 2) := by
        rw [hrefl]
        gcongr
        · exact sum_geometric_two_le _
        · exact sum_geometric_two_le _
    _ = 32 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) := by ring

variable {n : ℕ}

local notation "V" => Fin n → ZMod 2
local notation "Mat" => Matrix (Fin n) (Fin n) (ZMod 2)

theorem theta_split_le {S : Finset (Fin n)} (hS : S ∈ splitSupports n) :
    ((theta (kap S - 1) * theta (kap Sᶜ - 1) : ℕ) : ℝ) ≤
      3 * theta (kap (Finset.univ : Finset (Fin n)) - 1) * (1 / 2 : ℝ) ^ (kap S * kap Sᶜ) := by
  obtain ⟨-, h1S, h2S, h3S⟩ := Finset.mem_filter.1 hS
  have hc : Sᶜ.card = n - S.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hSc : S.card < n := by
    have := (Finset.card_lt_iff_ne_univ S).2 h2S
    rwa [Fintype.card_fin] at this
  have hSp := Finset.card_pos.2 h1S
  obtain ⟨a', ha'⟩ : ∃ a', kap S = a' + 1 := ⟨kap S - 1, by unfold kap; omega⟩
  obtain ⟨b', hb'⟩ : ∃ b', kap Sᶜ = b' + 1 := ⟨kap Sᶜ - 1, by unfold kap; rw [hc]; omega⟩
  have hκ : kap (Finset.univ : Finset (Fin n)) = a' + b' + 2 := by
    unfold kap at ha' hb' ⊢
    rw [hc] at hb' h3S
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  rw [ha', hb', hκ, Nat.add_sub_cancel, Nat.add_sub_cancel, show a' + b' + 2 - 1 = a' + b' + 1 by omega]
  have h' : ((theta a' * theta b' * 2 ^ ((a' + 1) * (b' + 1)) : ℕ) : ℝ) ≤
      ((3 * theta (a' + b' + 1) : ℕ) : ℝ) := by exact_mod_cast theta_ratio a' b'
  push_cast at h' ⊢
  have e : (theta a' : ℝ) * theta b' =
      (theta a' : ℝ) * theta b' * 2 ^ ((a' + 1) * (b' + 1)) * (1 / 2 : ℝ) ^ ((a' + 1) * (b' + 1)) := by
    rw [mul_assoc _ ((2 : ℝ) ^ _), ← mul_pow]
    norm_num
  rw [e]
  gcongr

theorem prob_bad_le (hn : 1 ≤ n) (H : 8 * n ^ 2 ≤ 2 ^ ((n + 1) / 2 / 2)) :
    prob (fun ω : Pairs n → Bool => BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2)))) ≤
      96 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) := by
  rw [prob_eq_alt (fun M => BadK (cyc M (ones n (ZMod 2))))]
  have hS : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have h1 := coupling_maxIso hn
  rw [card_maxIso hS] at h1
  have h2 := card_bad_maxIso_le (n := n)
  set θ := theta (kap (Finset.univ : Finset (Fin n)) - 1) with hθ
  set A := Nat.card {M : Mat // IsAlt M} with hA
  set B := Nat.card {M : Mat // IsAlt M ∧ BadK (cyc M (ones n (ZMod 2)))} with hB
  have hApos : (0 : ℝ) < A := by
    have : Nonempty {M : Mat // IsAlt M} := ⟨⟨0, transpose_zero, fun i => rfl⟩⟩
    exact_mod_cast Nat.card_pos
  have hθpos : (0 : ℝ) < θ := by exact_mod_cast theta_pos _
  have h3 : (B : ℝ) * θ ≤ (∑ S ∈ splitSupports n, ((theta (kap S - 1) * theta (kap Sᶜ - 1) : ℕ) : ℝ)) * A := by
    have h4 : B * θ ≤ (∑ S ∈ splitSupports n, theta (kap S - 1) * theta (kap Sᶜ - 1)) * A :=
      h1.trans (Nat.mul_le_mul_right _ h2)
    exact_mod_cast h4
  have h5 : ∑ S ∈ splitSupports n, ((theta (kap S - 1) * theta (kap Sᶜ - 1) : ℕ) : ℝ) ≤
      3 * θ * (32 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2)) := by
    calc ∑ S ∈ splitSupports n, ((theta (kap S - 1) * theta (kap Sᶜ - 1) : ℕ) : ℝ)
        ≤ ∑ S ∈ splitSupports n, 3 * (θ : ℝ) * (1 / 2 : ℝ) ^ (kap S * kap Sᶜ) :=
          Finset.sum_le_sum fun S hS' => theta_split_le hS'
      _ = 3 * θ * ∑ S ∈ splitSupports n, (1 / 2 : ℝ) ^ (kap S * kap Sᶜ) := by rw [Finset.mul_sum]
      _ ≤ 3 * θ * (32 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2)) := by
          gcongr
          exact sum_split_bound hn H
  rw [div_le_iff₀ hApos]
  have h6 : (B : ℝ) * θ ≤ 3 * θ * (32 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2)) * A :=
    h3.trans (by gcongr)
  have h7 : (B : ℝ) * θ ≤ 96 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) * A * θ := by
    linarith
  have : (B : ℝ) ≤ 96 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) * A :=
    le_of_mul_le_mul_right h7 hθpos
  change (Nat.card {M // IsAlt M ∧ BadK (cyc M (ones n (ZMod 2)))} : ℝ) ≤ _
  rw [← hB]
  exact this

theorem lem_condlaw_ii :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      prob (fun ω : Pairs n → Bool => BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2)))) ≤
        C * n ^ 2 * (1 / 2 : ℝ) ^ (n / 2) := by
  refine ⟨2 ^ 60, fun n hn => ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases h59 : 59 ≤ n
  · calc prob (fun ω : Pairs n → Bool => BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))))
        ≤ 96 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) := prob_bad_le hn (large_n_cond h59)
      _ ≤ 2 ^ 60 * n ^ 2 * (1 / 2 : ℝ) ^ ((n + 1) / 2) := by gcongr; norm_num
      _ ≤ 2 ^ 60 * n ^ 2 * (1 / 2 : ℝ) ^ (n / 2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
            (by positivity)
  · calc prob (fun ω : Pairs n → Bool => BadK (cyc (modP 2 (symOf 1 0 ω)) (ones n (ZMod 2))))
        ≤ 1 := prob_le_one _
      _ ≤ 2 ^ 60 * (1 / 2 : ℝ) ^ 29 := by norm_num
      _ ≤ 2 ^ 60 * (1 / 2 : ℝ) ^ (n / 2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
            (by positivity)
      _ ≤ 2 ^ 60 * n ^ 2 * (1 / 2 : ℝ) ^ (n / 2) := by
          have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
          have h0 : (0 : ℝ) ≤ 2 ^ 60 * (1 / 2 : ℝ) ^ (n / 2) := by positivity
          nlinarith

end DGS
