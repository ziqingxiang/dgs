module

public import DGS.S11_Deg1.PtLaws

@[expose] public section

open Finset

namespace DGS

theorem pexp_blocks' {ι G κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G] [Fintype κ]
    (ν : ι → G → ℝ) (hν1 : ∀ j, ∑ a, ν j a = 1) (B : κ → Finset ι)
    (hB : Pairwise fun i i' => Disjoint (B i) (B i')) (F : ∀ i, (B i → G) → ℝ) :
    pexp ν (fun y => ∏ i, F i (fun j : B i => y j)) = ∏ i, pexp (fun j : B i => ν j) (F i) := by
  set e := Fintype.equivFin κ
  have h := pexp_blocks ν hν1 (fun i => B (e.symm i)) (fun i i' hii' => hB (e.symm.injective.ne hii'))
    (fun i => F (e.symm i))
  have e1 : (fun y : ι → G => ∏ i, F i (fun j : B i => y j)) =
      fun y => ∏ i, F (e.symm i) (fun j : B (e.symm i) => y j) := by
    funext y
    exact (e.symm.prod_comp (fun i => F i (fun j : B i => y j))).symm
  rw [e1, h]
  exact e.symm.prod_comp (fun i => pexp (fun j : B i => ν j) (F i))

theorem pow_le_P2_pow {t P2 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (htP : 1 ≤ P2 * t) {N M k : ℕ}
    (hM : M ≤ N + k) : t ^ N ≤ P2 ^ k * t ^ M := by
  have hP1 : 1 ≤ P2 := by nlinarith
  rcases le_or_gt M N with hMN | hMN
  · calc t ^ N ≤ t ^ M := pow_le_pow_of_le_one ht0.le ht1 hMN
      _ = 1 * t ^ M := (one_mul _).symm
      _ ≤ P2 ^ k * t ^ M := mul_le_mul_of_nonneg_right (one_le_pow₀ hP1) (by positivity)
  · obtain ⟨d, rfl⟩ : ∃ d, M = N + d := ⟨M - N, by omega⟩
    have hdk : d ≤ k := by omega
    have h1 : 1 ≤ P2 ^ k * t ^ d := by
      calc (1 : ℝ) ≤ (P2 * t) ^ d := one_le_pow₀ htP
        _ = P2 ^ d * t ^ d := mul_pow _ _ _
        _ ≤ P2 ^ k * t ^ d := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP1 hdk) (by positivity)
    calc t ^ N = t ^ N * 1 := (mul_one _).symm
      _ ≤ t ^ N * (P2 ^ k * t ^ d) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = P2 ^ k * t ^ (N + d) := by rw [pow_add]; ring

theorem sub_chain_le {D k s : ℕ} (hk : 0 < k) (hsk : s ≤ k) :
    D - (k - s) * (D / k) ≤ k + s * (D / k) := by
  have h1 := Nat.div_add_mod D k
  have h2 := Nat.mod_lt D hk
  have h3 : (k - s) * (D / k) + s * (D / k) = k * (D / k) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hsk]
  omega

theorem chain_le {D k s : ℕ} : (k - s) * (D / k) ≤ D :=
  (Nat.mul_le_mul_right _ (Nat.sub_le k s)).trans (Nat.mul_div_le D k)

theorem level_pair_bound {N m k s : ℕ} {t P2 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (htP : 1 ≤ P2 * t)
    (mass ζ cf : Fin 3 → ℝ) (hmass0 : ∀ X, 0 ≤ mass X) (hmassP : ∀ X, mass X ≤ P2)
    (hζ0 : ∀ X, 0 ≤ ζ X) (hcf : ∀ X, mass X * ζ X * t ≤ cf X)
    (D : Fin 3 → ℕ) (hsum : ∑ X, D X ≤ m) (hNm : N + k = m) (hsk : s ≤ k) (hk : 0 < k) :
    (∏ X, mass X ^ D X) * (2 * t) ^ N * ∏ X, ζ X ^ ((k - s) * (D X / k)) ≤
      2 ^ N * P2 ^ (4 * k + s * (m / k)) * ∏ X, cf X ^ ((k - s) * (D X / k)) := by
  have hP1 : 1 ≤ P2 := by nlinarith
  set M : Fin 3 → ℕ := fun X => (k - s) * (D X / k) with hM
  set r : Fin 3 → ℕ := fun X => D X - M X with hr
  have hMD : ∀ X, M X ≤ D X := fun X => chain_le
  have hDMr : ∀ X, D X = M X + r X := fun X => by
    have := hMD X
    simp only [hr]
    omega
  have hrsum : ∑ X, r X ≤ 3 * k + s * (m / k) := by
    have h1 : ∀ X, r X ≤ k + s * (D X / k) := fun X => sub_chain_le hk hsk
    have h2 : ∑ X, D X / k ≤ m / k := by
      rw [Nat.le_div_iff_mul_le hk, sum_mul]
      exact (sum_le_sum fun X _ => Nat.div_mul_le_self (D X) k).trans hsum
    calc ∑ X, r X ≤ ∑ X : Fin 3, (k + s * (D X / k)) := sum_le_sum fun X _ => h1 X
      _ = 3 * k + s * ∑ X, D X / k := by rw [sum_add_distrib, ← mul_sum]; simp
      _ ≤ 3 * k + s * (m / k) := by gcongr
  have hMsum : ∑ X, M X ≤ N + k := by
    rw [hNm]
    exact (sum_le_sum fun X _ => hMD X).trans hsum
  have hmassD : ∏ X, mass X ^ D X ≤ (∏ X, mass X ^ M X) * P2 ^ (∑ X, r X) := by
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    refine prod_le_prod₀ (fun X _ => pow_nonneg (hmass0 X) _) fun X _ => ?_
    rw [hDMr X, pow_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hmass0 X) (hmassP X) _)
      (pow_nonneg (hmass0 X) _)
  have ht := pow_le_P2_pow ht0 ht1 htP hMsum
  have hchain : (∏ X, mass X ^ M X) * t ^ (∑ X, M X) * ∏ X, ζ X ^ M X ≤ ∏ X, cf X ^ M X := by
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_le_prod₀ (fun X _ => by have := hmass0 X; have := hζ0 X; positivity) fun X _ => ?_
    rw [← mul_pow, ← mul_pow]
    have h := hcf X
    have h0 : 0 ≤ mass X * t * ζ X := by have := hmass0 X; have := hζ0 X; positivity
    exact pow_le_pow_left₀ h0 (by linarith) _
  have hP : P2 ^ (k + ∑ X, r X) ≤ P2 ^ (4 * k + s * (m / k)) := pow_le_pow_right₀ hP1 (by omega)
  have hP0 : 0 ≤ P2 := by linarith
  have hζ : 0 ≤ ∏ X, ζ X ^ M X := prod_nonneg fun X _ => pow_nonneg (hζ0 X) _
  have hmD : 0 ≤ ∏ X, mass X ^ D X := prod_nonneg fun X _ => pow_nonneg (hmass0 X) _
  have hmM : 0 ≤ ∏ X, mass X ^ M X := prod_nonneg fun X _ => pow_nonneg (hmass0 X) _
  have hst : 0 ≤ (∏ X, mass X ^ M X) * t ^ (∑ X, M X) * ∏ X, ζ X ^ M X := by positivity
  calc (∏ X, mass X ^ D X) * (2 * t) ^ N * ∏ X, ζ X ^ M X
      ≤ ((∏ X, mass X ^ M X) * P2 ^ (∑ X, r X)) * (2 ^ N * (P2 ^ k * t ^ (∑ X, M X))) *
          ∏ X, ζ X ^ M X := by
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ hζ
        apply mul_le_mul hmassD _ (by positivity) (hmD.trans hmassD)
        exact mul_le_mul_of_nonneg_left ht (by positivity)
    _ = 2 ^ N * P2 ^ (k + ∑ X, r X) * ((∏ X, mass X ^ M X) * t ^ (∑ X, M X) * ∏ X, ζ X ^ M X) := by
        rw [pow_add]
        ring
    _ ≤ 2 ^ N * P2 ^ (4 * k + s * (m / k)) * ∏ X, cf X ^ M X :=
        mul_le_mul (mul_le_mul_of_nonneg_left hP (by positivity)) hchain hst
          (mul_nonneg (by positivity) (pow_nonneg hP0 _))

end DGS
