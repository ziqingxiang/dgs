module

public import DGS.S08_Two.KrylovLaw

@[expose] public section

open Polynomial

namespace DGS

variable {β : (ZMod 2)[X]}

theorem monic_X_pow_sub_polyOfFin {k : ℕ} (c : Fin k → ZMod 2) :
    (X ^ k - polyOfFin c).Monic :=
  monic_X_pow_sub (degree_polyOfFin_lt c)

theorem natDegree_X_pow_sub_polyOfFin {k : ℕ} (c : Fin k → ZMod 2) :
    (X ^ k - polyOfFin c).natDegree = k := by
  have h := degree_sub_eq_left_of_degree_lt (p := (X : (ZMod 2)[X]) ^ k) (q := polyOfFin c)
    (by rw [degree_X_pow]; exact degree_polyOfFin_lt c)
  rw [degree_X_pow] at h
  exact natDegree_eq_of_degree_eq_some h

theorem polyOfFin_injective {k : ℕ} : Function.Injective (polyOfFin (R := ZMod 2) (k := k)) := by
  intro c c' h
  funext i
  have := congrArg (coeff · (i : ℕ)) h
  simp only [coeff_polyOfFin, dite_eq_left i.2] at this
  exact this

theorem eq_of_monic_of_coeff_eq {p q : (ZMod 2)[X]} {m : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpm : p.natDegree = m) (hqm : q.natDegree = m) (h : ∀ j < m, p.coeff j = q.coeff j) : p = q := by
  ext j
  rcases lt_trichotomy j m with hj | rfl | hj
  · exact h j hj
  · rw [← hpm, hp.coeff_natDegree, hpm, ← hqm, hq.coeff_natDegree]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

variable (hβm : β.Monic)
include hβm

theorem quot_spec {g : (ZMod 2)[X]} (hg : g.Monic) (h : β ∣ g) :
    β * (g /ₘ β) = g ∧ (g /ₘ β).Monic ∧ (g /ₘ β).natDegree = g.natDegree - β.natDegree := by
  have hmul : β * (g /ₘ β) = g := by
    have := modByMonic_add_div g β
    rwa [(modByMonic_eq_zero_iff_dvd hβm).2 h, zero_add] at this
  have hq0 : g /ₘ β ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact hg.ne_zero hmul.symm
  refine ⟨hmul, hβm.of_mul_monic_left (by rw [hmul]; exact hg), ?_⟩
  have := congrArg natDegree hmul
  rw [natDegree_mul hβm.ne_zero hq0] at this
  omega

theorem card_dvd_even (k : ℕ) :
    Nat.card {c : Fin k → ZMod 2 // β ∣ X ^ k - polyOfFin c} * 2 ^ β.natDegree ≤ 2 ^ k := by
  set d := β.natDegree with hd
  by_cases hkd : k < d
  · have : IsEmpty {c : Fin k → ZMod 2 // β ∣ X ^ k - polyOfFin c} := by
      refine ⟨fun c => ?_⟩
      have h1 := natDegree_le_of_dvd c.2 (monic_X_pow_sub_polyOfFin c.1).ne_zero
      rw [natDegree_X_pow_sub_polyOfFin] at h1
      omega
    rw [Nat.card_of_isEmpty, zero_mul]
    exact Nat.zero_le _
  push Not at hkd
  have hinj : Function.Injective fun c : {c : Fin k → ZMod 2 // β ∣ X ^ k - polyOfFin c} =>
      fun j : Fin (k - d) => ((X ^ k - polyOfFin c.1) /ₘ β).coeff j := by
    intro c c' h
    obtain ⟨h1, h2, h3⟩ := quot_spec hβm (monic_X_pow_sub_polyOfFin c.1) c.2
    obtain ⟨h1', h2', h3'⟩ := quot_spec hβm (monic_X_pow_sub_polyOfFin c'.1) c'.2
    rw [natDegree_X_pow_sub_polyOfFin] at h3 h3'
    have hq : (X ^ k - polyOfFin c.1) /ₘ β = (X ^ k - polyOfFin c'.1) /ₘ β := by
      refine eq_of_monic_of_coeff_eq h2 h2' h3 h3' fun j hj => ?_
      exact congrFun h ⟨j, hj⟩
    have : polyOfFin c.1 = polyOfFin c'.1 := by
      have e : β * ((X ^ k - polyOfFin c.1) /ₘ β) = β * ((X ^ k - polyOfFin c'.1) /ₘ β) := by
        rw [hq]
      rw [h1, h1'] at e
      exact sub_right_injective e
    exact Subtype.ext (polyOfFin_injective this)
  have hle := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (Fin (k - d) → ZMod 2) = 2 ^ (k - d) := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin (k - d)), Fintype.card_fin]
  rw [h2] at hle
  calc Nat.card {c : Fin k → ZMod 2 // β ∣ X ^ k - polyOfFin c} * 2 ^ d ≤ 2 ^ (k - d) * 2 ^ d :=
        Nat.mul_le_mul_right _ hle
    _ = 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel hkd]

theorem card_dvd_odd (hβ : Irreducible β) (hβX : β ≠ X) {k : ℕ} (hk : 0 < k) :
    Nat.card {c : Fin k → ZMod 2 // c ⟨0, hk⟩ = 0 ∧ β ∣ X ^ k - polyOfFin c} * 2 ^ β.natDegree ≤
      2 ^ (k - 1) := by
  set d := β.natDegree with hd
  have hXβ : ¬ X ∣ β := by
    intro h
    exact hβX (eq_of_monic_of_associated hβm monic_X
      (associated_of_dvd_dvd (irreducible_X.dvd_symm hβ h) h))
  have hX : ∀ c : Fin k → ZMod 2, c ⟨0, hk⟩ = 0 → X ∣ X ^ k - polyOfFin c := by
    intro c hc
    rw [X_dvd_iff, coeff_sub, coeff_X_pow, ite_eq_right (by omega), coeff_polyOfFin, dite_eq_left hk, hc,
      sub_zero]
  have hβX' : ∀ c : Fin k → ZMod 2, c ⟨0, hk⟩ = 0 → β ∣ X ^ k - polyOfFin c →
      X ∣ (X ^ k - polyOfFin c) /ₘ β := by
    intro c hc hdvd
    have h1 := (quot_spec hβm (monic_X_pow_sub_polyOfFin c) hdvd).1
    have h2 := hX c hc
    rw [← h1] at h2
    exact (prime_X.dvd_or_dvd h2).resolve_left hXβ
  by_cases hkd : k < d + 1
  · have : IsEmpty {c : Fin k → ZMod 2 // c ⟨0, hk⟩ = 0 ∧ β ∣ X ^ k - polyOfFin c} := by
      refine ⟨fun c => ?_⟩
      obtain ⟨h1, h2, h3⟩ := quot_spec hβm (monic_X_pow_sub_polyOfFin c.1) c.2.2
      have hXq := hβX' c.1 c.2.1 c.2.2
      have hq0 : (X ^ k - polyOfFin c.1) /ₘ β ≠ 0 := h2.ne_zero
      have := natDegree_le_of_dvd hXq hq0
      rw [natDegree_X, h3, natDegree_X_pow_sub_polyOfFin] at this
      omega
    rw [Nat.card_of_isEmpty, zero_mul]
    exact Nat.zero_le _
  push Not at hkd
  have hinj : Function.Injective
      fun c : {c : Fin k → ZMod 2 // c ⟨0, hk⟩ = 0 ∧ β ∣ X ^ k - polyOfFin c} =>
        fun j : Fin (k - d - 1) => ((X ^ k - polyOfFin c.1) /ₘ β).coeff (j + 1) := by
    intro c c' h
    obtain ⟨h1, h2, h3⟩ := quot_spec hβm (monic_X_pow_sub_polyOfFin c.1) c.2.2
    obtain ⟨h1', h2', h3'⟩ := quot_spec hβm (monic_X_pow_sub_polyOfFin c'.1) c'.2.2
    rw [natDegree_X_pow_sub_polyOfFin] at h3 h3'
    have hq : (X ^ k - polyOfFin c.1) /ₘ β = (X ^ k - polyOfFin c'.1) /ₘ β := by
      refine eq_of_monic_of_coeff_eq h2 h2' h3 h3' fun j hj => ?_
      rcases j with - | j
      · have e1 := X_dvd_iff.1 (hβX' c.1 c.2.1 c.2.2)
        have e2 := X_dvd_iff.1 (hβX' c'.1 c'.2.1 c'.2.2)
        rw [e1, e2]
      · exact congrFun h ⟨j, by omega⟩
    have : polyOfFin c.1 = polyOfFin c'.1 := by
      have e : β * ((X ^ k - polyOfFin c.1) /ₘ β) = β * ((X ^ k - polyOfFin c'.1) /ₘ β) := by
        rw [hq]
      rw [h1, h1'] at e
      exact sub_right_injective e
    exact Subtype.ext (polyOfFin_injective this)
  have hle := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (Fin (k - d - 1) → ZMod 2) = 2 ^ (k - d - 1) := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin (k - d - 1)),
      Fintype.card_fin]
  rw [h2] at hle
  calc Nat.card {c : Fin k → ZMod 2 // c ⟨0, hk⟩ = 0 ∧ β ∣ X ^ k - polyOfFin c} * 2 ^ d
      ≤ 2 ^ (k - d - 1) * 2 ^ d := Nat.mul_le_mul_right _ hle
    _ = 2 ^ (k - 1) := by rw [← pow_add]; congr 1; omega

end DGS
