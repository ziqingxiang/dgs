module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Algebra.Order.Field.GeomSum

@[expose] public section

open Finset Polynomial

namespace DGS

section Valuations

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_intCast_alg (z : ℤ) : ‖(z : PadicAlgCl p)‖ = ‖(z : ℚ_[p])‖ := by
  have h := PadicAlgCl.norm_extends p (z : ℚ_[p])
  rw [map_intCast] at h
  exact h

theorem norm_intCast_alg_le_one (z : ℤ) : ‖(z : PadicAlgCl p)‖ ≤ 1 := by
  rw [norm_intCast_alg]
  exact Padic.norm_int_le_one z

theorem norm_intCast_alg_eq {z : ℤ} (hz : z ≠ 0) :
    ‖(z : PadicAlgCl p)‖ = (p : ℝ) ^ (-(padicValInt p z : ℤ)) := by
  rw [norm_intCast_alg, Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hz), Padic.valuation_intCast]

theorem dvd_of_norm_alg_lt {z : ℤ} {k : ℕ} (h : ‖(z : PadicAlgCl p)‖ < (p : ℝ) ^ (1 - (k : ℤ))) :
    (p : ℤ) ^ k ∣ z := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [← Padic.norm_int_le_pow_iff_dvd]
  by_cases hz : z = 0
  · rw [hz, Int.cast_zero, norm_zero]
    positivity
  rw [norm_intCast_alg_eq hz] at h
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hz), Padic.valuation_intCast]
  have h2 : -(padicValInt p z : ℤ) < 1 - k := (zpow_lt_zpow_iff_right₀ hp1).1 h
  exact zpow_le_zpow_right₀ hp1.le (by omega)

theorem norm_root_le_one {g : ℤ[X]} (hg : g.Monic) {γ : PadicAlgCl p}
    (hγ : (g.map (Int.castRingHom (PadicAlgCl p))).eval γ = 0) : ‖γ‖ ≤ 1 := by
  by_contra h
  push Not at h
  set G := g.map (Int.castRingHom (PadicAlgCl p)) with hG
  have hGm : G.Monic := hg.map _
  set j := G.natDegree with hj
  have hexp : G.eval γ = γ ^ j + ∑ k ∈ range j, G.coeff k * γ ^ k := by
    rw [eval_eq_sum_range, sum_range_succ, hGm.coeff_natDegree, one_mul, add_comm]
  rw [hexp] at hγ
  have hj0 : 0 < j := by
    by_contra hj0
    push Not at hj0
    have hj00 : j = 0 := by omega
    rw [hj00, pow_zero, range_zero, sum_empty, add_zero] at hγ
    exact one_ne_zero hγ
  have h1 : ‖∑ k ∈ range j, G.coeff k * γ ^ k‖ ≤ ‖γ‖ ^ (j - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro k hk
    rw [norm_mul, norm_pow]
    have hc : ‖G.coeff k‖ ≤ 1 := by
      rw [hG, coeff_map, eq_intCast]
      exact norm_intCast_alg_le_one _
    have hk' : k ≤ j - 1 := by
      have := mem_range.1 hk
      omega
    calc ‖G.coeff k‖ * ‖γ‖ ^ k ≤ 1 * ‖γ‖ ^ (j - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ h.le hk') (by positivity) zero_le_one
      _ = ‖γ‖ ^ (j - 1) := one_mul _
  have h2 : ‖γ ^ j‖ = ‖∑ k ∈ range j, G.coeff k * γ ^ k‖ := by
    rw [← norm_neg (∑ k ∈ range j, G.coeff k * γ ^ k), ← eq_neg_of_add_eq_zero_left hγ]
  rw [norm_pow] at h2
  have h3 : ‖γ‖ ^ (j - 1) < ‖γ‖ ^ j := pow_lt_pow_right₀ h (by omega)
  linarith

theorem card_le_of_pairwise_dvd {N q : ℕ} (_hq : 0 < q) {S : Finset ℕ} (hS : S ⊆ Icc 1 N)
    (hdvd : ∀ a ∈ S, ∀ b ∈ S, (q : ℤ) ∣ (a : ℤ) - b) : (S.card : ℝ) ≤ (N : ℝ) / q + 1 := by
  have hinj : Set.InjOn (fun a => a / q) S := by
    intro a ha b hb hab
    have hmod : b % q = a % q := Nat.modEq_iff_dvd.2 (hdvd a ha b hb)
    simp only at hab
    calc a = q * (a / q) + a % q := (Nat.div_add_mod a q).symm
      _ = q * (b / q) + b % q := by rw [hab, hmod]
      _ = b := Nat.div_add_mod b q
  have himg : S.image (fun a => a / q) ⊆ range (N / q + 1) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
    have : a ≤ N := (mem_Icc.1 (hS ha)).2
    exact mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right this))
  have h1 : S.card ≤ N / q + 1 := by
    rw [← card_image_of_injOn hinj]
    exact (card_le_card himg).trans (card_range _).le
  have h2 : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
  have h3 : (S.card : ℝ) ≤ ((N / q + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

theorem le_card_filter_lt {K : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hxK : x ≤ K) :
    x ≤ (((Icc 1 K).filter fun k : ℕ => (k : ℝ) - 1 < x).card : ℝ) := by
  set c := ⌈x⌉₊ with hc
  have hcK : c ≤ K := Nat.ceil_le.2 hxK
  have hsub : Icc 1 c ⊆ (Icc 1 K).filter fun k : ℕ => (k : ℝ) - 1 < x := by
    intro k hk
    rw [mem_Icc] at hk
    rw [mem_filter, mem_Icc]
    refine ⟨⟨hk.1, hk.2.trans hcK⟩, ?_⟩
    have h1 : (k : ℝ) ≤ c := by exact_mod_cast hk.2
    have h2 : (c : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
    linarith
  have h3 := card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h3
  have h4 : x ≤ c := Nat.le_ceil x
  have h5 : (c : ℝ) ≤ (((Icc 1 K).filter fun k : ℕ => (k : ℝ) - 1 < x).card : ℝ) := by exact_mod_cast h3
  linarith

theorem sum_geom_le (N K : ℕ) : ∑ k ∈ Icc 1 K, ((N : ℝ) / (p : ℝ) ^ k + 1) ≤ (N : ℝ) / (p - 1) + K := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hx0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hx1 : (1 : ℝ) / p < 1 := by rw [div_lt_one hp0]; exact hp1
  have hg : ∑ k ∈ Icc 1 K, ((1 : ℝ) / p) ^ k ≤ 1 / (p - 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    refine (geom_sum_Ico_le_of_lt_one hx0 hx1).trans (le_of_eq ?_)
    field_simp
  rw [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  have e : ∑ k ∈ Icc 1 K, (N : ℝ) / (p : ℝ) ^ k = N * ∑ k ∈ Icc 1 K, ((1 : ℝ) / p) ^ k := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [one_div_pow, mul_one_div]
  rw [e]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hg hN
  rw [mul_one_div] at this
  linarith

theorem lem_valuations {g : ℤ[X]} (hg : g.Monic) {N K : ℕ}
    (hN0 : ∀ a ∈ Icc 1 N, g.eval (a : ℤ) ≠ 0) (hK : ∀ a ∈ Icc 1 N, |g.eval (a : ℤ)| ≤ (p : ℤ) ^ K) :
    ∑ a ∈ Icc 1 N, (padicValInt p (g.eval (a : ℤ)) : ℝ) ≤ g.natDegree * ((N : ℝ) / (p - 1) + K) := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  set φ : ℤ →+* PadicAlgCl p := Int.castRingHom (PadicAlgCl p) with hφ
  set G := g.map φ with hG
  have hGm : G.Monic := hg.map φ
  have hspl : G.Splits := IsAlgClosed.splits G
  set s := G.roots with hs
  have hcard : Multiset.card s = g.natDegree := by
    rw [← hspl.natDegree_eq_card_roots, hG, hg.natDegree_map]
  have hprod : G = (s.map fun γ => X - C γ).prod := hspl.eq_prod_roots_of_monic hGm
  have heval : ∀ a : ℤ, ((g.eval a : ℤ) : PadicAlgCl p) = (s.map fun γ => (a : PadicAlgCl p) - γ).prod := by
    intro a
    have h1 : G.eval (a : PadicAlgCl p) = φ (g.eval a) := eval_intCast_map φ g a
    rw [hφ, eq_intCast] at h1
    rw [← h1, hprod, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun γ _ => ?_
    simp
  have hroot : ∀ γ ∈ s, ‖γ‖ ≤ 1 := fun γ hγ => norm_root_le_one hg ((mem_roots hGm.ne_zero).1 hγ)
  have hdist1 : ∀ (a : ℤ), ∀ γ ∈ s, ‖(a : PadicAlgCl p) - γ‖ ≤ 1 := by
    intro a γ hγ
    calc ‖(a : PadicAlgCl p) - γ‖ = ‖(a : PadicAlgCl p) + (-γ)‖ := by rw [sub_eq_add_neg]
      _ ≤ max ‖(a : PadicAlgCl p)‖ ‖-γ‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (norm_intCast_alg_le_one a) (by rw [norm_neg]; exact hroot γ hγ)
  have hfac : ∀ a ∈ Icc 1 N, ∀ γ ∈ s, 0 < ‖(((a : ℕ) : ℤ) : PadicAlgCl p) - γ‖ := by
    intro a ha γ hγ
    rw [norm_pos_iff]
    intro h0
    have h1 := heval a
    rw [Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨γ, hγ, h0⟩)] at h1
    exact hN0 a ha (by exact_mod_cast h1)
  set f : PadicAlgCl p → ℕ → ℝ := fun γ a => -Real.log ‖(((a : ℕ) : ℤ) : PadicAlgCl p) - γ‖ / Real.log p
    with hf
  have hf0 : ∀ a ∈ Icc 1 N, ∀ γ ∈ s, 0 ≤ f γ a := by
    intro a ha γ hγ
    simp only [hf]
    apply div_nonneg _ hlogp.le
    have := Real.log_nonpos (norm_nonneg _) (hdist1 a γ hγ)
    linarith
  have hsumf : ∀ a ∈ Icc 1 N, (s.map fun γ => f γ a).sum = padicValInt p (g.eval (a : ℤ)) := by
    intro a ha
    have hn := congrArg norm (heval a)
    rw [Multiset.norm_prod_map, norm_intCast_alg_eq (hN0 a ha)] at hn
    have hl := congrArg Real.log hn
    rw [Real.log_zpow, Real.log_multiset_prod (fun x hx => by
      obtain ⟨γ, hγ, rfl⟩ := Multiset.mem_map.1 hx
      exact (hfac a ha γ hγ).ne'), Multiset.map_map] at hl
    have e1 : (fun γ => f γ a) = fun γ => Real.log ‖(((a : ℕ) : ℤ) : PadicAlgCl p) - γ‖ * (-(Real.log p)⁻¹) := by
      funext γ
      simp only [hf]
      ring
    rw [e1, Multiset.sum_map_mul_right]
    have e2 : (s.map fun γ => Real.log ‖(((a : ℕ) : ℤ) : PadicAlgCl p) - γ‖).sum =
        ((-(padicValInt p (g.eval (a : ℤ)) : ℤ) : ℤ) : ℝ) * Real.log p := by
      rw [hl]
      rfl
    rw [e2]
    field_simp
    push_cast
    ring
  have hvK : ∀ a ∈ Icc 1 N, (padicValInt p (g.eval (a : ℤ)) : ℝ) ≤ K := by
    intro a ha
    have hdvd : (p : ℤ) ^ padicValInt p (g.eval (a : ℤ)) ∣ g.eval (a : ℤ) := padicValInt_dvd _
    have hle : (p : ℤ) ^ padicValInt p (g.eval (a : ℤ)) ≤ |g.eval (a : ℤ)| :=
      Int.le_of_dvd (abs_pos.2 (hN0 a ha)) ((dvd_abs _ _).2 hdvd)
    have h2 : (p : ℤ) ^ padicValInt p (g.eval (a : ℤ)) ≤ (p : ℤ) ^ K := hle.trans (hK a ha)
    have h3 : p ^ padicValInt p (g.eval (a : ℤ)) ≤ p ^ K := by exact_mod_cast h2
    have h4 : padicValInt p (g.eval (a : ℤ)) ≤ K := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 h3
    exact_mod_cast h4
  have hfK : ∀ a ∈ Icc 1 N, ∀ γ ∈ s, f γ a ≤ K := by
    intro a ha γ hγ
    have h1 : f γ a ≤ (s.map fun γ' => f γ' a).sum :=
      Multiset.single_le_sum (fun x hx => by
        obtain ⟨γ', hγ', rfl⟩ := Multiset.mem_map.1 hx
        exact hf0 a ha γ' hγ') _ (Multiset.mem_map_of_mem _ hγ)
    rw [hsumf a ha] at h1
    exact h1.trans (hvK a ha)
  have hcount : ∀ γ ∈ s, ∀ k ∈ Icc 1 K,
      (((Icc 1 N).filter fun a => (k : ℝ) - 1 < f γ a).card : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ k + 1 := by
    intro γ hγ k hk
    have hsmall : ∀ a ∈ (Icc 1 N).filter (fun a => (k : ℝ) - 1 < f γ a),
        ‖(((a : ℕ) : ℤ) : PadicAlgCl p) - γ‖ < (p : ℝ) ^ (1 - (k : ℤ)) := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := mem_filter.1 ha
      have hc := hfac a ha1 γ hγ
      simp only [hf] at ha2
      rw [lt_div_iff₀ hlogp] at ha2
      have h1 : Real.log ‖(((a : ℕ) : ℤ) : PadicAlgCl p) - γ‖ < (1 - (k : ℝ)) * Real.log p := by linarith
      have h2 : (p : ℝ) ^ (1 - (k : ℤ)) = Real.exp ((1 - (k : ℝ)) * Real.log p) := by
        rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by linarith)]
        push_cast
        ring_nf
      rw [h2, ← Real.exp_log hc]
      exact Real.exp_lt_exp.2 h1
    have hq : 0 < p ^ k := pow_pos hp.out.pos k
    have h := card_le_of_pairwise_dvd hq (filter_subset _ _) (fun a ha b hb => by
      have h1 := hsmall a ha
      have h2 := hsmall b hb
      have h3 : ‖((((a : ℤ) - b : ℤ)) : PadicAlgCl p)‖ < (p : ℝ) ^ (1 - (k : ℤ)) := by
        have e : ((((a : ℤ) - b : ℤ)) : PadicAlgCl p) =
            ((((a : ℕ) : ℤ) : PadicAlgCl p) - γ) + (-((((b : ℕ) : ℤ) : PadicAlgCl p) - γ)) := by
          push_cast
          ring
        rw [e]
        calc _ ≤ max ‖(((a : ℕ) : ℤ) : PadicAlgCl p) - γ‖ ‖-((((b : ℕ) : ℤ) : PadicAlgCl p) - γ)‖ :=
              IsUltrametricDist.norm_add_le_max _ _
          _ < (p : ℝ) ^ (1 - (k : ℤ)) := by
              rw [norm_neg]
              exact max_lt h1 h2
      have := dvd_of_norm_alg_lt h3
      exact_mod_cast this)
    push_cast at h
    exact h
  have hper : ∀ γ ∈ s, ∑ a ∈ Icc 1 N, f γ a ≤ (N : ℝ) / (p - 1) + K := by
    intro γ hγ
    calc ∑ a ∈ Icc 1 N, f γ a
        ≤ ∑ a ∈ Icc 1 N, (((Icc 1 K).filter fun k : ℕ => (k : ℝ) - 1 < f γ a).card : ℝ) :=
          sum_le_sum fun a ha => le_card_filter_lt (hf0 a ha γ hγ) (hfK a ha γ hγ)
      _ = ∑ k ∈ Icc 1 K, (((Icc 1 N).filter fun a => (k : ℝ) - 1 < f γ a).card : ℝ) := by
          simp only [card_filter]
          push_cast
          exact sum_comm
      _ ≤ ∑ k ∈ Icc 1 K, ((N : ℝ) / (p : ℝ) ^ k + 1) := sum_le_sum fun k hk => hcount γ hγ k hk
      _ ≤ (N : ℝ) / (p - 1) + K := sum_geom_le N K
  have hswap : ∑ a ∈ Icc 1 N, (s.map fun γ => f γ a).sum = (s.map fun γ => ∑ a ∈ Icc 1 N, f γ a).sum := by
    simp only [Finset.sum_eq_multiset_sum]
    exact Multiset.sum_map_sum_map _ _
  calc ∑ a ∈ Icc 1 N, (padicValInt p (g.eval (a : ℤ)) : ℝ)
      = ∑ a ∈ Icc 1 N, (s.map fun γ => f γ a).sum := sum_congr rfl fun a ha => (hsumf a ha).symm
    _ = (s.map fun γ => ∑ a ∈ Icc 1 N, f γ a).sum := hswap
    _ ≤ (s.map fun _ => (N : ℝ) / (p - 1) + K).sum := Multiset.sum_map_le_sum_map _ _ hper
    _ = g.natDegree * ((N : ℝ) / (p - 1) + K) := by
        rw [Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul]

end Valuations

end DGS
