module

public import DGS.S10_Tools.LittlewoodOfford
public import DGS.S10_Tools.SeqExp
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

open Finset Matrix
open scoped Real

namespace DGS

variable {m t : ℕ}

section Order

variable (B : Fin t → Finset (Fin m))

open Classical in
noncomputable def blockKey (j : Fin m) : ℕ :=
  if h : ∃ c, j ∈ B c then t - ((Classical.choose h : Fin t) : ℕ) else 0

noncomputable def seqKey (j : Fin m) : ℕ := blockKey B j * m + j.val

noncomputable def seqPerm : Equiv.Perm (Fin m) := Tuple.sort (seqKey B)

variable {B}

theorem blockKey_of_mem (hdisj : Pairwise fun c c' => Disjoint (B c) (B c')) {j : Fin m} {c : Fin t}
    (hj : j ∈ B c) : blockKey B j = t - c := by
  have h : ∃ c, j ∈ B c := ⟨c, hj⟩
  rw [blockKey, dite_eq_left h]
  by_cases hcc : Classical.choose h = c
  · rw [hcc]
  · exact absurd hj (Finset.disjoint_left.1 (hdisj hcc) (Classical.choose_spec h))

theorem exists_mem_of_blockKey_pos {j : Fin m} (hj : 0 < blockKey B j) : ∃ c, j ∈ B c := by
  by_contra h
  rw [blockKey, dite_eq_right h] at hj
  exact lt_irrefl 0 hj

theorem seqKey_lt_of_blockKey_lt {x y : Fin m} (h : blockKey B x < blockKey B y) :
    seqKey B x < seqKey B y := by
  unfold seqKey
  have hx := x.2
  calc blockKey B x * m + x.val < blockKey B x * m + m := by omega
    _ = (blockKey B x + 1) * m := by ring
    _ ≤ blockKey B y * m := Nat.mul_le_mul_right _ h
    _ ≤ blockKey B y * m + y.val := Nat.le_add_right _ _

theorem seqKey_injective : Function.Injective (seqKey B) := by
  intro x y h
  unfold seqKey at h
  have h1 : (blockKey B x * m + x.val) % m = x.val := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt x.2]
  have h2 : (blockKey B y * m + y.val) % m = y.val := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt y.2]
  apply Fin.ext
  rw [← h1, ← h2, h]

theorem seqKey_seqPerm_strictMono : StrictMono (seqKey B ∘ seqPerm B) :=
  (Tuple.monotone_sort (seqKey B)).strictMono_of_injective
    (seqKey_injective.comp (seqPerm B).injective)

theorem blocks_after {d : ℕ} (hdisj : Pairwise fun c c' => Disjoint (B c) (B c'))
    (hcard : ∀ c, (B c).card = d) (i : Fin m) (c : Fin t) (hc : ((c : ℕ) + 1) * d ≤ m - 1 - i) :
    ∀ x ∈ B c, i < (seqPerm B).symm x := by
  intro x hx
  by_contra hle
  push Not at hle
  have hd : 1 ≤ d := by
    rw [← hcard c]
    exact card_pos.2 ⟨x, hx⟩
  have hmono := seqKey_seqPerm_strictMono (B := B)
  have hkx : seqKey B x ≤ seqKey B (seqPerm B i) := by
    have := hmono.monotone hle
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using this
  set T := ((Iic c).biUnion B).erase x with hT
  have hmaps : Set.MapsTo (seqPerm B) (Ioi i : Finset (Fin m)) (T : Set (Fin m)) := by
    intro j' hj'
    have hij : i < j' := mem_Ioi.1 (Finset.mem_coe.1 hj')
    have hk : seqKey B x < seqKey B (seqPerm B j') := lt_of_le_of_lt hkx (hmono hij)
    have hb : blockKey B x ≤ blockKey B (seqPerm B j') := by
      by_contra hb
      push Not at hb
      exact absurd (seqKey_lt_of_blockKey_lt hb) (not_lt.2 hk.le)
    rw [blockKey_of_mem hdisj hx] at hb
    have hpos : 0 < blockKey B (seqPerm B j') := by
      have := c.2
      omega
    obtain ⟨c', hc'⟩ := exists_mem_of_blockKey_pos hpos
    rw [blockKey_of_mem hdisj hc'] at hb
    have hcc' : c' ≤ c := by
      rw [Fin.le_iff_val_le_val]
      have := c'.2
      have := c.2
      omega
    rw [Finset.mem_coe, hT, mem_erase]
    refine ⟨fun h => ?_, mem_biUnion.2 ⟨c', mem_Iic.2 hcc', hc'⟩⟩
    rw [h] at hk
    exact lt_irrefl _ hk
  have h1 := card_le_card_of_injOn (seqPerm B) hmaps (seqPerm B).injective.injOn
  rw [Fin.card_Ioi] at h1
  set D := ((c : ℕ) + 1) * d with hD
  have h2 : T.card ≤ D - 1 := by
    rw [hT, card_erase_of_mem (mem_biUnion.2 ⟨c, mem_Iic.2 le_rfl, hx⟩)]
    have h3 := card_biUnion_le (s := Iic c) (t := B)
    rw [sum_congr rfl fun c' _ => hcard c', sum_const, Fin.card_Iic, smul_eq_mul] at h3
    omega
  have h4 : 1 ≤ D := Nat.mul_pos (Nat.succ_pos _) hd
  omega

end Order

variable {p : ℕ} [Fact p.Prime]

noncomputable def etaRow (p d t r : ℕ) : ℝ :=
  if 2 ≤ min t (r / d) then (1 / p + 1 / √(π * ((min t (r / d) / 2 : ℕ) : ℝ))) ^ d else 1

theorem etaRow_nonneg (p d t r : ℕ) : 0 ≤ etaRow p d t r := by
  unfold etaRow
  split_ifs
  · positivity
  · exact zero_le_one

theorem row_bound (hp2 : p ≠ 2) {d : ℕ} {B : Fin t → Finset (Fin m)}
    (hdisj : Pairwise fun c c' => Disjoint (B c) (B c')) (hcard : ∀ c, (B c).card = d)
    (φ : Fin m → Fin d → ZMod p) (hspan : ∀ c, Submodule.span (ZMod p) (φ '' (B c : Set (Fin m))) = ⊤)
    (i : Fin m) (hr : 2 ≤ min t ((m - 1 - i) / d)) :
    rhoG (fun j : {j : Fin m // i < j} => φ (seqPerm B j)) ≤
      (1 / p + 1 / √(π * ((min t ((m - 1 - i) / d) / 2 : ℕ) : ℝ))) ^ d := by
  set s := min t ((m - 1 - i) / d) with hs
  have hst : s ≤ t := min_le_left _ _
  have hsr : s ≤ (m - 1 - i) / d := min_le_right _ _
  set σ := seqPerm B with hσ
  let c0 : Fin s → Fin t := fun c => ⟨c, lt_of_lt_of_le c.2 hst⟩
  let B' : Fin s → Finset {j : Fin m // i < j} := fun c => univ.filter fun j => σ j.1 ∈ B (c0 c)
  have hafter : ∀ c : Fin s, ∀ x ∈ B (c0 c), i < σ.symm x := by
    intro c
    apply blocks_after hdisj hcard i (c0 c)
    have h1 : (c : ℕ) + 1 ≤ (m - 1 - i) / d := by
      have := c.2
      omega
    calc ((c0 c : ℕ) + 1) * d = ((c : ℕ) + 1) * d := rfl
      _ ≤ (m - 1 - i) / d * d := Nat.mul_le_mul_right _ h1
      _ ≤ m - 1 - i := Nat.div_mul_le_self _ _
  have hdisj' : Pairwise fun c c' => Disjoint (B' c) (B' c') := by
    intro c c' hcc'
    have hne : c0 c ≠ c0 c' := fun h => hcc' (Fin.ext (by simpa [c0] using congrArg Fin.val h))
    refine Finset.disjoint_left.2 fun j hj hj' => ?_
    exact Finset.disjoint_left.1 (hdisj hne) (mem_filter.1 hj).2 (mem_filter.1 hj').2
  have hcard' : ∀ c, (B' c).card = d := by
    intro c
    rw [← hcard (c0 c)]
    refine Finset.card_bij' (fun j _ => σ j.1) (fun x hx => ⟨σ.symm x, hafter c x hx⟩)
      (fun j hj => (mem_filter.1 hj).2) (fun x hx => ?_) (fun j _ => ?_) (fun x _ => ?_)
    · simp only [B', mem_filter, mem_univ, true_and, Equiv.apply_symm_apply]
      exact hx
    · apply Subtype.ext
      simp
    · simp
  have hspan' : ∀ c, Submodule.span (ZMod p)
      ((fun j : {j : Fin m // i < j} => φ (σ j)) '' (B' c : Set {j : Fin m // i < j})) = ⊤ := by
    intro c
    rw [eq_top_iff, ← hspan (c0 c)]
    apply Submodule.span_mono
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨σ.symm x, hafter c x hx⟩, ?_, by simp⟩
    simp only [B', Finset.coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Equiv.apply_symm_apply]
    exact hx
  have h := lem_LObases_a hp2 hr (fun j : {j : Fin m // i < j} => φ (σ j)) B' hdisj' hcard' hspan'
  exact h.1.trans h.2

theorem seqbases_prod (hp2 : p ≠ 2) {d : ℕ} (B : Fin t → Finset (Fin m))
    (hdisj : Pairwise fun c c' => Disjoint (B c) (B c')) (hcard : ∀ c, (B c).card = d)
    (φ Y : Fin m → Fin d → ZMod p)
    (hspan : ∀ c, Submodule.span (ZMod p) (φ '' (B c : Set (Fin m))) = ⊤) :
    prob (fun ω : Pairs m → Bool => ∀ i, ∑ j, seidelOf ω i j • φ j = Y i) ≤
      ∏ r ∈ range m, etaRow p d t r := by
  refine (lem_seqexp_perm φ Y (seqPerm B)).trans ?_
  calc ∏ i : Fin m, rhoG (fun j : {j : Fin m // i < j} => φ (seqPerm B j))
      ≤ ∏ i : Fin m, etaRow p d t (m - 1 - i) := by
        refine prod_le_prod₀ (fun i _ => rhoG_nonneg _) fun i _ => ?_
        unfold etaRow
        split_ifs with hr
        · exact row_bound hp2 hdisj hcard φ hspan i hr
        · exact rhoG_le_one _
    _ = ∏ r ∈ range m, etaRow p d t r := by
        rw [← Fin.prod_univ_eq_prod_range]
        refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
        show etaRow p d t (m - 1 - i) = etaRow p d t ((Fin.rev i : Fin m) : ℕ)
        rw [Fin.val_rev]
        congr 1
        omega

theorem sum_inv_sqrt_le (N : ℕ) : ∑ u ∈ range N, 1 / √((u : ℝ) + 1) ≤ 2 * √(N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have h1 : 1 / √((N : ℝ) + 1) ≤ 2 * √((N : ℝ) + 1) - 2 * √(N : ℝ) := by
      have ha : 0 < √((N : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
      have hsq : √((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have hsq' : √(N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
      rw [div_le_iff₀ ha]
      nlinarith [sq_nonneg (√((N : ℝ) + 1) - √(N : ℝ))]
    push_cast
    linarith

theorem two_sqrt_two_div_sqrt_pi_le : 2 * √2 / √π ≤ 1.6 := by
  rw [div_le_iff₀ (Real.sqrt_pos.2 Real.pi_pos)]
  have h8 : 2 * √2 = √8 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h16 : 1.6 * √π = √(1.6 ^ 2 * π) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h8, h16]
  apply Real.sqrt_le_sqrt
  have := Real.pi_gt_d2
  nlinarith

omit [Fact (Nat.Prime p)] in
theorem seqbases_numeric {d : ℕ} (hp : 0 < p) (hd : 1 ≤ d) (ht : 2 ≤ t) (hdt : d * t ≤ m) :
    ∏ r ∈ range m, etaRow p d t r ≤
      ((p : ℝ) ^ (d * m))⁻¹ * (1 + p / √(π * ((t / 2 : ℕ) : ℝ))) ^ (d * m) *
        Real.exp (1.6 * d ^ 2 * p * √(t : ℝ)) * (p : ℝ) ^ (2 * d ^ 2) := by
  have hP0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hd0 : 0 < d := hd
  have hA1 : ∀ s : ℕ, 1 ≤ 1 + (p : ℝ) / √(π * ((s / 2 : ℕ) : ℝ)) := fun s => by
    have : 0 ≤ (p : ℝ) / √(π * ((s / 2 : ℕ) : ℝ)) := div_nonneg hP0.le (Real.sqrt_nonneg _)
    linarith
  have hetaA : ∀ s : ℕ, (1 / (p : ℝ) + 1 / √(π * ((s / 2 : ℕ) : ℝ))) ^ d =
      ((p : ℝ) ^ d)⁻¹ * (1 + (p : ℝ) / √(π * ((s / 2 : ℕ) : ℝ))) ^ d := by
    intro s
    rw [← inv_pow, ← mul_pow]
    congr 1
    rw [mul_add, mul_one, mul_div_assoc', inv_mul_cancel₀ hP0.ne', one_div]
  set c : ℝ := d * p * √(2 * d) / √π with hc
  have hc0 : 0 ≤ c := by positivity
  set e : ℕ → ℝ := fun r =>
    if 2 * d ≤ r ∧ r < d * t then c / √((r : ℝ) + 1 - 2 * d) else 0 with he
  have hfac : ∀ r ∈ range m, etaRow p d t r ≤ ((p : ℝ) ^ d)⁻¹ *
      ((if r < 2 * d then (p : ℝ) ^ d else 1) * Real.exp (e r) *
        (if d * t ≤ r then (1 + (p : ℝ) / √(π * ((t / 2 : ℕ) : ℝ))) ^ d else 1)) := by
    intro r _
    unfold etaRow
    by_cases h1 : r < 2 * d
    · have hmin : ¬ 2 ≤ min t (r / d) := by
        intro h
        have h2 : 2 ≤ r / d := le_trans h (min_le_right _ _)
        have := (Nat.le_div_iff_mul_le hd0).1 h2
        omega
      have he0 : e r = 0 := by
        simp only [he]
        rw [ite_eq_right (by omega)]
      rw [ite_eq_right hmin, ite_eq_left h1, ite_eq_right (by nlinarith : ¬ d * t ≤ r), he0, Real.exp_zero, mul_one,
        mul_one, inv_mul_cancel₀ (by positivity)]
    · push Not at h1
      by_cases h3 : d * t ≤ r
      · have hmin : min t (r / d) = t :=
          min_eq_left ((Nat.le_div_iff_mul_le hd0).2 (by rw [mul_comm]; exact h3))
        have he0 : e r = 0 := by
          simp only [he]
          rw [ite_eq_right (by omega)]
        rw [hmin, ite_eq_left ht, ite_eq_right (by omega), ite_eq_left h3, he0, Real.exp_zero, one_mul, one_mul,
          hetaA]
      · push Not at h3
        have hlt : r / d < t := (Nat.div_lt_iff_lt_mul hd0).2 (by rw [mul_comm]; exact h3)
        have hmin : min t (r / d) = r / d := min_eq_right hlt.le
        have h2 : 2 ≤ r / d := (Nat.le_div_iff_mul_le hd0).2 (by omega)
        have he1 : e r = c / √((r : ℝ) + 1 - 2 * d) := by
          simp only [he]
          rw [ite_eq_left ⟨h1, h3⟩]
        rw [hmin, ite_eq_left h2, ite_eq_right (by omega), ite_eq_right (by omega), one_mul, mul_one, hetaA, he1]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [Nat.div_div_eq_div_mul]
        set Q : ℝ := ((r / (d * 2) : ℕ) : ℝ) with hQdef
        set R : ℝ := (r : ℝ) + 1 - 2 * d with hRdef
        have hq : r < r / (d * 2) * (d * 2) + d * 2 := Nat.lt_div_mul_add (by omega)
        have hq' : (r : ℝ) + 1 ≤ Q * (d * 2) + d * 2 := by
          have := Nat.lt_iff_add_one_le.1 hq
          rw [hQdef]
          exact_mod_cast this
        have hQ1 : (1 : ℝ) ≤ Q := by
          rw [hQdef]
          exact_mod_cast (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
        have hR0 : 0 < R := by
          have : (2 * d : ℝ) ≤ r := by exact_mod_cast h1
          rw [hRdef]
          linarith
        have hRQ : R ≤ 2 * d * Q := by
          rw [hRdef]
          linarith
        calc (1 + (p : ℝ) / √(π * Q)) ^ d ≤ Real.exp ((p : ℝ) / √(π * Q)) ^ d := by
              apply pow_le_pow_left₀ (by positivity)
              linarith [Real.add_one_le_exp ((p : ℝ) / √(π * Q))]
          _ = Real.exp (d * ((p : ℝ) / √(π * Q))) := by rw [← Real.exp_nat_mul]
          _ ≤ Real.exp (c / √R) := by
              apply Real.exp_le_exp.2
              have hsQ : 0 < √Q := Real.sqrt_pos.2 (by linarith)
              have hsR : 0 < √R := Real.sqrt_pos.2 hR0
              have key : 1 / √Q ≤ √(2 * d) / √R := by
                rw [div_le_div_iff₀ hsQ hsR, one_mul, ← Real.sqrt_mul (by positivity)]
                exact Real.sqrt_le_sqrt hRQ
              have e1 : (d : ℝ) * ((p : ℝ) / √(π * Q)) = (d * p / √π) * (1 / √Q) := by
                rw [Real.sqrt_mul Real.pi_pos.le]
                field_simp
              have e2 : c / √R = (d * p / √π) * (√(2 * d) / √R) := by
                rw [hc]
                field_simp
              rw [e1, e2]
              exact mul_le_mul_of_nonneg_left key (by positivity)
  have hsum : ∑ r ∈ range m, e r ≤ 1.6 * d ^ 2 * p * √(t : ℝ) := by
    have h1 : ∑ r ∈ range m, e r = ∑ r ∈ Ico (2 * d) (d * t), c / √((r : ℝ) + 1 - 2 * d) := by
      simp only [he]
      rw [← Finset.sum_filter]
      congr 1
      ext r
      simp only [mem_filter, mem_range, mem_Ico]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · rintro h
        exact ⟨by omega, h⟩
    have h2 : ∑ r ∈ Ico (2 * d) (d * t), c / √((r : ℝ) + 1 - 2 * d) =
        c * ∑ u ∈ range (d * t - 2 * d), 1 / √((u : ℝ) + 1) := by
      rw [Finset.sum_Ico_eq_sum_range, mul_sum]
      refine sum_congr rfl fun u _ => ?_
      push_cast
      rw [show (2 * (d : ℝ) + u + 1 - 2 * d) = u + 1 by ring]
      ring
    have h3 := sum_inv_sqrt_le (d * t - 2 * d)
    have h4 : √(((d * t - 2 * d : ℕ) : ℝ)) ≤ √((d : ℝ) * t) := by
      apply Real.sqrt_le_sqrt
      have : d * t - 2 * d ≤ d * t := Nat.sub_le _ _
      exact_mod_cast this
    have hsqrt : √(2 * (d : ℝ)) * √((d : ℝ) * t) = d * (√2 * √(t : ℝ)) := by
      rw [Real.sqrt_mul (by norm_num) d, Real.sqrt_mul (by positivity) t]
      have := Real.mul_self_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
      calc √2 * √(d : ℝ) * (√(d : ℝ) * √(t : ℝ)) = √2 * (√(d : ℝ) * √(d : ℝ)) * √(t : ℝ) := by ring
        _ = d * (√2 * √(t : ℝ)) := by rw [this]; ring
    have hconst := two_sqrt_two_div_sqrt_pi_le
    rw [h1, h2]
    calc c * ∑ u ∈ range (d * t - 2 * d), 1 / √((u : ℝ) + 1)
        ≤ c * (2 * √((d : ℝ) * t)) :=
          mul_le_mul_of_nonneg_left (h3.trans (by linarith)) hc0
      _ = (2 * √2 / √π) * (d ^ 2 * p * √(t : ℝ)) := by
          rw [hc]
          have e3 : (d : ℝ) * p * √(2 * d) / √π * (2 * √((d : ℝ) * t)) =
              2 * d * p * (√(2 * d) * √((d : ℝ) * t)) / √π := by ring
          rw [e3, hsqrt]
          ring
      _ ≤ 1.6 * (d ^ 2 * p * √(t : ℝ)) := mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = 1.6 * d ^ 2 * p * √(t : ℝ) := by ring
  have hprod1 : ∏ r ∈ range m, (if r < 2 * d then (p : ℝ) ^ d else 1) = ((p : ℝ) ^ d) ^ (2 * d) :=
    prod_range_ite_lt _ (by nlinarith)
  set A : ℝ := 1 + (p : ℝ) / √(π * ((t / 2 : ℕ) : ℝ)) with hA
  have hA0 : 0 ≤ A ^ d := pow_nonneg (by linarith [hA1 t]) d
  have hprod3 : ∏ r ∈ range m, (if d * t ≤ r then A ^ d else 1) ≤ (A ^ d) ^ m := by
    calc ∏ r ∈ range m, (if d * t ≤ r then A ^ d else 1) ≤ ∏ r ∈ range m, A ^ d := by
          refine prod_le_prod₀ (fun r _ => ?_) fun r _ => ?_
          · split_ifs
            · exact hA0
            · exact zero_le_one
          · split_ifs
            · exact le_rfl
            · exact one_le_pow₀ (hA1 t)
      _ = (A ^ d) ^ m := by rw [prod_const, card_range]
  have hprod3' : 0 ≤ ∏ r ∈ range m, (if d * t ≤ r then A ^ d else 1) :=
    prod_nonneg fun r _ => by
      split_ifs
      · exact hA0
      · exact zero_le_one
  calc ∏ r ∈ range m, etaRow p d t r
      ≤ ∏ r ∈ range m, ((p : ℝ) ^ d)⁻¹ * ((if r < 2 * d then (p : ℝ) ^ d else 1) * Real.exp (e r) *
          (if d * t ≤ r then A ^ d else 1)) :=
        prod_le_prod₀ (fun r _ => etaRow_nonneg p d t r) hfac
    _ = (((p : ℝ) ^ d)⁻¹) ^ m * (((p : ℝ) ^ d) ^ (2 * d) * Real.exp (∑ r ∈ range m, e r) *
          ∏ r ∈ range m, (if d * t ≤ r then A ^ d else 1)) := by
        rw [prod_mul_distrib, prod_const, card_range, prod_mul_distrib, prod_mul_distrib,
          ← Real.exp_sum, hprod1]
    _ ≤ (((p : ℝ) ^ d)⁻¹) ^ m * (((p : ℝ) ^ d) ^ (2 * d) * Real.exp (1.6 * d ^ 2 * p * √(t : ℝ)) *
          (A ^ d) ^ m) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hsum) (by positivity)) hprod3
          hprod3' (by positivity)
    _ = ((p : ℝ) ^ (d * m))⁻¹ * A ^ (d * m) * Real.exp (1.6 * d ^ 2 * p * √(t : ℝ)) *
          (p : ℝ) ^ (2 * d ^ 2) := by
        rw [inv_pow, ← pow_mul, ← pow_mul, ← pow_mul, show d * (2 * d) = 2 * d ^ 2 by ring]
        ring

theorem lem_seqbases (hp2 : p ≠ 2) {d k : ℕ} (hd : 1 ≤ d) (φ Y : Fin m → Fin d → ZMod p)
    (hk : ∀ a : Fin d → ZMod p, a ≠ 0 → k ≤ (univ.filter fun j => a ⬝ᵥ φ j ≠ 0).card)
    (ht : 2 ≤ (k + d - 1) / d) :
    prob (fun ω : Pairs m → Bool => ∀ i, ∑ j, seidelOf ω i j • φ j = Y i) ≤
      ((p : ℝ) ^ (d * m))⁻¹ * (1 + p / √(π * (((k + d - 1) / d / 2 : ℕ) : ℝ))) ^ (d * m) *
        Real.exp (1.6 * d ^ 2 * p * √((((k + d - 1) / d : ℕ) : ℝ))) * (p : ℝ) ^ (2 * d ^ 2) := by
  obtain ⟨B, hdisj, hcard, hspan⟩ := lem_LObases_b hd φ hk
  have hdt : d * ((k + d - 1) / d) ≤ m := by
    have h1 := card_biUnion (s := (univ : Finset (Fin ((k + d - 1) / d)))) (t := B)
      (fun c _ c' _ h => hdisj h)
    have h2 : ((univ : Finset (Fin ((k + d - 1) / d))).biUnion B).card ≤ m := by
      simpa using card_le_univ ((univ : Finset (Fin ((k + d - 1) / d))).biUnion B)
    rw [h1, sum_congr rfl fun c _ => hcard c, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul] at h2
    rw [mul_comm]
    exact h2
  exact (seqbases_prod hp2 B hdisj hcard φ Y hspan).trans
    (seqbases_numeric (Fact.out : p.Prime).pos hd ht hdt)

end DGS
