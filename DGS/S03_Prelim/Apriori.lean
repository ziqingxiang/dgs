module

public import DGS.S03_Prelim.Border
public import DGS.Core.Seidel
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Matrix Module

namespace DGS

section Exposure

variable {m : ℕ}

def pairsSuccEquiv (m : ℕ) : (Pairs (m + 1) → Bool) ≃ (Pairs m → Bool) × (Fin m → Bool) where
  toFun ω' := (fun q => ω' ⟨(q.1.1.castSucc, q.1.2.castSucc), Fin.castSucc_lt_castSucc_iff.2 q.2⟩,
    fun i => ω' ⟨(i.castSucc, Fin.last m), Fin.castSucc_lt_last i⟩)
  invFun x := fun q =>
    if h : q.1.2 = Fin.last m then
      x.2 (q.1.1.castLT (by
        have h2 := q.2
        rw [h, Fin.lt_def, Fin.val_last] at h2
        exact h2))
    else
      x.1 ⟨(q.1.1.castLT (lt_trans (Fin.lt_def.1 q.2) (Fin.val_lt_last h)),
        q.1.2.castLT (Fin.val_lt_last h)), by
          rw [Fin.lt_def]
          exact Fin.lt_def.1 q.2⟩
  left_inv ω' := by
    funext q
    obtain ⟨⟨i, j⟩, hij⟩ := q
    by_cases h : j = Fin.last m
    · subst h
      simp
    · simp [h]
  right_inv x := by
    refine Prod.ext (funext fun q => ?_) (funext fun i => ?_)
    · simp [Fin.castSucc_ne_last]
    · simp

@[simp] theorem pairsSuccEquiv_apply_fst (ω' : Pairs (m + 1) → Bool) (q : Pairs m) :
    (pairsSuccEquiv m ω').1 q =
      ω' ⟨(q.1.1.castSucc, q.1.2.castSucc), Fin.castSucc_lt_castSucc_iff.2 q.2⟩ := rfl

@[simp] theorem pairsSuccEquiv_apply_snd (ω' : Pairs (m + 1) → Bool) (i : Fin m) :
    (pairsSuccEquiv m ω').2 i = ω' ⟨(i.castSucc, Fin.last m), Fin.castSucc_lt_last i⟩ := rfl

theorem symOf_succ (a b : ℤ) (ω' : Pairs (m + 1) → Bool) :
    symOf a b ω' = border (symOf a b (pairsSuccEquiv m ω').1)
      (twoValued a b (pairsSuccEquiv m ω').2) 0 := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · rw [border_last_castSucc, symOf_apply_gt _ _ _ (Fin.castSucc_lt_last j)]
    rfl
  · rw [border_castSucc_last, symOf_apply_lt _ _ _ (Fin.castSucc_lt_last i)]
    rfl
  · rw [border_castSucc_castSucc]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [symOf_apply_lt _ _ _ (Fin.castSucc_lt_castSucc_iff.2 h), symOf_apply_lt _ _ _ h]
      rfl
    · simp
    · rw [symOf_apply_gt _ _ _ (Fin.castSucc_lt_castSucc_iff.2 h), symOf_apply_gt _ _ _ h]
      rfl

theorem border_map {R S : Type*} {r : ℕ} (L : Matrix (Fin r) (Fin r) R) (y : Fin r → R) (c : R)
    (f : R → S) : (border L y c).map f = border (L.map f) (fun i => f (y i)) (f c) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

theorem border_sub_smul_one {F : Type*} [Field F] {r : ℕ} (L : Matrix (Fin r) (Fin r) F)
    (y : Fin r → F) (c μ : F) : border L y c - μ • 1 = border (L - μ • 1) y (c - μ) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · simp [(Fin.castSucc_ne_last j).symm]
  · simp [Fin.castSucc_ne_last i]
  · simp [Matrix.one_apply, Fin.castSucc_inj]

end Exposure

section Apriori

variable {F : Type*} [Field F] (a b : ℤ)

noncomputable def shiftedMat {m : ℕ} (μ : F) (ω : Pairs m → Bool) : Matrix (Fin m) (Fin m) F :=
  (symOf a b ω).map (Int.castRingHom F) - μ • 1

noncomputable def geomMult {m : ℕ} (μ : F) (ω : Pairs m → Bool) : ℕ :=
  corank (shiftedMat a b μ ω)

variable {a b}

theorem shiftedMat_transpose {m : ℕ} (μ : F) (ω : Pairs m → Bool) :
    (shiftedMat a b μ ω)ᵀ = shiftedMat a b μ ω := by
  have h : (symOf a b ω)ᵀ = symOf a b ω := by
    ext i j
    exact symOf_comm a b ω j i
  rw [shiftedMat, transpose_sub, transpose_smul, transpose_one, ← transpose_map, h]

theorem shiftedMat_succ {m : ℕ} (μ : F) (ω' : Pairs (m + 1) → Bool) :
    shiftedMat a b μ ω' = border (shiftedMat a b μ (pairsSuccEquiv m ω').1)
      (twoValued (a : F) (b : F) (pairsSuccEquiv m ω').2) (-μ) := by
  rw [shiftedMat, symOf_succ, border_map, border_sub_smul_one, map_zero, zero_sub]
  congr 1
  funext i
  simp only [twoValued]
  split_ifs <;> simp

theorem geomMult_le {m : ℕ} (μ : F) (ω : Pairs m → Bool) : geomMult a b μ ω ≤ m := by
  unfold geomMult corank
  exact (Submodule.finrank_le _).trans (Module.finrank_fin_fun F).le

noncomputable def ups (r : ℕ) : ℝ := (2 : ℝ) ^ ((r : ℝ) ^ 2 / 4)

theorem ups_pos (r : ℕ) : 0 < ups r := Real.rpow_pos_of_pos two_pos _

theorem ups_mono {r r' : ℕ} (h : r ≤ r') : ups r ≤ ups r' := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (r : ℝ) ≤ r' := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  nlinarith

theorem ups_zero : ups 0 = 1 := by simp [ups]

theorem two_rpow_neg_quarter_le : (2 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 0.841 := by
  have hx : 0 ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) := (Real.rpow_pos_of_pos two_pos _).le
  have h4 : ((2 : ℝ) ^ (-(1 / 4 : ℝ))) ^ (4 : ℕ) = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [← pow_le_pow_iff_left₀ hx (by norm_num) (by norm_num : (4 : ℕ) ≠ 0), h4]
  norm_num

theorem ups_three_le : ups 3 ≤ 4.76 := by
  have hx : 0 ≤ ups 3 := (ups_pos 3).le
  have h4 : (ups 3) ^ (4 : ℕ) = 512 := by
    rw [ups, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [← pow_le_pow_iff_left₀ hx (by norm_num) (by norm_num : (4 : ℕ) ≠ 0), h4]
  norm_num

theorem ups_step {r : ℕ} (hr : 3 ≤ r) :
    ups (r - 1) + ups (r + 1) * (2 : ℝ)⁻¹ ^ r ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) * ups r := by
  have hR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  have hinv : (2 : ℝ)⁻¹ ^ r = (2 : ℝ) ^ (-(r : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
  unfold ups
  rw [hcast, hinv, Nat.cast_succ, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos,
    show ((r : ℝ) + 1) ^ 2 / 4 + -(r : ℝ) = ((r : ℝ) - 1) ^ 2 / 4 by ring, ← two_mul,
    show (2 : ℝ) * (2 : ℝ) ^ (((r : ℝ) - 1) ^ 2 / 4) = (2 : ℝ) ^ (1 + ((r : ℝ) - 1) ^ 2 / 4) by
      rw [Real.rpow_add two_pos, Real.rpow_one]]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

end Apriori

section AprioriMain

variable {F : Type*} [Field F] {a b : ℤ}

theorem expect_ups_succ (hab : (a : F) ≠ (b : F)) (μ : F) (m : ℕ) (ω : Pairs m → Bool) :
    expect (fun s : Fin m → Bool => ups (geomMult a b μ ((pairsSuccEquiv m).symm (ω, s)))) ≤
      (2 : ℝ) ^ (-(1 / 4 : ℝ)) * ups (geomMult a b μ ω) + 4.76 := by
  classical
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) := (Real.rpow_pos_of_pos two_pos _).le
  set L := shiftedMat a b μ ω with hLdef
  set g := geomMult a b μ ω with hgdef
  have hL : Lᵀ = L := shiftedMat_transpose μ ω
  have hM : ∀ s : Fin m → Bool, geomMult a b μ ((pairsSuccEquiv m).symm (ω, s)) =
      corank (border L (twoValued (a : F) (b : F) s) (-μ)) := by
    intro s
    unfold geomMult
    rw [shiftedMat_succ, Equiv.apply_symm_apply]
  have hcor := fun s : Fin m → Bool => lem_border_corank (c := -μ) (y := twoValued (a : F) (b : F) s) hL
  have hgL : corank L = g := rfl
  by_cases hg : g ≤ 2
  ·
    calc expect (fun s : Fin m → Bool => ups (geomMult a b μ ((pairsSuccEquiv m).symm (ω, s))))
        ≤ expect (fun _ : Fin m → Bool => ups 3) := expect_mono fun s => by
          rw [hM]
          exact ups_mono (by have := (hcor s).1; omega)
      _ = ups 3 := expect_const _
      _ ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) * ups g + 4.76 := by
          have := ups_three_le
          have := ups_pos g
          nlinarith
  ·
    push Not at hg
    have hpoint : ∀ s : Fin m → Bool, ups (geomMult a b μ ((pairsSuccEquiv m).symm (ω, s))) ≤
        ups (g - 1) + ups (g + 1) * (if ∀ w ∈ LinearMap.ker L.mulVecLin,
          twoValued (a : F) (b : F) s ⬝ᵥ w = 0 then 1 else 0) := by
      intro s
      rw [hM]
      obtain ⟨h1, h2, h3⟩ := hcor s
      split_ifs with hperp
      · rw [mul_one]
        have := ups_mono (show corank (border L (twoValued (a : F) (b : F) s) (-μ)) ≤ g + 1 by omega)
        have := ups_pos (g - 1)
        linarith
      · rw [mul_zero, add_zero]
        apply ups_mono
        have : ¬ corank L ≤ corank (border L (twoValued (a : F) (b : F) s) (-μ)) :=
          fun h => hperp (h3.1 h)
        omega
    have hprob := lem_odlyzko_perp (a : F) (b : F) hab (LinearMap.ker L.mulVecLin)
    calc expect (fun s : Fin m → Bool => ups (geomMult a b μ ((pairsSuccEquiv m).symm (ω, s))))
        ≤ expect (fun s : Fin m → Bool => ups (g - 1) + ups (g + 1) *
            (if ∀ w ∈ LinearMap.ker L.mulVecLin, twoValued (a : F) (b : F) s ⬝ᵥ w = 0
              then 1 else 0)) := expect_mono hpoint
      _ = ups (g - 1) + ups (g + 1) * prob (fun s : Fin m → Bool =>
            ∀ w ∈ LinearMap.ker L.mulVecLin, twoValued (a : F) (b : F) s ⬝ᵥ w = 0) := by
          rw [expect_add, expect_const, expect_const_mul, expect_indicator]
      _ ≤ ups (g - 1) + ups (g + 1) * (2 : ℝ)⁻¹ ^ g := by
          gcongr
          · exact (ups_pos _).le
          · exact hprob
      _ ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) * ups g := ups_step (by omega)
      _ ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) * ups g + 4.76 := by linarith

theorem lem_apriori_expect (hab : (a : F) ≠ (b : F)) (μ : F) (m : ℕ) :
    expect (fun ω : Pairs m → Bool => ups (geomMult a b μ ω)) ≤ 30 := by
  induction m with
  | zero =>
    have h0 : ∀ ω : Pairs 0 → Bool, geomMult a b μ ω = 0 := fun ω => by
      unfold geomMult corank
      exact Module.finrank_zero_of_subsingleton
    simp only [h0, ups_zero]
    rw [expect_const]
    norm_num
  | succ m ih =>
    rw [← expect_equiv (pairsSuccEquiv m).symm, expect_prod]
    have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) := (Real.rpow_pos_of_pos two_pos _).le
    calc expect (fun ω => expect (fun s => ups (geomMult a b μ ((pairsSuccEquiv m).symm (ω, s)))))
        ≤ expect (fun ω : Pairs m → Bool => (2 : ℝ) ^ (-(1 / 4 : ℝ)) * ups (geomMult a b μ ω) + 4.76) :=
          expect_mono fun ω => expect_ups_succ hab μ m ω
      _ = (2 : ℝ) ^ (-(1 / 4 : ℝ)) * expect (fun ω : Pairs m → Bool => ups (geomMult a b μ ω)) + 4.76 := by
          rw [expect_add, expect_const_mul, expect_const]
      _ ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) * 30 + 4.76 := by gcongr
      _ ≤ 30 := by
          have := two_rpow_neg_quarter_le
          linarith

theorem lem_apriori_tail (hab : (a : F) ≠ (b : F)) (μ : F) (m r : ℕ) :
    prob (fun ω : Pairs m → Bool => r ≤ geomMult a b μ ω) ≤ 30 * (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4)) := by
  calc prob (fun ω : Pairs m → Bool => r ≤ geomMult a b μ ω)
      ≤ prob (fun ω : Pairs m → Bool => ups r ≤ ups (geomMult a b μ ω)) :=
        prob_mono fun ω h => ups_mono h
    _ ≤ expect (fun ω : Pairs m → Bool => ups (geomMult a b μ ω)) / ups r :=
        prob_ge_le_expect_div _ (fun ω => (ups_pos _).le) (ups_pos r)
    _ ≤ 30 / ups r := div_le_div_of_nonneg_right (lem_apriori_expect hab μ m) (ups_pos r).le
    _ = 30 * (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4)) := by
        rw [div_eq_mul_inv, ups, ← Real.rpow_neg (by norm_num)]

noncomputable def C0 : ℝ :=
  1 + 30 * ∑' r : ℕ, (10 : ℝ) ^ (r + 1) * (2 : ℝ) ^ (-(((r + 1 : ℕ) : ℝ) ^ 2 / 4))

theorem summable_C0 :
    Summable (fun r : ℕ => (10 : ℝ) ^ (r + 1) * (2 : ℝ) ^ (-(((r + 1 : ℕ) : ℝ) ^ 2 / 4))) := by
  refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left
      ((2 : ℝ) ^ (24 : ℝ)))
  set u : ℝ := ((r + 1 : ℕ) : ℝ) with hu
  have h10 : (10 : ℝ) ^ (r + 1) ≤ (2 : ℝ) ^ (4 * u) := by
    rw [hu, show (4 : ℝ) * ((r + 1 : ℕ) : ℝ) = ((4 * (r + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hgeom : ((1 : ℝ) / 2) ^ r = (2 : ℝ) ^ (-(r : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  calc (10 : ℝ) ^ (r + 1) * (2 : ℝ) ^ (-(u ^ 2 / 4))
      ≤ (2 : ℝ) ^ (4 * u) * (2 : ℝ) ^ (-(u ^ 2 / 4)) := by gcongr
    _ = (2 : ℝ) ^ (4 * u + -(u ^ 2 / 4)) := (Real.rpow_add two_pos _ _).symm
    _ ≤ (2 : ℝ) ^ ((24 : ℝ) + -(r : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : u = (r : ℝ) + 1 := by rw [hu]; push_cast; ring
        rw [this]
        nlinarith [sq_nonneg (((r : ℝ) + 1) / 2 - 5)]
    _ = (2 : ℝ) ^ (24 : ℝ) * ((1 : ℝ) / 2) ^ r := by rw [Real.rpow_add two_pos, hgeom]

theorem lem_apriori_ten (hab : (a : F) ≠ (b : F)) (μ : F) (m : ℕ) :
    expect (fun ω : Pairs m → Bool => (10 : ℝ) ^ geomMult a b μ ω) ≤ C0 := by
  classical
  have hpoint : ∀ ω : Pairs m → Bool, (10 : ℝ) ^ geomMult a b μ ω ≤
      1 + ∑ r ∈ Finset.range m, (10 : ℝ) ^ (r + 1) *
        (if r + 1 ≤ geomMult a b μ ω then 1 else 0) := by
    intro ω
    have hnn : ∀ r ∈ Finset.range m, (0 : ℝ) ≤ (10 : ℝ) ^ (r + 1) *
        (if r + 1 ≤ geomMult a b μ ω then 1 else 0) := fun r _ => by positivity
    rcases Nat.eq_zero_or_pos (geomMult a b μ ω) with h | h
    · rw [h, pow_zero]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun r _ => by positivity)
    · have hmem : geomMult a b μ ω - 1 ∈ Finset.range m := by
        have := geomMult_le (a := a) (b := b) μ ω
        rw [Finset.mem_range]
        omega
      have h1 := Finset.single_le_sum hnn hmem
      rw [Nat.sub_add_cancel h, ite_eq_left le_rfl, mul_one] at h1
      linarith
  have htail : ∀ r : ℕ, prob (fun ω : Pairs m → Bool => r + 1 ≤ geomMult a b μ ω) ≤
      30 * (2 : ℝ) ^ (-(((r + 1 : ℕ) : ℝ) ^ 2 / 4)) := fun r => lem_apriori_tail hab μ m (r + 1)
  calc expect (fun ω : Pairs m → Bool => (10 : ℝ) ^ geomMult a b μ ω)
      ≤ expect (fun ω : Pairs m → Bool => 1 + ∑ r ∈ Finset.range m, (10 : ℝ) ^ (r + 1) *
          (if r + 1 ≤ geomMult a b μ ω then 1 else 0)) := expect_mono hpoint
    _ = 1 + ∑ r ∈ Finset.range m, (10 : ℝ) ^ (r + 1) *
          prob (fun ω : Pairs m → Bool => r + 1 ≤ geomMult a b μ ω) := by
        rw [expect_add, expect_const, expect_sum]
        congr 1
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [expect_const_mul, expect_indicator]
    _ ≤ 1 + ∑ r ∈ Finset.range m, (10 : ℝ) ^ (r + 1) *
          (30 * (2 : ℝ) ^ (-(((r + 1 : ℕ) : ℝ) ^ 2 / 4))) := by
        gcongr with r hr
        exact htail r
    _ = 1 + 30 * ∑ r ∈ Finset.range m, (10 : ℝ) ^ (r + 1) *
          (2 : ℝ) ^ (-(((r + 1 : ℕ) : ℝ) ^ 2 / 4)) := by
        rw [Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ ≤ C0 := by
        unfold C0
        gcongr
        exact summable_C0.sum_le_tsum _ (fun r _ => by positivity)

theorem lem_apriori (hab : (a : F) ≠ (b : F)) (μ : F) (m : ℕ) :
    expect (fun ω : Pairs m → Bool => (2 : ℝ) ^ ((geomMult a b μ ω : ℝ) ^ 2 / 4)) ≤ 30 ∧
      (∀ r : ℕ, prob (fun ω : Pairs m → Bool => r ≤ geomMult a b μ ω) ≤
        30 * (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4))) ∧
      expect (fun ω : Pairs m → Bool => (10 : ℝ) ^ geomMult a b μ ω) ≤ C0 :=
  ⟨lem_apriori_expect hab μ m, fun r => lem_apriori_tail hab μ m r, lem_apriori_ten hab μ m⟩

end AprioriMain

end DGS
