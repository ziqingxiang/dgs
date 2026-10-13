module

public import DGS.S13_Deg3.FullSupp
public import DGS.S12_Deg2.SEd
public import DGS.S10_Tools.SeqBases

@[expose] public section

open Finset Matrix Polynomial Module
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime] {m n : ℕ}

def QAd (b : Fin (n + 1) → ZMod p) (A : Matrix (Fin m) (Fin m) (ZMod p)) : Matrix (Fin m) (Fin m) (ZMod p) :=
  A ^ (n + 1) + ∑ i : Fin (n + 1), b i • A ^ (i : ℕ)

theorem aeval_eq_QAd {A : Matrix (Fin m) (Fin m) (ZMod p)} {β : (ZMod p)[X]} (hβm : β.Monic)
    (hβd : β.natDegree = n + 1) : aeval A β = QAd (n := n) (fun i : Fin (n + 1) => β.coeff i) A :=
  aeval_monic_eq hβm hβd

def companionU (b : Fin (n + 1) → ZMod p) (c : ZMod p) (g : Fin (n + 1) → ZMod p) : Fin (n + 1) → ZMod p :=
  Fin.snoc (α := fun _ => ZMod p) (Fin.tail g) (c - ∑ l, b l * g l)

def krySysU (ω : Pairs m → Bool) (b : Fin (n + 1) → ZMod p) (u : Fin m → ZMod p)
    (w : Fin m → Fin (n + 1) → ZMod p) : Prop :=
  ∀ i, ∑ j, seidelOf ω i j • w j = companionU b (u i) (w i)

theorem krySysU_kryRows (ω : Pairs m → Bool) (b : Fin (n + 1) → ZMod p) {u v : Fin m → ZMod p}
    (hv : QAd b (modP p (seidelOf ω)) *ᵥ v = u) :
    krySysU ω b u (kryRows (n := n) (modP p (seidelOf ω)) v) := by
  set A := modP p (seidelOf ω) with hA
  have hlast : A ^ (n + 1) *ᵥ v = u - ∑ i : Fin (n + 1), b i • (A ^ (i : ℕ) *ᵥ v) := by
    rw [← hv, QAd, add_mulVec, Matrix.sum_mulVec]
    simp only [smul_mulVec]
    abel
  intro i
  funext r
  have hL : (∑ j, seidelOf ω i j • kryRows (n := n) A v j) r = (A ^ ((r : ℕ) + 1) *ᵥ v) i := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, kryRows, zsmul_eq_mul]
    rw [pow_succ', ← mulVec_mulVec]
    simp only [mulVec, dotProduct, hA, modP, Matrix.map_apply, Int.coe_castRingHom]
  rw [hL]
  induction r using Fin.lastCases with
  | last =>
    simp only [companionU, Fin.snoc_last, Fin.val_last]
    rw [hlast]
    simp [kryRows, Finset.sum_apply]
  | cast r' =>
    simp only [companionU, Fin.snoc_castSucc, Fin.tail, kryRows, Fin.val_castSucc, Fin.val_succ]

theorem dot_kryRows (A : Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) (a : Fin (n + 1) → ZMod p)
    (j : Fin m) : a ⬝ᵥ kryRows (n := n) A v j = (polyA A a *ᵥ v) j := by
  rw [polyA, Matrix.sum_mulVec, Finset.sum_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rfl

theorem card_dot_fiber {d : ℕ} (ℓ : Fin d → ZMod p) (hℓ : ℓ ≠ 0) (a : ZMod p) :
    ((univ.filter fun g : Fin d → ZMod p => ℓ ⬝ᵥ g = a).card : ℝ) * p = (p : ℝ) ^ d := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, ℓ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (funext h)
  set g0 : Fin d → ZMod p := Pi.single i (ℓ i)⁻¹ with hg0
  have hg0' : ℓ ⬝ᵥ g0 = 1 := by
    rw [hg0, dotProduct_single, mul_inv_cancel₀ hi]
  have hfib : ∀ c : ZMod p, (univ.filter fun g : Fin d → ZMod p => ℓ ⬝ᵥ g = c).card =
      (univ.filter fun g : Fin d → ZMod p => ℓ ⬝ᵥ g = 0).card := by
    intro c
    refine Finset.card_nbij' (fun g => g - c • g0) (fun g => g + c • g0) ?_ ?_ ?_ ?_
    · intro g hg
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      rw [dotProduct_sub, dotProduct_smul, hg0', hg, smul_eq_mul, mul_one, sub_self]
    · intro g hg
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      rw [dotProduct_add, dotProduct_smul, hg0', hg, smul_eq_mul, mul_one, zero_add]
    · intro g _
      simp
    · intro g _
      simp
  have htot : ∑ c : ZMod p, (univ.filter fun g : Fin d → ZMod p => ℓ ⬝ᵥ g = c).card = p ^ d := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := fun g => ℓ ⬝ᵥ g) (fun g _ => mem_univ _)]
    rw [card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [Finset.sum_congr rfl fun c _ => hfib c, sum_const, card_univ, ZMod.card, smul_eq_mul] at htot
  rw [hfib a]
  have h' : (((p * (univ.filter fun g : Fin d → ZMod p => ℓ ⬝ᵥ g = 0).card : ℕ)) : ℝ) = ((p ^ d : ℕ) : ℝ) := by
    rw [htot]
  push_cast at h'
  linarith

theorem sum_dot_eq_pow {d : ℕ} (ℓ : Fin d → ZMod p) (hℓ : ℓ ≠ 0) (F : ZMod p → ℝ) :
    (∑ g : Fin d → ZMod p, F (ℓ ⬝ᵥ g)) * p = (p : ℝ) ^ d * ∑ a, F a := by
  classical
  rw [← Finset.sum_fiberwise' (univ : Finset (Fin d → ZMod p)) (fun g => ℓ ⬝ᵥ g) F, sum_mul, mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_const, nsmul_eq_mul, mul_comm _ (F a), mul_assoc, card_dot_fiber ℓ hℓ a, mul_comm]

theorem sum_gaussW_dot (ℓ : Fin (n + 1) → ZMod p) (hℓ : ℓ ≠ 0) (σ : ℝ) :
    ∑ g : Fin (n + 1) → ZMod p, gaussW σ (ℓ ⬝ᵥ g).valMinAbs = (p : ℝ) ^ n * (1 + muP p σ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h := sum_dot_eq_pow ℓ hℓ (fun a => gaussW σ a.valMinAbs)
  have h1 : ∑ a : ZMod p, gaussW σ a.valMinAbs = 1 + muP p σ := by
    rw [muP, ← Finset.sum_filter, Finset.filter_ne' univ (0 : ZMod p), ← Finset.add_sum_erase _ _ (mem_univ 0)]
    rw [ZMod.valMinAbs_zero, gaussW_zero]
  rw [h1] at h
  have h2 : (p : ℝ) ^ (n + 1) * (1 + muP p σ) = ((p : ℝ) ^ n * (1 + muP p σ)) * p := by ring
  rw [h2] at h
  exact mul_right_cancel₀ hp.ne' h

noncomputable def seqB (p m n k : ℕ) : ℝ :=
  ((p : ℝ) ^ ((n + 1) * m))⁻¹ * (1 + p / √(π * ((((k + (n + 1) - 1) / (n + 1)) / 2 : ℕ) : ℝ))) ^ ((n + 1) * m) *
    Real.exp (1.6 * ((n + 1 : ℕ) : ℝ) ^ 2 * p * √((((k + (n + 1) - 1) / (n + 1) : ℕ) : ℝ))) *
      (p : ℝ) ^ (2 * (n + 1) ^ 2)

theorem seqB_nonneg (p m n k : ℕ) : 0 ≤ seqB p m n k := by
  unfold seqB
  positivity

theorem prob_sysU_short_le (hp2 : p ≠ 2) {k : ℕ} (b : Fin (n + 1) → ZMod p) (u : Fin m → ZMod p)
    (Uc : Finset (Fin m)) {σ : ℝ} (hσ : 0 ≤ σ) (R2 : ℝ) (ht : 2 ≤ (k + (n + 1) - 1) / (n + 1)) :
    prob (fun ω : Pairs m → Bool => ∃ w : Fin m → Fin (n + 1) → ZMod p,
      (∀ a : Fin (n + 1) → ZMod p, a ≠ 0 → k ≤ (univ.filter fun j => a ⬝ᵥ w j ≠ 0).card) ∧
      krySysU ω b u w ∧ ∃ ℓ : Fin (n + 1) → ZMod p, ℓ ≠ 0 ∧
        ∑ j ∈ Uc, (((ℓ ⬝ᵥ w j).valMinAbs : ℤ) : ℝ) ^ 2 ≤ R2) ≤
      (p : ℝ) ^ (n + 1) * (Real.exp (σ * R2) * (((p : ℝ) ^ n * (1 + muP p σ)) ^ Uc.card *
        ((p : ℝ) ^ (n + 1)) ^ Ucᶜ.card)) * seqB p m n k := by
  classical
  set B := seqB p m n k with hB
  have hB0 : 0 ≤ B := seqB_nonneg p m n k
  set H : (Fin m → Fin (n + 1) → ZMod p) → Prop :=
    fun w => ∀ a : Fin (n + 1) → ZMod p, a ≠ 0 → k ≤ (univ.filter fun j => a ⬝ᵥ w j ≠ 0).card with hH
  set sh : (Fin (n + 1) → ZMod p) → (Fin m → Fin (n + 1) → ZMod p) → Prop :=
    fun ℓ w => ∑ j ∈ Uc, (((ℓ ⬝ᵥ w j).valMinAbs : ℤ) : ℝ) ^ 2 ≤ R2 with hsh
  set wt : (Fin (n + 1) → ZMod p) → Fin m → (Fin (n + 1) → ZMod p) → ℝ :=
    fun ℓ j g => if j ∈ Uc then gaussW σ (ℓ ⬝ᵥ g).valMinAbs else 1 with hwt
  have hwt0 : ∀ ℓ j g, 0 ≤ wt ℓ j g := fun ℓ j g => by
    simp only [hwt]
    split_ifs
    · exact gaussW_nonneg _ _
    · exact zero_le_one
  set Wl : ℝ := Real.exp (σ * R2) * (((p : ℝ) ^ n * (1 + muP p σ)) ^ Uc.card *
    ((p : ℝ) ^ (n + 1)) ^ Ucᶜ.card) with hWl
  have hstep : ∀ ℓ w, prob (fun ω : Pairs m → Bool => ℓ ≠ 0 ∧ sh ℓ w ∧ H w ∧ krySysU ω b u w) ≤
      (if ℓ = 0 then 0 else Real.exp (σ * R2) * (∏ j, wt ℓ j (w j)) * B) := by
    intro ℓ w
    by_cases h : ℓ ≠ 0 ∧ sh ℓ w ∧ H w
    · rw [ite_eq_right h.1]
      have h1 : prob (fun ω : Pairs m → Bool => ℓ ≠ 0 ∧ sh ℓ w ∧ H w ∧ krySysU ω b u w) ≤
          prob (fun ω : Pairs m → Bool => krySysU ω b u w) := prob_mono fun ω hω => hω.2.2.2
      have h2 : prob (fun ω : Pairs m → Bool => krySysU ω b u w) ≤ B :=
        lem_seqbases hp2 (by omega) w (fun i => companionU b (u i) (w i)) h.2.2 ht
      have e : ∏ j, wt ℓ j (w j) = Real.exp (-σ * ∑ j ∈ Uc, (((ℓ ⬝ᵥ w j).valMinAbs : ℤ) : ℝ) ^ 2) := by
        simp only [hwt]
        rw [Finset.prod_ite_mem univ Uc, univ_inter, mul_sum, Real.exp_sum]
        rfl
      have h3 : 1 ≤ Real.exp (σ * R2) * ∏ j, wt ℓ j (w j) := by
        rw [e, ← Real.exp_add]
        apply Real.one_le_exp
        have := h.2.1
        simp only [hsh] at this
        nlinarith
      calc prob (fun ω : Pairs m → Bool => ℓ ≠ 0 ∧ sh ℓ w ∧ H w ∧ krySysU ω b u w) ≤ B := h1.trans h2
        _ ≤ (Real.exp (σ * R2) * ∏ j, wt ℓ j (w j)) * B := le_mul_of_one_le_left hB0 h3
    · rw [prob_congr (Q := fun _ => False) fun ω => ⟨fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩, False.elim⟩,
        prob_false]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (prod_nonneg fun j _ => hwt0 _ _ _)) hB0
  have hcount : ∀ ℓ : Fin (n + 1) → ZMod p, ℓ ≠ 0 → ∑ w : Fin m → Fin (n + 1) → ZMod p, ∏ j, wt ℓ j (w j) =
      ((p : ℝ) ^ n * (1 + muP p σ)) ^ Uc.card * ((p : ℝ) ^ (n + 1)) ^ Ucᶜ.card := by
    intro ℓ hℓ
    rw [← Fintype.prod_sum (fun j g => wt ℓ j g)]
    have e : ∀ j, ∑ g, wt ℓ j g = if j ∈ Uc then (p : ℝ) ^ n * (1 + muP p σ) else (p : ℝ) ^ (n + 1) := by
      intro j
      simp only [hwt]
      split_ifs
      · exact sum_gaussW_dot ℓ hℓ σ
      · rw [sum_const, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul, mul_one]
        push_cast
        ring
    rw [Finset.prod_congr rfl fun j _ => e j, Finset.prod_ite, prod_const, prod_const]
    congr 2
    · congr 1
      ext j
      simp
    · congr 1
      ext j
      simp
  have hsub : ∀ ω : Pairs m → Bool, (∃ w : Fin m → Fin (n + 1) → ZMod p, H w ∧ krySysU ω b u w ∧
      ∃ ℓ : Fin (n + 1) → ZMod p, ℓ ≠ 0 ∧ sh ℓ w) →
      ∃ ℓ : Fin (n + 1) → ZMod p, ∃ w : Fin m → Fin (n + 1) → ZMod p,
        ℓ ≠ 0 ∧ sh ℓ w ∧ H w ∧ krySysU ω b u w := by
    rintro ω ⟨w, hw, hs, ℓ, hℓ, hsh'⟩
    exact ⟨ℓ, w, hℓ, hsh', hw, hs⟩
  calc prob (fun ω : Pairs m → Bool => ∃ w : Fin m → Fin (n + 1) → ZMod p, H w ∧ krySysU ω b u w ∧
        ∃ ℓ : Fin (n + 1) → ZMod p, ℓ ≠ 0 ∧ sh ℓ w)
      ≤ prob (fun ω : Pairs m → Bool => ∃ ℓ : Fin (n + 1) → ZMod p, ∃ w : Fin m → Fin (n + 1) → ZMod p,
          ℓ ≠ 0 ∧ sh ℓ w ∧ H w ∧ krySysU ω b u w) := prob_mono hsub
    _ ≤ ∑ ℓ : Fin (n + 1) → ZMod p, prob (fun ω : Pairs m → Bool => ∃ w : Fin m → Fin (n + 1) → ZMod p,
          ℓ ≠ 0 ∧ sh ℓ w ∧ H w ∧ krySysU ω b u w) := prob_exists_le_sum_fintype _
    _ ≤ ∑ ℓ : Fin (n + 1) → ZMod p, ∑ w : Fin m → Fin (n + 1) → ZMod p,
          prob (fun ω : Pairs m → Bool => ℓ ≠ 0 ∧ sh ℓ w ∧ H w ∧ krySysU ω b u w) :=
        sum_le_sum fun ℓ _ => prob_exists_le_sum_fintype _
    _ ≤ ∑ ℓ : Fin (n + 1) → ZMod p, ∑ w : Fin m → Fin (n + 1) → ZMod p,
          (if ℓ = 0 then 0 else Real.exp (σ * R2) * (∏ j, wt ℓ j (w j)) * B) :=
        sum_le_sum fun ℓ _ => sum_le_sum fun w _ => hstep ℓ w
    _ ≤ ∑ _ℓ : Fin (n + 1) → ZMod p, Wl * B := by
        refine sum_le_sum fun ℓ _ => ?_
        by_cases hℓ : ℓ = 0
        · simp only [hℓ, ite_true, sum_const_zero]
          have hμ := muP_pos (p := p) σ
          exact mul_nonneg (by rw [hWl]; positivity) hB0
        · simp only [hℓ, ite_false]
          rw [← sum_mul, ← mul_sum, hcount ℓ hℓ]
    _ = (p : ℝ) ^ (n + 1) * Wl * B := by
        rw [sum_const, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

theorem sysU_of_short (ω : Pairs m → Bool) (b : Fin (n + 1) → ZMod p) (u : Fin m → ZMod p)
    (P : Fin m → Prop) [DecidablePred P] {R2 : ℝ}
    (hQ : IsUnit (QAd b (modP p (seidelOf ω))).det)
    (hsupp : ∀ a : Fin (n + 1) → ZMod p, a ≠ 0 → m ≤ 20 * (univ.filter fun j =>
      ((polyA (modP p (seidelOf ω)) a * (QAd b (modP p (seidelOf ω)))⁻¹) *ᵥ u) j ≠ 0).card)
    {a : Fin (n + 1) → ZMod p} (ha : a ≠ 0)
    (hmu : (muMin (fun j : {j // P j} =>
      ((polyA (modP p (seidelOf ω)) a * (QAd b (modP p (seidelOf ω)))⁻¹) *ᵥ u) j) : ℝ) ≤ R2) :
    ∃ w : Fin m → Fin (n + 1) → ZMod p,
      (∀ a : Fin (n + 1) → ZMod p, a ≠ 0 → (m + 19) / 20 ≤ (univ.filter fun j => a ⬝ᵥ w j ≠ 0).card) ∧
      krySysU ω b u w ∧ ∃ ℓ : Fin (n + 1) → ZMod p, ℓ ≠ 0 ∧
        ∑ j ∈ univ.filter P, (((ℓ ⬝ᵥ w j).valMinAbs : ℤ) : ℝ) ^ 2 ≤ R2 := by
  classical
  set A := modP p (seidelOf ω) with hA
  set Q := QAd b A with hQdef
  set v := Q⁻¹ *ᵥ u with hv
  have hdot : ∀ a' : Fin (n + 1) → ZMod p, ∀ j, a' ⬝ᵥ kryRows (n := n) A v j = ((polyA A a' * Q⁻¹) *ᵥ u) j := by
    intro a' j
    rw [dot_kryRows, hv, mulVec_mulVec]
  refine ⟨kryRows (n := n) A v, ?_, ?_, ?_⟩
  · intro a' ha'
    have h1 := hsupp a' ha'
    have e : (univ.filter fun j => a' ⬝ᵥ kryRows (n := n) A v j ≠ 0) =
        univ.filter fun j => ((polyA A a' * Q⁻¹) *ᵥ u) j ≠ 0 := by
      ext j
      simp only [mem_filter, mem_univ, true_and, hdot]
    rw [e]
    omega
  · refine krySysU_kryRows ω b ?_
    rw [hv, mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ, one_mulVec]
  · obtain ⟨c, hc0, hc⟩ := exists_muMin_eq (fun j : {j // P j} => ((polyA A a * Q⁻¹) *ᵥ u) j)
    refine ⟨c • a, smul_ne_zero hc0 ha, ?_⟩
    have e1 : ∀ j, (c • a) ⬝ᵥ kryRows (n := n) A v j = c * ((polyA A a * Q⁻¹) *ᵥ u) j := by
      intro j
      rw [smul_dotProduct, hdot, smul_eq_mul]
    have e2 : ∑ j ∈ univ.filter P, ((((c • a) ⬝ᵥ kryRows (n := n) A v j).valMinAbs : ℤ) : ℝ) ^ 2 =
        ((normSqLift (fun j : {j // P j} => c * ((polyA A a * Q⁻¹) *ᵥ u) j) : ℤ) : ℝ) := by
      rw [normSqLift]
      push_cast
      simp only [e1]
      exact Finset.sum_subtype (univ.filter P) (fun j => by simp)
        (fun j => (((c * ((polyA A a * Q⁻¹) *ᵥ u) j).valMinAbs : ℤ) : ℝ) ^ 2)
    rw [e2, ← hc]
    exact hmu

end DGS
