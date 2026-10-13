module

public import DGS.S11_Deg1.PencilBlocks
public import DGS.S11_Deg1.SEthm

@[expose] public section

open Finset Matrix Module Filter Topology

namespace DGS

variable {m : ℕ} {p : ℕ} [Fact p.Prime]

section OneChoice

variable (b0 b1 a0 a1 : ZMod p) (U R : Finset (Fin m))

def BW (t : ℕ) (ω : Pairs m → Bool) : Prop :=
  (Set.range (Wrow p R ω)).finrank (ZMod p) ≤ R.card / 2 - t - 1

def BP (t : ℕ) (ω : Pairs m → Bool) : Prop :=
  t + 1 ≤ corank (PUmat (PAm a0 a1 (modP p (seidelOf ω))) (eUOf U))

def BK (ω : Pairs m → Bool) : Prop :=
  ((Kof p b0 b1 a0 a1 U R ω).rank : ℝ) < Rᶜ.card + 0.13 * m

theorem prob_BW_le (hp2 : p ≠ 2) {t : ℕ} (htk : t + 1 ≤ R.card / 2) (hkn : R.card / 2 ≤ Rᶜ.card) :
    prob (BW (p := p) R t) ≤ 2 ^ (R.card / 2) * ((1 : ℝ) / 2) ^ ((t + 1) * (t + 1)) := by
  set k := R.card / 2 with hk
  set nR := Rᶜ.card with hnR
  have hF : (1 : ZMod p) ≠ -1 := one_ne_neg_one_zmod hp2
  rw [prob_eq_prob_replace (blk2 R) (blk2_injective R)]
  have h1 : ∀ y : (Pairs m → Bool) × (Fin k × Fin nR → Bool),
      BW (p := p) R t (replace (blk2 R) (blk2_injective R) y.1 y.2) ↔
        (Set.range fun c => twoValued (1 : ZMod p) (-1) (fun a => y.2 (c, a))).finrank (ZMod p) ≤ k - t - 1 := by
    intro y
    unfold BW
    rw [Wrow_replace2]
  rw [prob_congr h1, prob_snd (Ω := Pairs m → Bool)
    (fun x : Fin k × Fin nR → Bool =>
      (Set.range fun c => twoValued (1 : ZMod p) (-1) (fun a => x (c, a))).finrank (ZMod p) ≤ k - t - 1)]
  rw [prob_curry_eq (fun x : Fin k → Fin nR → Bool =>
    (Set.range fun c => twoValued (1 : ZMod p) (-1) (x c)).finrank (ZMod p) ≤ k - t - 1)]
  refine (prob_setFinrank_sign_le (k := k) (r := k - t - 1) hF (by omega)).trans ?_
  have h3 : k - (k - t - 1) = t + 1 := by omega
  rw [h3]
  have h4 : (2 : ℝ) ^ (k - t - 1) * 2 ^ (t + 1) ≤ 2 ^ nR := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h5 : (2 : ℝ) ^ (k - t - 1) / 2 ^ nR ≤ ((1 : ℝ) / 2) ^ (t + 1) := by
    rw [_root_.one_div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    exact h4
  rw [pow_mul]
  gcongr

theorem prob_BP_le (hp2 : p ≠ 2) (ha : a0 ≠ 0 ∨ a1 ≠ 0) (t : ℕ) :
    prob (BP (p := p) a0 a1 U t) ≤ 30 * (2 : ℝ) ^ (-(((t + 1 : ℕ) : ℝ) ^ 2 / 4)) := by
  by_cases ha1 : a1 = 0
  · have ha0 : a0 ≠ 0 := ha.resolve_right (not_not.2 ha1)
    have h0 : ∀ ω : Pairs m → Bool, ¬ BP (p := p) a0 a1 U t ω := by
      intro ω h
      unfold BP at h
      rw [PUmat_eq, ha1, zero_smul, zero_add] at h
      have hc : corank (a0 • (1 : Matrix (Fin U.card) (Fin U.card) (ZMod p))) = 0 := by
        unfold corank
        rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
        intro v hv
        rw [LinearMap.mem_ker, mulVecLin_apply, smul_mulVec, one_mulVec] at hv
        exact (smul_eq_zero.1 hv).resolve_left ha0
      omega
    rw [prob_congr (Q := fun _ => False) fun ω => ⟨h0 ω, False.elim⟩, prob_false]
    positivity
  · set ϑ : ZMod p := -a0 / a1 with hϑ
    have hPU : ∀ ω : Pairs m → Bool, corank (PUmat (PAm a0 a1 (modP p (seidelOf ω))) (eUOf U)) =
        geomMult (F := ZMod p) 1 (-1) ϑ (ω ∘ blkU U) := by
      intro ω
      rw [PUmat_eq]
      have e : a1 • modP p (seidelOf (ω ∘ blkU U)) + a0 • (1 : Matrix (Fin U.card) (Fin U.card) (ZMod p)) =
          a1 • shiftedMat (F := ZMod p) 1 (-1) ϑ (ω ∘ blkU U) := by
        show _ = a1 • (modP p (seidelOf (ω ∘ blkU U)) - ϑ • 1)
        rw [smul_sub, smul_smul, show a1 * ϑ = -a0 by rw [hϑ]; field_simp, neg_smul, sub_neg_eq_add]
      rw [e]
      have hker : LinearMap.ker (a1 • shiftedMat (F := ZMod p) 1 (-1) ϑ (ω ∘ blkU U)).mulVecLin =
          LinearMap.ker (shiftedMat (F := ZMod p) 1 (-1) ϑ (ω ∘ blkU U)).mulVecLin := by
        ext v
        rw [LinearMap.mem_ker, LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply, smul_mulVec,
          smul_eq_zero, or_iff_right ha1]
      unfold geomMult corank
      rw [hker]
    have hev : ∀ ω : Pairs m → Bool, BP (p := p) a0 a1 U t ω ↔
        (fun ω' : Pairs U.card → Bool => t + 1 ≤ geomMult (F := ZMod p) 1 (-1) ϑ ω') (ω ∘ blkU U) := by
      intro ω
      unfold BP
      rw [hPU]
    rw [prob_congr hev]
    refine (le_of_eq (prob_comp_injective (blkU U) (blkU_injective U)
      (fun ω' : Pairs U.card → Bool => t + 1 ≤ geomMult (F := ZMod p) 1 (-1) ϑ ω'))).trans ?_
    have hab : ((1 : ℤ) : ZMod p) ≠ ((-1 : ℤ) : ZMod p) := by
      push_cast
      exact one_ne_neg_one_zmod hp2
    exact lem_apriori_tail hab ϑ U.card (t + 1)

theorem prob_BK_good_le (hp2 : p ≠ 2) (hRU : Disjoint R U) {t : ℕ}
    (hnum : (Rᶜ.card : ℝ) + 0.13 * m ≤ (U.card : ℝ) + ((R.card / 2 : ℕ) : ℝ) - 4 * t) :
    prob (fun ω => BK b0 b1 a0 a1 U R ω ∧ (¬ BW (p := p) R t ω ∧ ¬ BP (p := p) a0 a1 U t ω)) ≤
      2 ^ (R.card / 2) * ((1 : ℝ) / 2) ^ ((t + 1) * (t + 1)) := by
  classical
  set k := R.card / 2 with hk
  set nU := U.card with hnU
  set nR := Rᶜ.card with hnR
  have hF : (1 : ZMod p) ≠ -1 := one_ne_neg_one_zmod hp2
  refine prob_and_le_of_replace (blk1 R) (blk1_injective R) (by positivity) (fun ω x => ?_)
    (fun ω hω => ?_)
  · unfold BW BP
    rw [Wrow_replace1, PUmat_replace1 _ _ _ _ _ hRU]
  · obtain ⟨hW, hP⟩ := hω
    unfold BW at hW
    unfold BP at hP
    push Not at hW hP
    set K' : (Fin k × Fin k → Bool) → Matrix (Fin m) (Fin nR ⊕ Fin nU) (ZMod p) :=
      fun x => Kof p b0 b1 a0 a1 U R (replace (blk1 R) (blk1_injective R) ω x) with hK'
    have hL0 : ∀ x, Submodule.span (ZMod p) (Set.range fun b => K' x (eUOf U b)) =
        Submodule.span (ZMod p) (Set.range fun b => Kof p b0 b1 a0 a1 U R ω (eUOf U b)) := by
      intro x
      have e : (fun b => K' x (eUOf U b)) = fun b => Kof p b0 b1 a0 a1 U R ω (eUOf U b) :=
        funext fun b => Kof_replace_U _ _ _ _ _ _ _ hRU ω x b
      rw [e]
    have hPU : ∀ x b, projU (K' x (eUOf U b)) = PUmat (PAm a0 a1 (modP p (seidelOf ω))) (eUOf U) b := by
      intro x b
      have e : K' x (eUOf U b) = Kof p b0 b1 a0 a1 U R ω (eUOf U b) := Kof_replace_U _ _ _ _ _ _ _ hRU ω x b
      rw [e]
      exact projU_Kmat _ _ _ _ _
    have hrow : ∀ x a, K' x (e1Of R a) = Fintype.linearCombination (ZMod p)
        (fun c => (Sum.elim (Wrow p R ω c) 0 : Fin nR ⊕ Fin nU → ZMod p))
          (twoValued (1 : ZMod p) (-1) fun c => x (a, c)) +
        (Kof p b0 b1 a0 a1 U R ω (e1Of R a) - Fintype.linearCombination (ZMod p)
          (Wvec p U R ω) (fun c => modP p (seidelOf ω) (e1Of R a) (e2Of R c))) :=
      fun x a => Kof_replace_row _ _ _ _ _ _ _ hRU ω x a
    have hrP : corank (PUmat (PAm a0 a1 (modP p (seidelOf ω))) (eUOf U)) ≤ t := by omega
    have hWt : k ≤ (Set.range (Wrow p R ω)).finrank (ZMod p) + t := by omega
    have hgen := prob_rank_small_generic hF K' (eUOf U) (e1Of R) _ hL0 _ hPU (Wrow p R ω) _ hrow hrP hWt
    refine le_trans (prob_mono fun x hx => ?_) hgen
    have hx' : ((K' x).rank : ℝ) < (nR : ℝ) + 0.13 * m := hx
    by_contra hcon
    push Not at hcon
    have h5 : ((nU + k : ℕ) : ℝ) ≤ ((K' x).rank : ℝ) + 4 * t := by exact_mod_cast hcon
    push_cast at h5
    linarith

end OneChoice

end DGS
