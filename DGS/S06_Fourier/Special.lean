module

public import DGS.S06_Fourier.Robust
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

open Matrix

namespace DGS

variable {p : ℕ} [hp : Fact p.Prime] {E : ℕ} {N m : ℕ}

def cij (X Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) (i j : Fin N) : ZMod (p ^ E) :=
  X i ⬝ᵥ Y j + X j ⬝ᵥ Y i

def nuX (X Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) : ℕ :=
  (Finset.univ.filter fun q : Pairs N => cij X Y q.1.1 q.1.2 ≠ 0).card

open Classical in
noncomputable def tX (X Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) : ℕ :=
  sInf {k | ∃ K : Matrix (Fin m) (Fin m) (ZMod (p ^ E)), Kᵀ = -K ∧
    (Finset.univ.filter fun i => X i ≠ (Y * K) i).card = k}

omit hp in
theorem cij_comm (X Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) (i j : Fin N) :
    cij X Y i j = cij X Y j i := by
  rw [cij, cij, add_comm]

omit hp in
theorem cij_mul_antisymm (Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E)))
    {K : Matrix (Fin m) (Fin m) (ZMod (p ^ E))} (hK : Kᵀ = -K) (i j : Fin N) :
    cij (Y * K) Y i j = 0 := by
  have hK' : ∀ a b, K a b = -K b a := fun a b => by
    have := congrFun (congrFun hK b) a
    simpa [transpose_apply] using this
  simp only [cij, dotProduct, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun x y => Y j y * K y x * Y i x)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [hK' b a]; ring

omit hp in
theorem cij_sub_mul_antisymm (X Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E)))
    {K : Matrix (Fin m) (Fin m) (ZMod (p ^ E))} (hK : Kᵀ = -K) (i j : Fin N) :
    cij (X - Y * K) Y i j = cij X Y i j := by
  have h := cij_mul_antisymm Y hK i j
  simp only [cij] at h ⊢
  rw [show (X - Y * K) i = X i - (Y * K) i from rfl, show (X - Y * K) j = X j - (Y * K) j from rfl,
    sub_dotProduct, sub_dotProduct]
  linear_combination -h

omit hp in
open Classical in
theorem tX_mem (X Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) :
    ∃ K : Matrix (Fin m) (Fin m) (ZMod (p ^ E)), Kᵀ = -K ∧
      (Finset.univ.filter fun i => X i ≠ (Y * K) i).card = tX X Y := by
  unfold tX
  have hne : Set.Nonempty {k | ∃ K : Matrix (Fin m) (Fin m) (ZMod (p ^ E)), Kᵀ = -K ∧
      (Finset.univ.filter fun i => X i ≠ (Y * K) i).card = k} :=
    ⟨_, 0, by simp, rfl⟩
  exact Nat.sInf_mem hne

omit hp in
open Classical in
theorem tX_le (X Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) {K : Matrix (Fin m) (Fin m) (ZMod (p ^ E))}
    (hK : Kᵀ = -K) : tX X Y ≤ (Finset.univ.filter fun i => X i ≠ (Y * K) i).card :=
  Nat.sInf_le ⟨K, hK, rfl⟩

omit hp in
theorem card_ordered_le (X Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) (S : Finset (Fin N × Fin N))
    (hS : ∀ q ∈ S, q.1 ≠ q.2 ∧ cij X Y q.1 q.2 ≠ 0) : S.card ≤ 2 * nuX X Y := by
  classical
  let f : Fin N × Fin N → Fin N × Fin N := fun q => (min q.1 q.2, max q.1 q.2)
  have hmaps : ∀ q ∈ S, f q ∈ (Finset.univ.filter fun q : Pairs N => cij X Y q.1.1 q.1.2 ≠ 0).image
      Subtype.val := by
    intro q hq
    obtain ⟨hne, hc⟩ := hS q hq
    rw [Finset.mem_image]
    refine ⟨⟨f q, ?_⟩, ?_, rfl⟩
    · show min q.1 q.2 < max q.1 q.2
      rcases lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left h.le, max_eq_right h.le]; exact h
      · rw [min_eq_right h.le, max_eq_left h.le]; exact h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show cij X Y (min q.1 q.2) (max q.1 q.2) ≠ 0
      rcases le_total q.1 q.2 with h | h
      · rw [min_eq_left h, max_eq_right h]; exact hc
      · rw [min_eq_right h, max_eq_left h, cij_comm]; exact hc
  have h1 := Finset.card_le_mul_card_image_of_maps_to hmaps 2 ?_
  · rw [Finset.card_image_of_injective _ Subtype.val_injective] at h1
    exact h1
  · intro b _
    have : (S.filter fun q => f q = b) ⊆ {b, (b.2, b.1)} := by
      intro q hq
      simp only [Finset.mem_filter] at hq
      obtain ⟨hqS, hqb⟩ := hq
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [← hqb]
      rcases le_total q.1 q.2 with h | h
      · left; simp [f, min_eq_left h, max_eq_right h]
      · right; simp [f, min_eq_right h, max_eq_left h]
    exact (Finset.card_le_card this).trans Finset.card_le_two

omit hp in
theorem card_le_nu_of_injOn (X Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E)))
    (S : Finset (Fin N × Fin N)) (hS : ∀ q ∈ S, q.1 ≠ q.2 ∧ cij X Y q.1 q.2 ≠ 0)
    (hinj : Set.InjOn (fun q : Fin N × Fin N => (min q.1 q.2, max q.1 q.2)) S) :
    S.card ≤ nuX X Y := by
  classical
  let f : Fin N × Fin N → Fin N × Fin N := fun q => (min q.1 q.2, max q.1 q.2)
  have hmaps : ∀ q ∈ S, f q ∈ (Finset.univ.filter fun q : Pairs N => cij X Y q.1.1 q.1.2 ≠ 0).image
      Subtype.val := by
    intro q hq
    obtain ⟨hne, hc⟩ := hS q hq
    rw [Finset.mem_image]
    refine ⟨⟨f q, ?_⟩, ?_, rfl⟩
    · show min q.1 q.2 < max q.1 q.2
      rcases lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left h.le, max_eq_right h.le]; exact h
      · rw [min_eq_right h.le, max_eq_left h.le]; exact h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show cij X Y (min q.1 q.2) (max q.1 q.2) ≠ 0
      rcases le_total q.1 q.2 with h | h
      · rw [min_eq_left h, max_eq_right h]; exact hc
      · rw [min_eq_right h, max_eq_left h, cij_comm]; exact hc
  calc S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((Finset.univ.filter fun q : Pairs N => cij X Y q.1.1 q.1.2 ≠ 0).image Subtype.val).card :=
        Finset.card_le_card fun x hx => by
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
          exact hmaps q hq
    _ = nuX X Y := Finset.card_image_of_injective _ Subtype.val_injective

theorem step1 (hE : 1 ≤ E) {s : ℕ} {Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))}
    (hY : IsRobustE p E s Y) (X : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) :
    tX X Y * (s - tX X Y) ≤ nuX X Y := by
  classical
  obtain ⟨K0, hK0, hcard⟩ := tX_mem X Y
  set X' := X - Y * K0 with hX'
  set P := Finset.univ.filter fun i => X i ≠ (Y * K0) i with hPdef
  have hP : ∀ i, i ∈ P ↔ X' i ≠ 0 := by
    intro i
    simp only [hPdef, Finset.mem_filter, Finset.mem_univ, true_and, hX', Ne]
    rw [show (X - Y * K0) i = X i - (Y * K0) i from rfl, sub_eq_zero]
  have hc : ∀ i j, cij X Y i j = cij X' Y i j := fun i j => (cij_sub_mul_antisymm X Y hK0 i j).symm
  set T := Finset.univ \ P
  set S := (P ×ˢ T).filter fun q => cij X Y q.1 q.2 ≠ 0 with hSdef
  have hmemS : ∀ q, q ∈ S ↔ q.1 ∈ P ∧ q.2 ∉ P ∧ cij X Y q.1 q.2 ≠ 0 := by
    intro q
    simp [hSdef, T, Finset.mem_product, Finset.mem_sdiff, and_assoc]
  have hSν : S.card ≤ nuX X Y := by
    refine card_le_nu_of_injOn X Y S (fun q hq => ?_) ?_
    · obtain ⟨h1, h2, h3⟩ := (hmemS q).1 hq
      exact ⟨fun h => h2 (h ▸ h1), h3⟩
    · intro q hq q' hq' hqq
      have hq1 := (hmemS q).1 hq
      have hq1' := (hmemS q').1 hq'
      simp only [Prod.mk.injEq] at hqq
      obtain ⟨hmin, hmax⟩ := hqq
      rcases le_total q.1 q.2 with h | h <;> rcases le_total q'.1 q'.2 with h' | h'
      · rw [min_eq_left h, min_eq_left h'] at hmin
        rw [max_eq_right h, max_eq_right h'] at hmax
        exact Prod.ext hmin hmax
      · rw [min_eq_left h, min_eq_right h'] at hmin
        exact absurd (hmin ▸ hq1.1) hq1'.2.1
      · rw [min_eq_right h, min_eq_left h'] at hmin
        exact absurd (hmin.symm ▸ hq1'.1) hq1.2.1
      · rw [min_eq_right h, min_eq_right h'] at hmin
        rw [max_eq_left h, max_eq_left h'] at hmax
        exact Prod.ext hmax hmin
  have hrow : ∀ i ∈ P, s - tX X Y ≤ (T.filter fun j => cij X Y i j ≠ 0).card := by
    intro i hi
    have hX'i : X' i ≠ 0 := (hP i).1 hi
    have hrob := robust_lift hE hY hX'i
    set Ti := Finset.univ.filter fun j => (Y *ᵥ X' i) j ≠ 0
    have hsub : Ti \ P ⊆ T.filter fun j => cij X Y i j ≠ 0 := by
      intro j hj
      rw [Finset.mem_sdiff] at hj
      obtain ⟨hjT, hjP⟩ := hj
      simp only [Ti, Finset.mem_filter, Finset.mem_univ, true_and] at hjT
      simp only [T, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      refine ⟨hjP, ?_⟩
      rw [hc, cij]
      have hX'j : X' j = 0 := by by_contra h; exact hjP ((hP j).2 h)
      rw [hX'j, zero_dotProduct, add_zero, dotProduct_comm]
      exact hjT
    calc s - tX X Y ≤ Ti.card - P.card := by
          rw [← hcard]; exact Nat.sub_le_sub_right hrob _
      _ ≤ (Ti \ P).card := Finset.le_card_sdiff _ _
      _ ≤ _ := Finset.card_le_card hsub
  have hScard : S.card = ∑ i ∈ P, (T.filter fun j => cij X Y i j ≠ 0).card := by
    rw [hSdef, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.card_filter]
  have hge : tX X Y * (s - tX X Y) ≤ S.card := by
    rw [hScard]
    have := Finset.card_nsmul_le_sum P (fun i => (T.filter fun j => cij X Y i j ≠ 0).card)
      (s - tX X Y) hrow
    rw [smul_eq_mul, hcard] at this
    exact this
  exact hge.trans hSν

theorem isUnit_of_cast_ne_zero {x : ZMod (p ^ E)} (hx : (x.cast : ZMod p) ≠ 0) : IsUnit x := by
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  have h1 : (x.cast : ZMod p) = ((x.val : ℕ) : ZMod p) := (ZMod.natCast_val x).symm
  rw [h1, Ne, ZMod.natCast_eq_zero_iff] at hx
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
  exact ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hx).symm.pow_right E

theorem exists_good_rows {F : Type*} [Field F] [DecidableEq F] {s : ℕ}
    {Yb : Matrix (Fin N) (Fin m) F} (hY : IsRobust s Yb) (H : Finset (Fin N))
    (nb : Fin N → Finset (Fin N)) (hsymm : ∀ i j, j ∈ nb i → i ∈ nb j) (hirr : ∀ i, i ∉ nb i)
    (hdeg : ∀ i, i ∉ H → 8 * m * (nb i).card ≤ s) (hH : 4 * H.card < s) :
    ∀ k ≤ m, ∃ b : Fin k → Fin N, (∀ l, b l ∉ H) ∧ (∀ l l', b l' ∉ nb (b l)) ∧
      LinearIndependent F (fun l => Yb (b l)) := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨Fin.elim0, fun l => l.elim0, fun l => l.elim0, linearIndependent_empty_type⟩
  | succ k ih =>
    intro hk
    obtain ⟨b, hbH, hbR, hbli⟩ := ih (by omega)
    let Mb : Matrix (Fin k) (Fin m) F := fun l => Yb (b l)
    have hker : LinearMap.ker Mb.mulVecLin ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt (by simp only [Module.finrank_fin_fun]; omega)
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hYbu : ∀ l, Yb (b l) ⬝ᵥ u = 0 := fun l => by
      have := congrFun (LinearMap.mem_ker.1 hu) l
      exact this
    set Nb := Finset.univ.biUnion fun l => nb (b l) with hNb
    set C := ((Finset.univ.filter fun j => (Yb *ᵥ u) j ≠ 0) \ H) \ Nb with hC
    have hs := hY u hu0
    have hNbcard : 8 * m * Nb.card ≤ k * s := by
      calc 8 * m * Nb.card ≤ 8 * m * ∑ l, (nb (b l)).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ l : Fin k, 8 * m * (nb (b l)).card := by rw [Finset.mul_sum]
        _ ≤ ∑ _l : Fin k, s := Finset.sum_le_sum fun l _ => hdeg _ (hbH l)
        _ = k * s := by simp
    have hwt : wt (Yb *ᵥ u) ≤ C.card + H.card + Nb.card := by
      unfold wt
      calc _ ≤ (C ∪ H ∪ Nb).card := Finset.card_le_card (by
            intro j hj
            by_cases hjH : j ∈ H
            · simp [hjH]
            by_cases hjN : j ∈ Nb
            · simp [hjN]
            simp only [Finset.mem_union]
            left; left
            simp only [hC, Finset.mem_sdiff]
            exact ⟨⟨hj, hjH⟩, hjN⟩)
        _ ≤ (C ∪ H).card + Nb.card := Finset.card_union_le _ _
        _ ≤ C.card + H.card + Nb.card := by
            have := Finset.card_union_le C H; omega
    have hCpos : 0 < C.card := by
      by_contra h0
      have h2 : s ≤ H.card + Nb.card := by omega
      have h3 : m * s ≤ m * H.card + m * Nb.card := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left m h2
      have h4 : m * (4 * H.card + 1) ≤ m * s := Nat.mul_le_mul_left m hH
      have h5 : (k + 1) * s ≤ m * s := Nat.mul_le_mul_right s hk
      nlinarith
    obtain ⟨j, hj⟩ := Finset.card_pos.1 hCpos
    simp only [hC, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨⟨hju, hjH⟩, hjN⟩ := hj
    have hjN' : ∀ l, j ∉ nb (b l) := fun l h => hjN (by
      rw [hNb, Finset.mem_biUnion]; exact ⟨l, Finset.mem_univ _, h⟩)
    refine ⟨Fin.snoc b j, ?_, ?_, ?_⟩
    · intro l
      refine Fin.lastCases ?_ (fun l => ?_) l
      · simpa using hjH
      · simpa using hbH l
    · intro l l'
      refine Fin.lastCases ?_ (fun l => ?_) l <;> refine Fin.lastCases ?_ (fun l' => ?_) l'
      · simpa using hirr j
      · simpa using fun h => hjN' l' (hsymm _ _ h)
      · simpa using hjN' l
      · simpa using hbR l l'
    · have key : LinearIndependent F
          (Fin.snoc (α := fun _ => Fin m → F) (fun l => Yb (b l)) (Yb j)) := by
        rw [linearIndependent_finSnoc]
        refine ⟨hbli, fun hmem => hju ?_⟩
        have h0 : ∀ v ∈ Submodule.span F (Set.range fun l => Yb (b l)), v ⬝ᵥ u = 0 := by
          intro v hv
          induction hv using Submodule.span_induction with
          | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hYbu l
          | zero => exact zero_dotProduct u
          | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
          | smul a x _ hx => rw [smul_dotProduct, hx, smul_zero]
        exact h0 _ hmem
      convert key using 1
      exact Fin.comp_snoc Yb b j

theorem step2 (hE : 1 ≤ E) {s : ℕ} {Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))}
    (hY : IsRobustE p E s Y) (hm : 1 ≤ m) (hs : 16 * m ≤ s)
    (X : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) (ht : s < 2 * tX X Y) :
    s ^ 2 ≤ 64 * m * nuX X Y := by
  classical
  by_contra hν
  push Not at hν
  have hY' : IsRobust s (Y.map (ZMod.cast : ZMod (p ^ E) → ZMod p)) := hY
  obtain ⟨K0, hK0, hcard⟩ := tX_mem X Y
  set X' := X - Y * K0 with hX'
  have hc : ∀ i j, cij X Y i j = cij X' Y i j := fun i j =>
    (cij_sub_mul_antisymm X Y hK0 i j).symm
  set nb : Fin N → Finset (Fin N) := fun i =>
    Finset.univ.filter fun j => j ≠ i ∧ cij X Y i j ≠ 0 with hnb
  have hmem_nb : ∀ i j, j ∈ nb i ↔ j ≠ i ∧ cij X Y i j ≠ 0 := fun i j => by
    simp [hnb]
  have hsymm : ∀ i j, j ∈ nb i → i ∈ nb j := fun i j h => by
    rw [hmem_nb] at h ⊢; exact ⟨h.1.symm, by rw [cij_comm]; exact h.2⟩
  have hirr : ∀ i, i ∉ nb i := fun i h => ((hmem_nb i i).1 h).1 rfl
  set H := Finset.univ.filter fun i => s < 8 * m * (nb i).card with hHdef
  have hHsum : ∑ i ∈ H, (nb i).card ≤ 2 * nuX X Y := by
    have h := card_ordered_le X Y
      ((H ×ˢ Finset.univ).filter fun q : Fin N × Fin N => q.2 ≠ q.1 ∧ cij X Y q.1 q.2 ≠ 0)
      (fun q hq => by
        simp only [Finset.mem_filter] at hq
        exact ⟨hq.2.1.symm, hq.2.2⟩)
    calc ∑ i ∈ H, (nb i).card = ((H ×ˢ Finset.univ).filter
          fun q : Fin N × Fin N => q.2 ≠ q.1 ∧ cij X Y q.1 q.2 ≠ 0).card := by
          rw [Finset.card_filter, Finset.sum_product]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hnb, Finset.card_filter]
      _ ≤ _ := h
  have hdeg : ∀ i, i ∉ H → 8 * m * (nb i).card ≤ s := by
    intro i hi
    simp only [hHdef, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    exact hi
  have hH : 4 * H.card < s := by
    have h1 : s * H.card ≤ 8 * m * ∑ i ∈ H, (nb i).card := by
      calc s * H.card = ∑ _i ∈ H, s := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ i ∈ H, 8 * m * (nb i).card := Finset.sum_le_sum fun i hi => by
            simp only [hHdef, Finset.mem_filter] at hi; exact hi.2.le
        _ = _ := by rw [Finset.mul_sum]
    by_contra h
    push Not at h
    have h2 : s * s ≤ s * (4 * H.card) := Nat.mul_le_mul_left s h
    have h3 : 8 * m * ∑ i ∈ H, (nb i).card ≤ 8 * m * (2 * nuX X Y) := Nat.mul_le_mul_left _ hHsum
    nlinarith
  obtain ⟨b, hbH, hbnb, hbli⟩ := exists_good_rows hY' H nb hsymm hirr hdeg hH m le_rfl
  set MB : Matrix (Fin m) (Fin m) (ZMod (p ^ E)) := fun l => Y (b l) with hMB
  have hMBdet : IsUnit MB.det := by
    have h1 : IsUnit (MB.map (ZMod.cast : ZMod (p ^ E) → ZMod p)) :=
      Matrix.linearIndependent_row_iff_isUnit.1 hbli
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at h1
    apply isUnit_of_cast_ne_zero
    rw [← redHom_apply hE MB.det, RingHom.map_det]
    convert h1 using 2
    ext a c
    simp [RingHom.mapMatrix_apply, redHom_apply]
  set X'B : Matrix (Fin m) (Fin m) (ZMod (p ^ E)) := fun l => X' (b l) with hX'B
  set K : Matrix (Fin m) (Fin m) (ZMod (p ^ E)) := -X'Bᵀ * MBᵀ⁻¹ with hK
  have hKMB : K * MBᵀ = -X'Bᵀ := by
    rw [hK, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (by rw [det_transpose]; exact hMBdet), Matrix.mul_one]
  have hKcol : ∀ l, K *ᵥ Y (b l) = -X' (b l) := by
    intro l; funext k
    have := congrFun (congrFun hKMB k) l
    simp only [Matrix.mul_apply, transpose_apply] at this
    exact this
  set Γ := Finset.univ.filter fun j => (∀ l, b l ≠ j) ∧ ∀ l, j ∉ nb (b l) with hΓ
  have hΓc : 8 * (Finset.univ \ Γ).card ≤ 8 * m + s := by
    have hsub : Finset.univ \ Γ ⊆ Finset.univ.image b ∪ Finset.univ.biUnion fun l => nb (b l) := by
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
      by_cases h : ∃ l, b l = j
      · obtain ⟨l, hl⟩ := h
        exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨l, Finset.mem_univ _, hl⟩)
      · push Not at h
        have : ∃ l, j ∈ nb (b l) := by
          by_contra h'
          push Not at h'
          exact hj (by simp only [hΓ, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h, h'⟩)
        obtain ⟨l, hl⟩ := this
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, hl⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (Finset.univ.image b) (Finset.univ.biUnion fun l => nb (b l))
    have h3 : (Finset.univ.image b).card ≤ m := Finset.card_image_le.trans (by simp)
    have h4 : 8 * m * (Finset.univ.biUnion fun l => nb (b l)).card ≤ m * s := by
      calc 8 * m * (Finset.univ.biUnion fun l => nb (b l)).card ≤ 8 * m * ∑ l, (nb (b l)).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ l, 8 * m * (nb (b l)).card := by rw [Finset.mul_sum]
        _ ≤ ∑ _l : Fin m, s := Finset.sum_le_sum fun l _ => hdeg _ (hbH l)
        _ = m * s := by simp
    have h5 : 8 * (Finset.univ.biUnion fun l => nb (b l)).card ≤ s := by
      have h6 : m * (8 * (Finset.univ.biUnion fun l => nb (b l)).card) ≤ m * s := by linarith
      exact Nat.le_of_mul_le_mul_left h6 (by omega)
    omega
  have hX'Γ : ∀ j ∈ Γ, X' j = (Y * K) j := by
    intro j hj
    simp only [hΓ, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hjb, hjnb⟩ := hj
    set v := X' j - Y j ᵥ* K with hv
    have hMv : MB *ᵥ v = 0 := by
      funext l
      have hcjl : cij X Y j (b l) = 0 := by
        by_contra h
        exact hjnb l ((hmem_nb (b l) j).2 ⟨(hjb l).symm, by rw [cij_comm]; exact h⟩)
      rw [hc, cij] at hcjl
      change Y (b l) ⬝ᵥ v = 0
      rw [hv, dotProduct_sub, dotProduct_comm (Y (b l)) (Y j ᵥ* K), ← dotProduct_mulVec, hKcol,
        dotProduct_neg, dotProduct_comm (Y (b l)) (X' j), dotProduct_comm (Y j) (X' (b l))]
      linear_combination hcjl
    have hv0 : v = 0 := by
      rw [← one_mulVec v, ← Matrix.nonsing_inv_mul MB hMBdet, ← mulVec_mulVec, hMv, mulVec_zero]
    rw [hv, sub_eq_zero] at hv0
    exact hv0
  set L := K + Kᵀ with hL
  have hcΓ : ∀ j ∈ Γ, ∀ j' ∈ Γ, cij X Y j j' = Y j ⬝ᵥ (L *ᵥ Y j') := by
    intro j hj j' hj'
    rw [hc, cij, hX'Γ j hj, hX'Γ j' hj']
    show (Y j ᵥ* K) ⬝ᵥ Y j' + (Y j' ᵥ* K) ⬝ᵥ Y j = Y j ⬝ᵥ (L *ᵥ Y j')
    rw [hL, add_mulVec, dotProduct_add, ← dotProduct_mulVec, ← dotProduct_mulVec, mulVec_transpose,
      dotProduct_comm (Y j) (Y j' ᵥ* K), ← dotProduct_mulVec]
  by_cases hL0 : L = 0
  ·
    have hKt : Kᵀ = -K := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hL0
    have hK1 : (K0 + K)ᵀ = -(K0 + K) := by rw [transpose_add, hK0, hKt, neg_add]
    have hle := tX_le X Y hK1
    have hsub : (Finset.univ.filter fun i => X i ≠ (Y * (K0 + K)) i) ⊆ Finset.univ \ Γ := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro hiΓ
      apply hi
      have h1 := hX'Γ i hiΓ
      have h2 : X' i = X i - (Y * K0) i := rfl
      rw [Matrix.mul_add]
      show X i = (Y * K0) i + (Y * K) i
      rw [← h1, h2]; abel
    have := Finset.card_le_card hsub
    omega
  ·
    obtain ⟨k, hk⟩ : ∃ k, L k ≠ 0 := by
      by_contra h; push Not at h; exact hL0 (funext h)
    have hrob1 := robust_lift hE hY hk
    set J' := Γ.filter fun j' => L *ᵥ Y j' ≠ 0 with hJ'
    have hJ'card : s ≤ J'.card + (Finset.univ \ Γ).card := by
      refine hrob1.trans ?_
      unfold wt
      calc _ ≤ (J' ∪ (Finset.univ \ Γ)).card := Finset.card_le_card (by
            intro j' hj'
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
            by_cases hj'Γ : j' ∈ Γ
            · refine Finset.mem_union_left _ ?_
              rw [hJ', Finset.mem_filter]
              refine ⟨hj'Γ, fun h0 => hj' ?_⟩
              have h1 : (Y *ᵥ L k) j' = (L *ᵥ Y j') k := dotProduct_comm _ _
              rw [h1, h0, Pi.zero_apply]
            · exact Finset.mem_union_right _ (by simp [hj'Γ]))
        _ ≤ _ := Finset.card_union_le _ _
    set Fb : Fin N → Finset (Fin N) := fun j' =>
      Finset.univ.filter fun j => j ∈ Γ ∧ j ≠ j' ∧ cij X Y j' j ≠ 0 with hFb
    have hfib : ∀ j' ∈ J', s ≤ (Fb j').card + (Finset.univ \ Γ).card + 1 := by
      intro j' hj'
      rw [hJ', Finset.mem_filter] at hj'
      obtain ⟨hj'Γ, hj'L⟩ := hj'
      have hrob2 := robust_lift hE hY hj'L
      refine hrob2.trans ?_
      unfold wt
      calc _ ≤ (Fb j' ∪ (Finset.univ \ Γ) ∪ {j'}).card := Finset.card_le_card (by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            by_cases hjΓ : j ∈ Γ
            · by_cases hjj : j = j'
              · simp [hjj]
              · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
                simp only [hFb, Finset.mem_filter, Finset.mem_univ, true_and]
                refine ⟨hjΓ, hjj, ?_⟩
                rw [cij_comm, hcΓ j hjΓ j' hj'Γ]
                exact hj
            · simp [hjΓ])
        _ ≤ (Fb j' ∪ (Finset.univ \ Γ)).card + 1 := by
            have := Finset.card_union_le (Fb j' ∪ (Finset.univ \ Γ)) {j'}
            simpa using this
        _ ≤ _ := by
            have := Finset.card_union_le (Fb j') (Finset.univ \ Γ); omega
    set S2 := (J' ×ˢ Finset.univ).filter
      fun q : Fin N × Fin N => q.2 ∈ Γ ∧ q.2 ≠ q.1 ∧ cij X Y q.1 q.2 ≠ 0 with hS2
    have hS2ν : S2.card ≤ 2 * nuX X Y :=
      card_ordered_le X Y S2 fun q hq => by
        rw [hS2, Finset.mem_filter] at hq
        exact ⟨hq.2.2.1.symm, hq.2.2.2⟩
    have hS2card : S2.card = ∑ j' ∈ J', (Fb j').card := by
      rw [hS2, Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun j' _ => ?_
      simp only [hFb, Finset.card_filter]
    have hS2ge : J'.card * (s - (Finset.univ \ Γ).card - 1) ≤ S2.card := by
      rw [hS2card]
      have := Finset.card_nsmul_le_sum J' (fun j' => (Fb j').card)
        (s - (Finset.univ \ Γ).card - 1) (fun j' hj' => by have := hfib j' hj'; omega)
      rw [smul_eq_mul] at this
      exact this
    set g := (Finset.univ \ Γ).card
    set a := J'.card
    have hc4 : 3 * s ≤ 4 * (s - g - 1) := by omega
    have hac : s - g - 1 ≤ a := by omega
    have h1 : (s - g - 1) * (s - g - 1) ≤ a * (s - g - 1) := Nat.mul_le_mul_right _ hac
    have h2 : (3 * s) * (3 * s) ≤ (4 * (s - g - 1)) * (4 * (s - g - 1)) := Nat.mul_le_mul hc4 hc4
    have h3 : 1 * nuX X Y ≤ m * nuX X Y := Nat.mul_le_mul_right _ hm
    nlinarith

theorem lem_special_nat (hE : 1 ≤ E) {s : ℕ} {Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))}
    (hY : IsRobustE p E s Y) (hm : 1 ≤ m) (hs : 16 * m ≤ s)
    (X : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) :
    tX X Y * s ≤ 2 * nuX X Y ∨ s ^ 2 ≤ 64 * m * nuX X Y := by
  by_cases ht : 2 * tX X Y ≤ s
  · left
    have h1 := step1 hE hY X
    have h2 : tX X Y * s ≤ 2 * (tX X Y * (s - tX X Y)) := by
      have : s ≤ 2 * (s - tX X Y) := by omega
      calc tX X Y * s ≤ tX X Y * (2 * (s - tX X Y)) := Nat.mul_le_mul_left _ this
        _ = 2 * (tX X Y * (s - tX X Y)) := by ring
    omega
  · right
    exact step2 hE hY hm hs X (by omega)

theorem lem_special (hE : 1 ≤ E) {s : ℕ} {Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))}
    (hY : IsRobustE p E s Y) (hm : 1 ≤ m) (hs : 16 * m ≤ s)
    (X : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) :
    min ((tX X Y : ℝ) * s / 2) ((s : ℝ) ^ 2 / (64 * m)) ≤ nuX X Y := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm' : (0 : ℝ) < 64 * m := by linarith
  rcases lem_special_nat hE hY hm hs X with h | h
  · refine (min_le_left _ _).trans ?_
    have : ((tX X Y * s : ℕ) : ℝ) ≤ ((2 * nuX X Y : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  · refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ hm']
    have : ((s ^ 2 : ℕ) : ℝ) ≤ ((64 * m * nuX X Y : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith

theorem nuX_eq_zero_iff (hE : 1 ≤ E) {s : ℕ} {Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))}
    (hY : IsRobustE p E s Y) (hm : 1 ≤ m) (hs : 16 * m ≤ s)
    (X : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) :
    nuX X Y = 0 ↔ ∃ K : Matrix (Fin m) (Fin m) (ZMod (p ^ E)), Kᵀ = -K ∧ X = Y * K := by
  classical
  constructor
  · intro h0
    rcases lem_special_nat hE hY hm hs X with h | h
    · rw [h0] at h
      have ht : tX X Y = 0 := by
        rcases Nat.eq_zero_or_pos (tX X Y) with h' | h'
        · exact h'
        · have : 0 < tX X Y * s := Nat.mul_pos h' (by omega)
          omega
      obtain ⟨K, hK, hcard⟩ := tX_mem X Y
      rw [ht, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcard
      refine ⟨K, hK, ?_⟩
      ext i k
      by_contra hik
      exact hcard (Finset.mem_univ i) (fun h => hik (congrFun h k))
    · rw [h0] at h
      have : 0 < s ^ 2 := pow_pos (by omega) 2
      omega
  · rintro ⟨K, hK, rfl⟩
    unfold nuX
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro q _
    rw [not_not]
    exact cij_mul_antisymm Y hK _ _

end DGS
