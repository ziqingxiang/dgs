module

public import DGS.S07_Small.Tight
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section

open Polynomial Matrix Finset

namespace DGS

section OneVar

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicValInt_lt_of_not_dvd {a : ℤ} {m : ℕ} (ha : ¬ (p : ℤ) ^ m ∣ a) :
    a ≠ 0 ∧ padicValInt p a < m := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha (dvd_zero _)
  refine ⟨ha0, ?_⟩
  by_contra h
  push Not at h
  exact ha ((padicValInt_dvd_iff m a).2 (Or.inr h))

theorem padicValInt_prod_le {ι : Type*} (s : Finset ι) (g : ι → ℤ) {B : ℕ}
    (hg : ∀ i ∈ s, g i ≠ 0 ∧ padicValInt p (g i) ≤ B) :
    (∏ i ∈ s, g i) ≠ 0 ∧ padicValInt p (∏ i ∈ s, g i) ≤ s.card * B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have hga := hg a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine ⟨mul_ne_zero hga.1 ih'.1, ?_⟩
    rw [padicValInt.mul hga.1 ih'.1, add_mul, one_mul]
    omega

theorem dvd_det_vandermonde_mul_coeff {f : ℤ[X]} {D : ℕ} (hfD : f.natDegree ≤ D)
    (v : Fin (D + 1) → ℤ) {P : ℤ} (hv : ∀ i, P ∣ f.eval (v i)) (l : ℕ) :
    P ∣ (vandermonde v).det * f.coeff l := by
  by_cases hl : D < l
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]; exact dvd_zero _
  push Not at hl
  set c : Fin (D + 1) → ℤ := fun j => f.coeff j with hc
  have hVc : vandermonde v *ᵥ c = fun i => f.eval (v i) := by
    funext i
    rw [eval_eq_sum_range' (n := D + 1) (by omega)]
    simp only [mulVec, dotProduct, vandermonde_apply, hc]
    rw [Fin.sum_univ_eq_sum_range (fun j => v i ^ j * f.coeff j) (D + 1)]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h1 : (vandermonde v).det • c = (vandermonde v).adjugate *ᵥ (fun i => f.eval (v i)) := by
    rw [← hVc, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  have h2 := congrFun h1 ⟨l, by omega⟩
  simp only [Pi.smul_apply, smul_eq_mul, hc] at h2
  rw [h2]
  simp only [mulVec, dotProduct]
  exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hv i) _

omit hp in
theorem not_pow_dvd_sub_of_mod_ne {m y z : ℕ} (h : y % p ^ m ≠ z % p ^ m) :
    ¬ (p : ℤ) ^ m ∣ (z : ℤ) - (y : ℤ) := by
  intro hd
  apply h
  have : y ≡ z [MOD p ^ m] := by
    rw [Nat.modEq_iff_dvd]
    exact_mod_cast hd
  exact this

theorem card_root_le {f : ℤ[X]} {D : ℕ} (hfD : f.natDegree ≤ D) {c : ℕ}
    (hc : ∃ j, ¬ (p : ℤ) ^ c ∣ f.coeff j) {m e E : ℕ} (hm : m ≤ E)
    (he : c + (D + 1) ^ 2 * m ≤ e) :
    (univ.filter fun y : Fin (p ^ E) => (p : ℤ) ^ e ∣ f.eval ((y : ℕ) : ℤ)).card ≤
      D * p ^ (E - m) := by
  classical
  have hpm : 0 < p ^ m := pow_pos hp.out.pos m
  set S := univ.filter fun y : Fin (p ^ E) => (p : ℤ) ^ e ∣ f.eval ((y : ℕ) : ℤ) with hS
  set π : Fin (p ^ E) → Fin (p ^ m) := fun y => ⟨(y : ℕ) % p ^ m, Nat.mod_lt _ hpm⟩ with hπ
  have himage : (S.image π).card ≤ D := by
    by_contra hcon
    push Not at hcon
    obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq (show D + 1 ≤ (S.image π).card by
      omega)
    have hrep : ∀ z ∈ U, ∃ y ∈ S, π y = z := fun z hz => Finset.mem_image.1 (hUsub hz)
    choose! rep hrepS hrepπ using hrep
    have hUc : Fintype.card U = D + 1 := by rw [Fintype.card_coe, hUcard]
    set eU := (Fintype.equivFinOfCardEq hUc).symm with heU
    set w : Fin (D + 1) → Fin (p ^ E) := fun i => rep (eU i : Fin (p ^ m)) with hw
    set v : Fin (D + 1) → ℤ := fun i => ((w i : ℕ) : ℤ) with hv
    have hvS : ∀ i, (p : ℤ) ^ e ∣ f.eval (v i) := by
      intro i
      have := hrepS _ (eU i).2
      rw [hS, Finset.mem_filter] at this
      exact this.2
    have hdist : ∀ i j, i ≠ j → ¬ (p : ℤ) ^ m ∣ v j - v i := by
      intro i j hij
      apply not_pow_dvd_sub_of_mod_ne
      intro h
      apply hij
      have h1 : π (w i) = π (w j) := Fin.ext h
      rw [hw] at h1
      simp only at h1
      rw [hrepπ _ (eU i).2, hrepπ _ (eU j).2] at h1
      exact eU.injective (Subtype.ext h1)
    have hdet : (vandermonde v).det ≠ 0 ∧
        padicValInt p (vandermonde v).det ≤ (D + 1) * ((D + 1) * m) := by
      rw [det_vandermonde]
      have h := padicValInt_prod_le (p := p) (univ : Finset (Fin (D + 1)))
        (fun i => ∏ j ∈ Ioi i, (v j - v i)) (B := (D + 1) * m) fun i _ => by
          have h2 := padicValInt_prod_le (p := p) (Ioi i) (fun j => v j - v i) (B := m)
            fun j hj => by
              have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.1 hj)
              have := padicValInt_lt_of_not_dvd (hdist i j hij)
              exact ⟨this.1, this.2.le⟩
          refine ⟨h2.1, h2.2.trans ?_⟩
          have hcard : (Ioi i).card ≤ D + 1 := by
            calc (Ioi i).card ≤ (univ : Finset (Fin (D + 1))).card := card_le_univ _
              _ = D + 1 := by rw [card_univ, Fintype.card_fin]
          exact Nat.mul_le_mul_right _ hcard
      rw [card_univ, Fintype.card_fin] at h
      exact h
    obtain ⟨j0, hj0⟩ := hc
    have hdvd := dvd_det_vandermonde_mul_coeff hfD v hvS j0
    have hf0 : f.coeff j0 ≠ 0 := by rintro h; rw [h] at hj0; exact hj0 (dvd_zero _)
    rcases (padicValInt_dvd_iff e _).1 hdvd with h0 | h0
    · exact mul_ne_zero hdet.1 hf0 h0
    · rw [padicValInt.mul hdet.1 hf0] at h0
      apply hj0
      rw [padicValInt_dvd_iff]
      right
      have : (D + 1) * ((D + 1) * m) = (D + 1) ^ 2 * m := by ring
      omega
  have hfib : ∀ z ∈ S.image π, (S.filter fun y => π y = z).card ≤ p ^ (E - m) := by
    intro z _
    have hinj : Set.InjOn (fun y : Fin (p ^ E) => ((y : ℕ) / p ^ m))
        ((S.filter fun y => π y = z) : Set (Fin (p ^ E))) := by
      intro y hy y' hy' h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hy hy'
      have h1 : (y : ℕ) % p ^ m = (y' : ℕ) % p ^ m := by
        have := hy.2.trans hy'.2.symm
        exact congrArg Fin.val this
      apply Fin.ext
      rw [← Nat.mod_add_div (y : ℕ) (p ^ m), ← Nat.mod_add_div (y' : ℕ) (p ^ m), h1]
      simp only at h
      rw [h]
    have hmaps : Set.MapsTo (fun y : Fin (p ^ E) => ((y : ℕ) / p ^ m))
        ((S.filter fun y => π y = z) : Set (Fin (p ^ E))) (range (p ^ (E - m)) : Set ℕ) := by
      intro y _
      simp only [coe_range, Set.mem_Iio]
      rw [Nat.div_lt_iff_lt_mul hpm, ← pow_add, Nat.sub_add_cancel hm]
      exact y.2
    calc (S.filter fun y => π y = z).card ≤ (range (p ^ (E - m))).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = p ^ (E - m) := card_range _
  calc S.card ≤ p ^ (E - m) * (S.image π).card := Finset.card_le_mul_card_image S _ hfib
    _ ≤ p ^ (E - m) * D := Nat.mul_le_mul_left _ himage
    _ = D * p ^ (E - m) := mul_comm _ _

end OneVar

section MultiVar

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def zcount (E e : ℕ) {t : ℕ} (F : MvPolynomial (Fin t) ℤ) : ℕ :=
  (univ.filter fun x : Fin t → Fin (p ^ E) =>
    (p : ℤ) ^ e ∣ MvPolynomial.eval (fun i => ((x i : ℕ) : ℤ)) F).card

theorem cons_coe_eq {t : ℕ} {q : ℕ} (y : Fin q) (x' : Fin t → Fin q) :
    (fun i => (((Fin.cons y x' : Fin (t + 1) → Fin q) i : ℕ) : ℤ)) =
      Fin.cons ((y : ℕ) : ℤ) (fun i => ((x' i : ℕ) : ℤ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

theorem zcount_le : ∀ (t : ℕ) (F : MvPolynomial (Fin t) ℤ), F ≠ 0 → ∀ ε : ℝ, 0 < ε →
    ∃ c0 : ℕ, ∀ e E : ℕ, c0 ≤ e → e ≤ E → (zcount p E e F : ℝ) ≤ ε * (p : ℝ) ^ (E * t) := by
  intro t
  induction t with
  | zero =>
    intro F hF ε hε
    set a := F.coeff 0 with ha
    have hFa : F = MvPolynomial.C a := MvPolynomial.eq_C_of_isEmpty F
    have ha0 : a ≠ 0 := fun h => hF (by rw [hFa, h, map_zero])
    refine ⟨padicValInt p a + 1, fun e E he _ => ?_⟩
    have h0 : zcount p E e F = 0 := by
      rw [zcount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ hdvd
      rw [hFa, MvPolynomial.eval_C] at hdvd
      rcases (padicValInt_dvd_iff e a).1 hdvd with h | h
      · exact ha0 h
      · omega
    rw [h0, Nat.cast_zero]
    positivity
  | succ t ih =>
    intro F hF ε hε
    classical
    set P := MvPolynomial.finSuccEquiv ℤ t F with hP
    have hP0 : P ≠ 0 := fun h =>
      hF ((MvPolynomial.finSuccEquiv ℤ t).injective (by rw [← hP, h, map_zero]))
    set D := P.natDegree with hD
    set G := P.leadingCoeff with hG
    have hG0 : G ≠ 0 := leadingCoeff_ne_zero.2 hP0
    obtain ⟨c1, hc1⟩ := ih G hG0 (ε / 2) (by positivity)
    obtain ⟨m, hm⟩ := exists_nat_gt (2 * D / ε)
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    have hpm : 2 * (D : ℝ) / ε < (p : ℝ) ^ m :=
      hm.trans (by exact_mod_cast Nat.lt_pow_self hp.out.one_lt)
    refine ⟨c1 + (D + 1) ^ 2 * m, fun e E he heE => ?_⟩
    have hmE : m ≤ E := by
      have : m ≤ (D + 1) ^ 2 * m := Nat.le_mul_of_pos_left m (by positivity)
      omega
    have hc1E : c1 ≤ E := by omega
    set q := p ^ E with hq
    set cnt : (Fin t → Fin q) → ℕ := fun x' => (univ.filter fun y : Fin q =>
      (p : ℤ) ^ e ∣ (P.map (MvPolynomial.eval fun i => ((x' i : ℕ) : ℤ))).eval ((y : ℕ) : ℤ)).card
      with hcnt
    have hdecomp : zcount p E e F = ∑ x' : Fin t → Fin q, cnt x' := by
      rw [zcount, Finset.card_filter]
      rw [← (Fin.consEquiv (fun _ : Fin (t + 1) => Fin q)).sum_comp]
      rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun x' _ => ?_
      simp only [hcnt]
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Fin.consEquiv_apply]
      rw [cons_coe_eq, MvPolynomial.eval_eq_eval_mv_eval']
    have hslice : ∀ x' : Fin t → Fin q, (cnt x' : ℝ) ≤ D * (p : ℝ) ^ (E - m) +
        (q : ℝ) * (if (p : ℤ) ^ c1 ∣ MvPolynomial.eval (fun i => ((x' i : ℕ) : ℤ)) G
          then 1 else 0) := by
      intro x'
      set f := P.map (MvPolynomial.eval fun i => ((x' i : ℕ) : ℤ)) with hf
      by_cases hdiv : (p : ℤ) ^ c1 ∣ MvPolynomial.eval (fun i => ((x' i : ℕ) : ℤ)) G
      · rw [ite_eq_left hdiv, mul_one]
        have : (cnt x' : ℝ) ≤ q := by
          have h1 : cnt x' ≤ q := by
            calc cnt x' ≤ (univ : Finset (Fin q)).card := Finset.card_filter_le _ _
              _ = q := by rw [card_univ, Fintype.card_fin]
          exact_mod_cast h1
        have h0 : (0 : ℝ) ≤ D * (p : ℝ) ^ (E - m) := by positivity
        linarith
      · rw [ite_eq_right hdiv, mul_zero, add_zero]
        have hfD : f.natDegree ≤ D := natDegree_map_le
        have hcoef : ∃ j, ¬ (p : ℤ) ^ c1 ∣ f.coeff j := by
          refine ⟨D, ?_⟩
          rw [hf, coeff_map]
          exact hdiv
        have h1 := card_root_le hfD hcoef hmE (by omega : c1 + (D + 1) ^ 2 * m ≤ e)
        have h2 : (cnt x' : ℝ) ≤ ((D * p ^ (E - m) : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at h2
        exact h2
    have hcount : ∑ x' : Fin t → Fin q,
        (if (p : ℤ) ^ c1 ∣ MvPolynomial.eval (fun i => ((x' i : ℕ) : ℤ)) G then (1 : ℝ) else 0) =
          zcount p E c1 G := by
      rw [zcount, Finset.card_filter]
      push_cast
      rfl
    have hIH := hc1 c1 E le_rfl hc1E
    have hpE : (q : ℝ) = (p : ℝ) ^ E := by rw [hq]; push_cast; rfl
    have hcardx : ((Fintype.card (Fin t → Fin q) : ℕ) : ℝ) = (p : ℝ) ^ (E * t) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hq]
      push_cast
      rw [← pow_mul]
    have hpos : (0 : ℝ) < (p : ℝ) ^ m := by positivity
    have hDm : (D : ℝ) * (p : ℝ) ^ (E - m) ≤ ε / 2 * (p : ℝ) ^ E := by
      have h1 : (p : ℝ) ^ E = (p : ℝ) ^ (E - m) * (p : ℝ) ^ m := by
        rw [← pow_add, Nat.sub_add_cancel hmE]
      have h2 : (D : ℝ) ≤ ε / 2 * (p : ℝ) ^ m := by
        rw [div_lt_iff₀ hε] at hpm
        nlinarith
      rw [h1]
      have h3 : (0 : ℝ) ≤ (p : ℝ) ^ (E - m) := by positivity
      nlinarith
    calc (zcount p E e F : ℝ) = ∑ x' : Fin t → Fin q, (cnt x' : ℝ) := by
          rw [hdecomp]; push_cast; rfl
      _ ≤ ∑ x' : Fin t → Fin q, (D * (p : ℝ) ^ (E - m) + (q : ℝ) *
          (if (p : ℤ) ^ c1 ∣ MvPolynomial.eval (fun i => ((x' i : ℕ) : ℤ)) G then 1 else 0)) :=
          Finset.sum_le_sum fun x' _ => hslice x'
      _ = (p : ℝ) ^ (E * t) * (D * (p : ℝ) ^ (E - m)) + (q : ℝ) * zcount p E c1 G := by
          rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, hcount, card_univ,
            nsmul_eq_mul, hcardx]
      _ ≤ (p : ℝ) ^ (E * t) * (ε / 2 * (p : ℝ) ^ E) + (p : ℝ) ^ E * (ε / 2 * (p : ℝ) ^ (E * t)) := by
          rw [hpE]
          gcongr
      _ = ε * (p : ℝ) ^ (E * (t + 1)) := by
          rw [mul_add, mul_one, pow_add]
          ring

theorem zeroDensity {σ : Type*} [Fintype σ] [DecidableEq σ] (F : MvPolynomial σ ℤ) (hF : F ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ E0 : ℕ, ∀ E ≥ E0, ((univ.filter fun x : σ → ZMod (p ^ E) =>
      MvPolynomial.eval₂ (Int.castRingHom (ZMod (p ^ E))) x F = 0).card : ℝ) ≤
        ε * (p : ℝ) ^ (E * Fintype.card σ) := by
  classical
  set t := Fintype.card σ with ht
  set eσ := Fintype.equivFin σ with heσ
  set F' := MvPolynomial.rename eσ F with hF'
  have hF'0 : F' ≠ 0 := fun h =>
    hF (MvPolynomial.rename_injective eσ eσ.injective (by rw [← hF', h, map_zero]))
  obtain ⟨c0, hc0⟩ := zcount_le p t F' hF'0 ε hε
  refine ⟨c0, fun E hE => ?_⟩
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  have hcount : (univ.filter fun x : σ → ZMod (p ^ E) =>
      MvPolynomial.eval₂ (Int.castRingHom (ZMod (p ^ E))) x F = 0).card = zcount p E E F' := by
    rw [zcount]
    have hpE : ((p : ℤ) ^ E) = ((p ^ E : ℕ) : ℤ) := by push_cast; rfl
    have hev : ∀ g : σ → ℤ, ((MvPolynomial.eval g F : ℤ) : ZMod (p ^ E)) =
        MvPolynomial.eval₂ (Int.castRingHom (ZMod (p ^ E)))
          (fun s => ((g s : ℤ) : ZMod (p ^ E))) F := by
      intro g
      have h3 := MvPolynomial.eval₂_comp_left (Int.castRingHom (ZMod (p ^ E))) (RingHom.id ℤ) g F
      rw [RingHom.comp_id] at h3
      rw [← eq_intCast (Int.castRingHom (ZMod (p ^ E)))]
      exact h3
    refine Finset.card_bij' (fun x _ => fun i => (⟨(x (eσ.symm i)).val, ZMod.val_lt _⟩ : Fin (p ^ E)))
      (fun y _ => fun s => (((y (eσ s) : ℕ)) : ZMod (p ^ E))) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have h1 : MvPolynomial.eval (fun i => (((x (eσ.symm i)).val : ℕ) : ℤ)) F' =
          MvPolynomial.eval (fun s => (((x s).val : ℕ) : ℤ)) F := by
        rw [hF', MvPolynomial.eval_rename]
        simp only [Function.comp_def, Equiv.symm_apply_apply]
      rw [h1, hpE, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hev]
      convert hx using 2
      funext s
      simp
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      have h1 : MvPolynomial.eval (fun i => ((y i : ℕ) : ℤ)) F' =
          MvPolynomial.eval (fun s => ((y (eσ s) : ℕ) : ℤ)) F := by
        rw [hF', MvPolynomial.eval_rename]
        rfl
      rw [h1, hpE, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hev] at hy
      convert hy using 2
      funext s
      simp
    · intro x _
      funext s
      simp
    · intro y _
      funext i
      apply Fin.ext
      simp only [Equiv.apply_symm_apply]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (y i).2]
  rw [hcount]
  exact hc0 E E hE le_rfl

end MultiVar

end DGS
