module

public import DGS.S06_Fourier.Special
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Normed.Ring.Finite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open Matrix Complex
open scoped Real

namespace DGS

section Char

theorem addChar_map_sum {A M : Type*} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M)
    {ι : Type*} (s : Finset ι) (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, ih, Finset.prod_insert ha]

variable {q : ℕ} [NeZero q]

theorem sum_stdAddChar_dot {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → ZMod q) :
    ∑ x : ι → ZMod q, ZMod.stdAddChar (∑ i, x i * M i) =
      if M = 0 then (q : ℂ) ^ Fintype.card ι else 0 := by
  simp_rw [addChar_map_sum]
  rw [← Fintype.prod_sum (fun i (y : ZMod q) => ZMod.stdAddChar (y * M i))]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), ZMod.card]
  split_ifs with hM
  · simp [hM]
  · obtain ⟨i, hi⟩ : ∃ i, M i ≠ 0 := by
      by_contra h; push Not at h; exact hM (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

def matDot {R : Type*} [CommRing R] {n m : ℕ} (X M : Matrix (Fin n) (Fin m) R) : R :=
  ∑ i, ∑ k, X i k * M i k

theorem matDot_sub {R : Type*} [CommRing R] {n m : ℕ} (X M M' : Matrix (Fin n) (Fin m) R) :
    matDot X (M - M') = matDot X M - matDot X M' := by
  simp only [matDot, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem sum_stdAddChar_matDot {n m : ℕ} (M : Matrix (Fin n) (Fin m) (ZMod q)) :
    ∑ X : Matrix (Fin n) (Fin m) (ZMod q), ZMod.stdAddChar (matDot X M) =
      if M = 0 then (q : ℂ) ^ (n * m) else 0 := by
  have h1 : ∀ X : Matrix (Fin n) (Fin m) (ZMod q), ZMod.stdAddChar (matDot X M) =
      ∏ i, ZMod.stdAddChar (∑ k, X i k * M i k) := fun X => addChar_map_sum _ _ _
  simp_rw [h1]
  rw [show (∑ X : Matrix (Fin n) (Fin m) (ZMod q), ∏ i, ZMod.stdAddChar (∑ k, X i k * M i k)) =
      ∑ X : Fin n → Fin m → ZMod q, ∏ i, ZMod.stdAddChar (∑ k, X i k * M i k) from rfl]
  rw [← Fintype.prod_sum (fun i (x : Fin m → ZMod q) => ZMod.stdAddChar (∑ k, x k * M i k))]
  simp_rw [sum_stdAddChar_dot, Fintype.card_fin]
  split_ifs with hM
  · have h2 : ∀ i : Fin n, (if M i = 0 then (q : ℂ) ^ m else 0) = (q : ℂ) ^ m := fun i => by
      rw [hM]; exact ite_eq_left rfl
    simp_rw [h2]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
  · obtain ⟨i, hi⟩ : ∃ i, M i ≠ 0 := by
      by_contra h; push Not at h; exact hM (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem card_filter_eq_zero_le {Ω : Type*} [Fintype Ω] {n m : ℕ}
    (M : Ω → Matrix (Fin n) (Fin m) (ZMod q)) :
    ((Finset.univ.filter fun ω => M ω = 0).card : ℝ) ≤
      ((q : ℝ) ^ (n * m))⁻¹ * ∑ X : Matrix (Fin n) (Fin m) (ZMod q),
        ‖∑ ω, ZMod.stdAddChar (matDot X (M ω))‖ := by
  classical
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have h1 : ((Finset.univ.filter fun ω => M ω = 0).card : ℂ) =
      ((q : ℂ) ^ (n * m))⁻¹ * ∑ X : Matrix (Fin n) (Fin m) (ZMod q),
        ∑ ω, ZMod.stdAddChar (matDot X (M ω)) := by
    rw [Finset.sum_comm]
    simp_rw [sum_stdAddChar_matDot]
    rw [Finset.card_filter]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs
    · rw [inv_mul_cancel₀ (pow_ne_zero _ hq)]
    · rw [mul_zero]
  have h2 : ((Finset.univ.filter fun ω => M ω = 0).card : ℝ) =
      ‖((Finset.univ.filter fun ω => M ω = 0).card : ℂ)‖ := by
    rw [Complex.norm_natCast]
  rw [h2, h1, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  gcongr
  exact norm_sum_le _ _

end Char

section Tau

noncomputable def tauq (q : ℕ) : ℝ := Real.cos (π / q)

theorem tauq_le_one (q : ℕ) : tauq q ≤ 1 := Real.cos_le_one _

theorem tauq_nonneg {q : ℕ} (hq : 2 ≤ q) : 0 ≤ tauq q := by
  unfold tauq
  apply Real.cos_nonneg_of_mem_Icc
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : 0 ≤ π / q := by positivity
  have h2 : π / q ≤ π / 2 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hq'
  constructor <;> linarith [Real.pi_pos]

theorem norm_one_add_stdAddChar_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) {c : ZMod q} (hc : c ≠ 0) :
    ‖1 + ZMod.stdAddChar c‖ ≤ 2 * tauq q := by
  have hv1 : 1 ≤ c.val := Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero])
  have hv2 : c.val < q := ZMod.val_lt c
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set θ : ℝ := π * c.val / q with hθ
  have hexp : ZMod.stdAddChar c = Complex.exp (2 * ((θ : ℂ) * I)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, hθ]
    congr 1
    push_cast
    ring
  have hfac : 1 + Complex.exp (2 * ((θ : ℂ) * I)) =
      Complex.exp ((θ : ℂ) * I) * ((2 * Real.cos θ : ℝ) : ℂ) := by
    push_cast
    rw [Complex.two_cos, mul_add, ← Complex.exp_add, ← Complex.exp_add]
    have h1 : (θ : ℂ) * I + θ * I = 2 * (θ * I) := by ring
    have h2 : (θ : ℂ) * I + -θ * I = 0 := by ring
    rw [h1, h2, Complex.exp_zero, add_comm]
  rw [hexp, hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_two]
  have hv1' : (1 : ℝ) ≤ c.val := by exact_mod_cast hv1
  have hv2' : (c.val : ℝ) + 1 ≤ q := by exact_mod_cast hv2
  have hθ1 : π / q ≤ θ := by
    rw [hθ, div_le_div_iff_of_pos_right hq0]
    nlinarith [Real.pi_pos]
  have hθ2 : θ ≤ π - π / q := by
    have h1 : θ + π / q = π * (c.val + 1) / q := by rw [hθ]; field_simp
    have h2 : π * (c.val + 1) / q ≤ π := by
      rw [div_le_iff₀ hq0]; nlinarith [Real.pi_pos]
    linarith
  have hpq : 0 ≤ π / q := by positivity
  have hc1 : Real.cos θ ≤ Real.cos (π / q) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hpq (by linarith) hθ1
  have hc2 : -Real.cos θ ≤ Real.cos (π / q) := by
    rw [← Real.cos_pi_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hpq (by linarith) (by linarith)
  unfold tauq
  have := abs_le.2 ⟨by linarith, hc1⟩
  linarith

end Tau

section Trace

theorem sum_ite_lt {R : Type*} [AddCommMonoid R] {n : ℕ} (g : Fin n × Fin n → R) :
    ∑ x : Fin n × Fin n, (if x.1 < x.2 then g x else 0) = ∑ q : Pairs n, g q.1 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun x => by simp) g

theorem sum_eq_sum_pairs {R : Type*} [AddCommMonoid R] {n : ℕ} (f : Fin n → Fin n → R)
    (hf : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j = ∑ q : Pairs n, (f q.1.1 q.1.2 + f q.1.2 q.1.1) := by
  rw [Finset.sum_add_distrib, ← sum_ite_lt (fun x => f x.1 x.2), ← sum_ite_lt (fun x => f x.2 x.1),
    ← Fintype.sum_prod_type']
  have hswap : ∑ x : Fin n × Fin n, (if x.1 < x.2 then f x.2 x.1 else 0) =
      ∑ x : Fin n × Fin n, (if x.2 < x.1 then f x.1 x.2 else 0) :=
    Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun x => rfl)
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases lt_trichotomy x.1 x.2 with h | h | h
  · simp [h, not_lt.2 h.le]
  · simp [h, hf]
  · simp [h, not_lt.2 h.le]

variable {p : ℕ} [hp : Fact p.Prime] {E : ℕ} {n m : ℕ}

omit hp in
theorem matDot_symOf_mul (ω : Pairs n → Bool) (X Y : Matrix (Fin n) (Fin m) (ZMod (p ^ E))) :
    matDot X (modP (p ^ E) (symOf 1 0 ω) * Y) =
      ∑ pr : Pairs n, (if ω pr then 1 else 0) * cij X Y pr.1.1 pr.1.2 := by
  set A := modP (p ^ E) (symOf 1 0 ω) with hA
  have h1 : matDot X (A * Y) = ∑ i, ∑ j, A i j * (X i ⬝ᵥ Y j) := by
    unfold matDot
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mul_apply, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h1, sum_eq_sum_pairs _ (fun i => by simp [hA, modP])]
  refine Finset.sum_congr rfl fun pr _ => ?_
  have hlt := pr.2
  have h2 : A pr.1.1 pr.1.2 = if ω pr then 1 else 0 := by
    simp only [hA, modP, Matrix.map_apply, symOf_apply_lt 1 0 ω hlt]
    split_ifs <;> simp
  have h3 : A pr.1.2 pr.1.1 = if ω pr then 1 else 0 := by
    simp only [hA, modP, Matrix.map_apply, symOf_apply_gt 1 0 ω hlt]
    split_ifs <;> simp
  rw [h2, h3, cij]
  ring

theorem sum_omega_stdAddChar (X Y : Matrix (Fin n) (Fin m) (ZMod (p ^ E))) :
    ∑ ω : Pairs n → Bool, ZMod.stdAddChar (matDot X (modP (p ^ E) (symOf 1 0 ω) * Y)) =
      ∏ pr : Pairs n, (ZMod.stdAddChar (cij X Y pr.1.1 pr.1.2) + 1) := by
  classical
  simp_rw [matDot_symOf_mul, addChar_map_sum]
  have h1 : ∀ pr : Pairs n, ZMod.stdAddChar (cij X Y pr.1.1 pr.1.2) + 1 =
      ∑ b : Bool, ZMod.stdAddChar ((if b then 1 else 0) * cij X Y pr.1.1 pr.1.2) := by
    intro pr
    rw [Fintype.sum_bool]
    simp [AddChar.map_zero_eq_one]
  simp_rw [h1]
  rw [Fintype.prod_sum]

theorem norm_sum_omega_le (hq2 : 2 ≤ p ^ E) (X Y : Matrix (Fin n) (Fin m) (ZMod (p ^ E))) :
    ‖∑ ω : Pairs n → Bool, ZMod.stdAddChar (matDot X (modP (p ^ E) (symOf 1 0 ω) * Y))‖ ≤
      2 ^ Fintype.card (Pairs n) * tauq (p ^ E) ^ nuX X Y := by
  classical
  rw [sum_omega_stdAddChar, norm_prod]
  have h1 : ∀ pr : Pairs n, ‖ZMod.stdAddChar (cij X Y pr.1.1 pr.1.2) + 1‖ ≤
      2 * (if cij X Y pr.1.1 pr.1.2 ≠ 0 then tauq (p ^ E) else 1) := by
    intro pr
    split_ifs with hc
    · rw [add_comm]; exact norm_one_add_stdAddChar_le hq2 hc
    · rw [not_not] at hc
      rw [hc, AddChar.map_zero_eq_one, one_add_one_eq_two, Complex.norm_two, mul_one]
  calc ∏ pr : Pairs n, ‖ZMod.stdAddChar (cij X Y pr.1.1 pr.1.2) + 1‖
      ≤ ∏ pr : Pairs n, 2 * (if cij X Y pr.1.1 pr.1.2 ≠ 0 then tauq (p ^ E) else 1) := by
        apply Finset.prod_le_prod₀
        · intro pr _; exact norm_nonneg _
        · intro pr _; exact h1 pr
    _ = 2 ^ Fintype.card (Pairs n) * tauq (p ^ E) ^ nuX X Y := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_ite,
          Finset.prod_const_one, mul_one, Finset.prod_const, nuX]

end Trace

section Count

theorem prob_eq_card_filter {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] :
    prob P = ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω := by
  unfold prob
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]

variable {q : ℕ} [NeZero q] {n m : ℕ}

def nzRows (X : Fin n → Fin m → ZMod q) : ℕ := (Finset.univ.filter fun i => X i ≠ 0).card

theorem sum_pow_nz (w : ℝ) :
    ∑ X : Fin n → Fin m → ZMod q, w ^ nzRows X =
      (∑ x : Fin m → ZMod q, if x ≠ 0 then w else 1) ^ n := by
  have h1 : ∀ X : Fin n → Fin m → ZMod q, w ^ nzRows X = ∏ i, (if X i ≠ 0 then w else 1) := by
    intro X
    rw [nzRows, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun _ (x : Fin m → ZMod q) => if x ≠ 0 then w else 1)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem sum_ite_ne_zero_le {w : ℝ} (hw : 0 ≤ w) :
    ∑ x : Fin m → ZMod q, (if x ≠ 0 then w else 1) ≤ 1 + (q : ℝ) ^ m * w := by
  classical
  calc ∑ x : Fin m → ZMod q, (if x ≠ 0 then w else 1)
      ≤ ∑ x : Fin m → ZMod q, (w + if x = 0 then 1 else 0) :=
        Finset.sum_le_sum fun x _ => by split_ifs with h1 h2 <;> first | linarith | simp_all
    _ = 1 + (q : ℝ) ^ m * w := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Finset.sum_ite_eq',
          ite_eq_left (Finset.mem_univ _), nsmul_eq_mul, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        push_cast; ring

variable {p : ℕ} [hp : Fact p.Prime] {E : ℕ}

theorem sum_pow_tX_le (Y : Matrix (Fin n) (Fin m) (ZMod (p ^ E))) {w : ℝ} (hw : 0 ≤ w) :
    ∑ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)), w ^ tX X Y ≤
      (antisymm m (p ^ E)).card * (1 + ((p ^ E : ℕ) : ℝ) ^ m * w) ^ n := by
  classical
  have ht : ∀ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)),
      ∃ K ∈ antisymm m (p ^ E), tX X Y = nzRows (X - Y * K).row := by
    intro X
    obtain ⟨K, hK, hKcard⟩ := tX_mem X Y
    refine ⟨K, (mem_antisymm m (p ^ E)).2 hK, ?_⟩
    rw [← hKcard]
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show X i ≠ (Y * K) i ↔ X i - (Y * K) i ≠ 0
    rw [Ne, Ne, sub_eq_zero]
  have hle : ∀ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)),
      w ^ tX X Y ≤ ∑ K ∈ antisymm m (p ^ E), w ^ nzRows (X - Y * K).row := by
    intro X
    obtain ⟨K, hK, hKt⟩ := ht X
    rw [hKt]
    exact Finset.single_le_sum (f := fun K => w ^ nzRows (X - Y * K).row)
      (fun K _ => by positivity) hK
  have htrans : ∀ K : Matrix (Fin m) (Fin m) (ZMod (p ^ E)),
      ∑ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)), w ^ nzRows (X - Y * K).row =
        ∑ X : Fin n → Fin m → ZMod (p ^ E), w ^ nzRows X := by
    intro K
    rw [Fintype.sum_equiv (Equiv.subRight (Y * K)) (fun X => w ^ nzRows (X - Y * K).row)
      (fun X => w ^ nzRows X.row) (fun X => rfl)]
    exact Fintype.sum_equiv Matrix.of.symm _ _ (fun X => rfl)
  calc ∑ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)), w ^ tX X Y
      ≤ ∑ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)),
          ∑ K ∈ antisymm m (p ^ E), w ^ nzRows (X - Y * K).row :=
        Finset.sum_le_sum fun X _ => hle X
    _ = ∑ K ∈ antisymm m (p ^ E),
          ∑ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)), w ^ nzRows (X - Y * K).row :=
        Finset.sum_comm
    _ = ∑ _K ∈ antisymm m (p ^ E), ∑ X : Fin n → Fin m → ZMod (p ^ E), w ^ nzRows X :=
        Finset.sum_congr rfl fun K _ => htrans K
    _ = (antisymm m (p ^ E)).card * ∑ X : Fin n → Fin m → ZMod (p ^ E), w ^ nzRows X := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (antisymm m (p ^ E)).card * (1 + ((p ^ E : ℕ) : ℝ) ^ m * w) ^ n := by
        gcongr
        rw [sum_pow_nz]
        exact pow_le_pow_left₀ (Finset.sum_nonneg fun x _ => by split_ifs <;> linarith)
          (sum_ite_ne_zero_le hw) n

end Count

section Fourier

variable {p : ℕ} [hp : Fact p.Prime] {E : ℕ} {n m : ℕ}

theorem two_le_pow (hE : 1 ≤ E) : 2 ≤ p ^ E :=
  (Nat.Prime.two_le hp.out).trans (Nat.le_self_pow (by omega) p)

theorem prob_le_sum_tau (hE : 1 ≤ E) (Y Z : Matrix (Fin n) (Fin m) (ZMod (p ^ E))) :
    prob (fun ω : Pairs n → Bool => modP (p ^ E) (symOf 1 0 ω) * Y = Z) ≤
      (((p ^ E : ℕ) : ℝ) ^ (n * m))⁻¹ *
        ∑ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)), tauq (p ^ E) ^ nuX X Y := by
  classical
  have hq2 : 2 ≤ p ^ E := two_le_pow hE
  rw [prob_eq_card_filter]
  have hfil : (Finset.univ.filter fun ω : Pairs n → Bool => modP (p ^ E) (symOf 1 0 ω) * Y = Z) =
      Finset.univ.filter fun ω => modP (p ^ E) (symOf 1 0 ω) * Y - Z = 0 := by
    ext ω; simp [sub_eq_zero]
  rw [hfil]
  have h1 := card_filter_eq_zero_le (q := p ^ E)
    (fun ω : Pairs n → Bool => modP (p ^ E) (symOf 1 0 ω) * Y - Z)
  have h2 : ∀ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)),
      ‖∑ ω : Pairs n → Bool, ZMod.stdAddChar (matDot X (modP (p ^ E) (symOf 1 0 ω) * Y - Z))‖ ≤
        2 ^ Fintype.card (Pairs n) * tauq (p ^ E) ^ nuX X Y := by
    intro X
    have h3 : ∀ ω : Pairs n → Bool,
        ZMod.stdAddChar (matDot X (modP (p ^ E) (symOf 1 0 ω) * Y - Z)) =
          ZMod.stdAddChar (matDot X (modP (p ^ E) (symOf 1 0 ω) * Y)) /
            ZMod.stdAddChar (matDot X Z) := by
      intro ω; rw [matDot_sub, AddChar.map_sub_eq_div]
    simp_rw [h3]
    rw [← Finset.sum_div, norm_div, AddChar.norm_apply, div_one]
    exact norm_sum_omega_le hq2 X Y
  have hcard : (Fintype.card (Pairs n → Bool) : ℝ) = 2 ^ Fintype.card (Pairs n) := by
    rw [Fintype.card_fun, Fintype.card_bool]; push_cast; ring
  rw [hcard, div_le_iff₀ (by positivity)]
  calc _ ≤ _ := h1
    _ ≤ (((p ^ E : ℕ) : ℝ) ^ (n * m))⁻¹ * ∑ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)),
          2 ^ Fintype.card (Pairs n) * tauq (p ^ E) ^ nuX X Y := by
        gcongr with X
        exact h2 X
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem tau_pow_nu_le (hE : 1 ≤ E) {s : ℕ} {Y : Matrix (Fin n) (Fin m) (ZMod (p ^ E))}
    (hY : IsRobustE p E s Y) (hm : 1 ≤ m) (hs : 16 * m ≤ s)
    (X : Matrix (Fin n) (Fin m) (ZMod (p ^ E))) :
    tauq (p ^ E) ^ nuX X Y ≤
      tauq (p ^ E) ^ ((tX X Y : ℝ) * s / 2) + tauq (p ^ E) ^ ((s : ℝ) ^ 2 / (64 * m)) := by
  have hτ0 := tauq_nonneg (two_le_pow (p := p) hE)
  have hτ1 := tauq_le_one (p ^ E)
  rw [← Real.rpow_natCast]
  rcases lem_special_nat hE hY hm hs X with h | h
  · have h1 : (tX X Y : ℝ) * s / 2 ≤ nuX X Y := by
      have : ((tX X Y * s : ℕ) : ℝ) ≤ ((2 * nuX X Y : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this; linarith
    have h2 := Real.rpow_le_rpow_of_exponent_ge' hτ0 hτ1 (by positivity) h1
    have h3 : 0 ≤ tauq (p ^ E) ^ ((s : ℝ) ^ 2 / (64 * m)) := Real.rpow_nonneg hτ0 _
    linarith
  · have hm' : (0 : ℝ) < 64 * m := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have h1 : (s : ℝ) ^ 2 / (64 * m) ≤ nuX X Y := by
      rw [div_le_iff₀ hm']
      have : ((s ^ 2 : ℕ) : ℝ) ≤ ((64 * m * nuX X Y : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this; linarith
    have h2 := Real.rpow_le_rpow_of_exponent_ge' hτ0 hτ1 (by positivity) h1
    have h3 : 0 ≤ tauq (p ^ E) ^ ((tX X Y : ℝ) * s / 2) := Real.rpow_nonneg hτ0 _
    linarith

theorem sum_tau_tX_le (hE : 1 ≤ E) (s : ℕ) (Y : Matrix (Fin n) (Fin m) (ZMod (p ^ E))) :
    ∑ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)), tauq (p ^ E) ^ ((tX X Y : ℝ) * s / 2) ≤
      (antisymm m (p ^ E)).card *
        (1 + ((p ^ E : ℕ) : ℝ) ^ m * tauq (p ^ E) ^ ((s : ℝ) / 2)) ^ n := by
  have hτ0 := tauq_nonneg (two_le_pow (p := p) hE)
  have h1 : ∀ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)), tauq (p ^ E) ^ ((tX X Y : ℝ) * s / 2) =
      (tauq (p ^ E) ^ ((s : ℝ) / 2)) ^ tX X Y := by
    intro X
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ0]
    congr 1; ring
  simp_rw [h1]
  exact sum_pow_tX_le Y (Real.rpow_nonneg hτ0 _)

theorem lem_fourier_a (hE : 1 ≤ E) (hm : 1 ≤ m) {s : ℕ} (hs : 16 * m ≤ s)
    {Y : Matrix (Fin n) (Fin m) (ZMod (p ^ E))} (hY : IsRobustE p E s Y)
    (Z : Matrix (Fin n) (Fin m) (ZMod (p ^ E))) :
    prob (fun ω : Pairs n → Bool => modP (p ^ E) (symOf 1 0 ω) * Y = Z) ≤
      ((p : ℝ) ^ (E * n * m))⁻¹ * ((antisymm m (p ^ E)).card *
        (1 + (p : ℝ) ^ (E * m) * tauq (p ^ E) ^ ((s : ℝ) / 2)) ^ n +
        (p : ℝ) ^ (E * n * m) * tauq (p ^ E) ^ ((s : ℝ) ^ 2 / (64 * m))) := by
  have hqnm : ((p ^ E : ℕ) : ℝ) ^ (n * m) = (p : ℝ) ^ (E * n * m) := by
    push_cast; rw [← pow_mul, mul_assoc]
  have hqm : ((p ^ E : ℕ) : ℝ) ^ m = (p : ℝ) ^ (E * m) := by
    push_cast; rw [← pow_mul]
  have hcardM : (Fintype.card (Matrix (Fin n) (Fin m) (ZMod (p ^ E))) : ℝ) =
      (p : ℝ) ^ (E * n * m) := by
    rw [← hqnm, show Fintype.card (Matrix (Fin n) (Fin m) (ZMod (p ^ E))) =
      Fintype.card (Fin n → Fin m → ZMod (p ^ E)) from rfl, Fintype.card_fun, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, Fintype.card_fin]
    push_cast; ring
  refine (prob_le_sum_tau hE Y Z).trans ?_
  rw [hqnm]
  gcongr
  calc ∑ X, tauq (p ^ E) ^ nuX X Y
      ≤ ∑ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)), (tauq (p ^ E) ^ ((tX X Y : ℝ) * s / 2) +
          tauq (p ^ E) ^ ((s : ℝ) ^ 2 / (64 * m))) :=
        Finset.sum_le_sum fun X _ => tau_pow_nu_le hE hY hm hs X
    _ = ∑ X : Matrix (Fin n) (Fin m) (ZMod (p ^ E)), tauq (p ^ E) ^ ((tX X Y : ℝ) * s / 2) +
          (p : ℝ) ^ (E * n * m) * tauq (p ^ E) ^ ((s : ℝ) ^ 2 / (64 * m)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcardM]
    _ ≤ _ := by
        gcongr
        rw [← hqm]
        exact sum_tau_tX_le hE s Y

end Fourier

end DGS
