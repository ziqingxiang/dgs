module

public import DGS.S05_Local.Hensel

@[expose] public section

open Matrix Polynomial Real

namespace DGS

section Robust

variable {R : Type*} [Zero R] [DecidableEq R] {N : ℕ}

def wt (v : Fin N → R) : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card

variable {m : ℕ}

def IsRobust {F : Type*} [Field F] [DecidableEq F] (s : ℕ) (Y : Matrix (Fin N) (Fin m) F) : Prop :=
  ∀ c : Fin m → F, c ≠ 0 → s ≤ wt (Y *ᵥ c)

def IsRobustE (p E : ℕ) [Fact p.Prime] (s : ℕ) (Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))) : Prop :=
  IsRobust s (Y.map (ZMod.cast : ZMod (p ^ E) → ZMod p))

end Robust

section ZModPow

variable {p : ℕ} [hp : Fact p.Prime] {E : ℕ}

noncomputable def redHom (p E : ℕ) (hE : 1 ≤ E) : ZMod (p ^ E) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)

theorem redHom_apply (hE : 1 ≤ E) (x : ZMod (p ^ E)) : redHom p E hE x = (x.cast : ZMod p) :=
  ZMod.castHom_apply _

theorem exists_eq_p_mul_of_cast_eq_zero (_hE : 1 ≤ E) {x : ZMod (p ^ E)}
    (hx : (x.cast : ZMod p) = 0) : ∃ y : ZMod (p ^ E), x = (p : ZMod (p ^ E)) * y := by
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  have h1 : (x.cast : ZMod p) = ((x.val : ℕ) : ZMod p) := (ZMod.natCast_val x).symm
  rw [h1, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨k, hk⟩ := hx
  refine ⟨(k : ZMod (p ^ E)), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hk]
  push_cast; ring

theorem pow_mul_ne_zero_of_cast_ne_zero {x : ZMod (p ^ E)} (hx : (x.cast : ZMod p) ≠ 0) {r : ℕ}
    (hr : r < E) : (p : ZMod (p ^ E)) ^ r * x ≠ 0 := by
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  intro h0
  apply hx
  have h1 : (x.cast : ZMod p) = ((x.val : ℕ) : ZMod p) := (ZMod.natCast_val x).symm
  rw [h1, ZMod.natCast_eq_zero_iff]
  have h2 : ((p ^ r * x.val : ℕ) : ZMod (p ^ E)) = 0 := by
    push_cast; rw [ZMod.natCast_zmod_val]; exact h0
  rw [ZMod.natCast_eq_zero_iff] at h2
  have h3 : p ^ r * p ^ (E - r) ∣ p ^ r * x.val := by
    rw [← pow_add, Nat.add_sub_cancel' hr.le]; exact h2
  have h4 := (Nat.mul_dvd_mul_iff_left (pow_pos hp.out.pos r)).1 h3
  exact (dvd_pow_self p (by omega)).trans h4

theorem exists_pow_mul_of_ne_zero (hE : 1 ≤ E) {m : ℕ} {x : Fin m → ZMod (p ^ E)} (hx : x ≠ 0) :
    ∃ r < E, ∃ x'' : Fin m → ZMod (p ^ E), x = (p : ZMod (p ^ E)) ^ r • x'' ∧
      (fun k => ((x'' k).cast : ZMod p)) ≠ 0 := by
  classical
  have hpE : (p : ZMod (p ^ E)) ^ E = 0 := by exact_mod_cast ZMod.natCast_self (p ^ E)
  have hQ : ∃ r, ¬ ∃ x'' : Fin m → ZMod (p ^ E), x = (p : ZMod (p ^ E)) ^ (r + 1) • x'' := by
    refine ⟨E - 1, fun ⟨x'', hx''⟩ => hx ?_⟩
    rw [hx'', Nat.sub_add_cancel hE, hpE, zero_smul]
  obtain ⟨r, hrdef⟩ : ∃ r, r = Nat.find hQ := ⟨_, rfl⟩
  have hrQ : ¬ ∃ x'' : Fin m → ZMod (p ^ E), x = (p : ZMod (p ^ E)) ^ (r + 1) • x'' := by
    rw [hrdef]; exact Nat.find_spec hQ
  have hrE : r < E := by
    have h1 : Nat.find hQ ≤ E - 1 := Nat.find_min' hQ (fun ⟨x'', hx''⟩ => hx (by
      rw [hx'', Nat.sub_add_cancel hE, hpE, zero_smul]))
    omega
  have hdiv : ∃ x'' : Fin m → ZMod (p ^ E), x = (p : ZMod (p ^ E)) ^ r • x'' := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · exact ⟨x, by simp only [h0, pow_zero, one_smul]⟩
    · have h1 := Nat.find_min hQ (show r - 1 < Nat.find hQ by omega)
      push Not at h1
      rw [Nat.sub_add_cancel hpos] at h1
      exact h1
  obtain ⟨x'', hx''⟩ := hdiv
  refine ⟨r, hrE, x'', hx'', fun h0 => hrQ ?_⟩
  have hk : ∀ k, ∃ y, x'' k = (p : ZMod (p ^ E)) * y := fun k =>
    exists_eq_p_mul_of_cast_eq_zero hE (congrFun h0 k)
  choose y hy using hk
  refine ⟨y, ?_⟩
  rw [hx'']
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, hy k, pow_succ]
  try ring

theorem robust_lift (hE : 1 ≤ E) {N m s : ℕ} {Y : Matrix (Fin N) (Fin m) (ZMod (p ^ E))}
    (hY : IsRobustE p E s Y) {x : Fin m → ZMod (p ^ E)} (hx : x ≠ 0) : s ≤ wt (Y *ᵥ x) := by
  obtain ⟨r, hr, x'', rfl, hx''⟩ := exists_pow_mul_of_ne_zero hE hx
  have hY' : IsRobust s (Y.map (ZMod.cast : ZMod (p ^ E) → ZMod p)) := hY
  refine (hY' _ hx'').trans (Finset.card_le_card fun j hj => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  have h1 : (Y.map (ZMod.cast : ZMod (p ^ E) → ZMod p) *ᵥ fun k => ((x'' k).cast : ZMod p)) j =
      (((Y *ᵥ x'') j).cast : ZMod p) := by
    rw [← redHom_apply hE]
    simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, redHom_apply]
  rw [h1] at hj
  rw [mulVec_smul, Pi.smul_apply, smul_eq_mul]
  exact pow_mul_ne_zero_of_cast_ne_zero hj hr

end ZModPow

section Antisymm

variable (m : ℕ) (q : ℕ) [NeZero q]

def antisymm : Finset (Matrix (Fin m) (Fin m) (ZMod q)) :=
  Finset.univ.filter fun K => Kᵀ = -K

theorem mem_antisymm {K : Matrix (Fin m) (Fin m) (ZMod q)} : K ∈ antisymm m q ↔ Kᵀ = -K := by
  simp [antisymm]

def antisymmEquiv :
    {K : Matrix (Fin m) (Fin m) (ZMod q) // Kᵀ = -K} ≃
      (Pairs m → ZMod q) × (Fin m → {x : ZMod q // x + x = 0}) where
  toFun K := (fun pr => K.1 pr.1.1 pr.1.2, fun i => ⟨K.1 i i, by
    have := congrFun (congrFun K.2 i) i
    simp only [transpose_apply, Matrix.neg_apply] at this
    rw [eq_neg_iff_add_eq_zero] at this
    exact this⟩)
  invFun x := ⟨Matrix.of fun i j =>
      if h : i < j then x.1 ⟨(i, j), h⟩ else if h' : j < i then -x.1 ⟨(j, i), h'⟩ else (x.2 i).1, by
    ext i j
    simp only [transpose_apply, Matrix.neg_apply, Matrix.of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.2 h.le]
    · simp only [lt_irrefl, dite_false]
      have := (x.2 i).2
      rw [eq_neg_iff_add_eq_zero]; exact this
    · simp [h, not_lt.2 h.le]⟩
  left_inv K := by
    ext i j
    simp only [Matrix.of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h]
    · simp
    · simp only [not_lt.2 h.le, h, dite_false, dite_true]
      have := congrFun (congrFun K.2 i) j
      simp only [transpose_apply, Matrix.neg_apply] at this
      rw [this, neg_neg]
  right_inv x := by
    ext pr
    · simp [pr.2]
    · simp

theorem card_antisymm :
    (antisymm m q).card = q ^ (m * (m - 1) / 2) * (Fintype.card {x : ZMod q // x + x = 0}) ^ m := by
  classical
  have h1 : (antisymm m q).card = Fintype.card {K : Matrix (Fin m) (Fin m) (ZMod q) // Kᵀ = -K} := by
    rw [antisymm, Fintype.card_subtype]
  rw [h1, Fintype.card_congr (antisymmEquiv m q), Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]
  congr 2
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun pr : Fin m × Fin m => pr.1 < pr.2).card = m.choose 2 := by
    have := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin m)))
    rwa [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] at this
  rw [this, Nat.choose_two_right]

end Antisymm

end DGS
