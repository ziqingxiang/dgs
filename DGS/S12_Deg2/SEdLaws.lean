module

public import DGS.S11_Deg1.PtPsi

@[expose] public section

open Finset Matrix Module
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

theorem sum_fst_eq (F : ZMod p → ℝ) :
    ∑ g : Fin (n + 1) → ZMod p, F (g 0) = (p : ℝ) ^ n * ∑ a, F a := by
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ZMod p).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, sum_const, card_univ]
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [Fintype.card_pi, prod_const, card_univ, Fintype.card_fin, ZMod.card, nsmul_eq_mul]
  push_cast
  ring

theorem pow_sub_one_pos (hn : 1 ≤ n) : (0 : ℝ) < (p : ℝ) ^ n - 1 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have h1 : (p : ℝ) ^ 1 ≤ (p : ℝ) ^ n := pow_le_pow_right₀ (by linarith) hn
  rw [pow_one] at h1
  linarith

theorem sum_fst_ne_zero (σ : ℝ) :
    ∑ g : Fin (n + 1) → ZMod p, (if g 0 ≠ 0 then gaussW σ (g 0).valMinAbs else 0) =
      (p : ℝ) ^ n * muP p σ := by
  rw [sum_fst_eq (fun a => if a ≠ 0 then gaussW σ a.valMinAbs else 0)]
  rfl

theorem sum_fst_eq_zero_ne :
    ∑ g : Fin (n + 1) → ZMod p, (if g 0 = 0 ∧ g ≠ 0 then (1 : ℝ) else 0) = (p : ℝ) ^ n - 1 := by
  have e : ∀ g : Fin (n + 1) → ZMod p, (if g 0 = 0 ∧ g ≠ 0 then (1 : ℝ) else 0) =
      (if g 0 = 0 then (1 : ℝ) else 0) - (if g = 0 then 1 else 0) := by
    intro g
    by_cases hg : g = 0
    · simp [hg]
    · simp [hg]
  simp_rw [e]
  rw [sum_sub_distrib, sum_fst_eq (fun a => if a = 0 then (1 : ℝ) else 0)]
  simp

def clsSd (g : Fin (n + 1) → ZMod p) : Fin 3 := if g 0 ≠ 0 then 1 else if g = 0 then 0 else 2

noncomputable def wtSd (σ : ℝ) (g : Fin (n + 1) → ZMod p) : ℝ := gaussW σ (g 0).valMinAbs

variable (p n) in
noncomputable def massSd (σ : ℝ) (c : Fin 3) : ℝ :=
  if c = 1 then (p : ℝ) ^ n * muP p σ else if c = 2 then (p : ℝ) ^ n - 1 else 1

noncomputable def lawSd (σ : ℝ) (c : Fin 3) (g : Fin (n + 1) → ZMod p) : ℝ :=
  if c = 1 then (if g 0 ≠ 0 then gaussW σ (g 0).valMinAbs / ((p : ℝ) ^ n * muP p σ) else 0)
  else if c = 2 then (if g 0 = 0 ∧ g ≠ 0 then 1 / ((p : ℝ) ^ n - 1) else 0)
  else (if g = 0 then 1 else 0)

theorem massSd_pos (hn : 1 ≤ n) (σ : ℝ) (c : Fin 3) : 0 < massSd p n σ c := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 := pow_sub_one_pos (p := p) hn
  have h2 := muP_pos (p := p) σ
  unfold massSd
  split_ifs <;> positivity

omit [Fact (Nat.Prime p)] in
theorem wtSd_nonneg (σ : ℝ) (g : Fin (n + 1) → ZMod p) : 0 ≤ wtSd σ g := gaussW_nonneg _ _

theorem lawSd_nonneg (hn : 1 ≤ n) (σ : ℝ) (c : Fin 3) (g : Fin (n + 1) → ZMod p) : 0 ≤ lawSd σ c g := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 := pow_sub_one_pos (p := p) hn
  have h2 := muP_pos (p := p) σ
  unfold lawSd
  split_ifs <;> first | positivity | exact div_nonneg (gaussW_nonneg _ _) (by positivity)

theorem clsSd_of_lawSd_ne_zero {σ : ℝ} {c : Fin 3} {g : Fin (n + 1) → ZMod p} (h : lawSd σ c g ≠ 0) :
    clsSd g = c := by
  unfold lawSd at h
  unfold clsSd
  obtain rfl | rfl | rfl := fin3_cases c
  · rw [ite_eq_right (by decide), ite_eq_right (by decide)] at h
    by_cases hg : g = 0
    · subst hg
      simp
    · rw [ite_eq_right hg] at h
      exact absurd rfl h
  · rw [ite_eq_left rfl] at h
    by_cases hg : g 0 ≠ 0
    · rw [ite_eq_left hg]
    · rw [ite_eq_right hg] at h
      exact absurd rfl h
  · rw [ite_eq_right (by decide), ite_eq_left rfl] at h
    by_cases hg : g 0 = 0 ∧ g ≠ 0
    · rw [ite_eq_right (not_not.2 hg.1), ite_eq_right hg.2]
    · rw [ite_eq_right hg] at h
      exact absurd rfl h

theorem wtSd_cls_eq (hn : 1 ≤ n) (σ : ℝ) (c : Fin 3) (g : Fin (n + 1) → ZMod p) :
    (if clsSd g = c then wtSd σ g else 0) = massSd p n σ c * lawSd σ c g := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 := (pow_sub_one_pos (p := p) hn).ne'
  have hμ := (muP_pos (p := p) σ).ne'
  have hpn : (p : ℝ) ^ n ≠ 0 := by positivity
  obtain rfl | rfl | rfl := fin3_cases c
  ·
    have hl : lawSd σ 0 g = if g = 0 then 1 else 0 := by
      rw [lawSd, ite_eq_right (by decide), ite_eq_right (by decide)]
    have hm : massSd p n σ 0 = 1 := by rw [massSd, ite_eq_right (by decide), ite_eq_right (by decide)]
    rw [hl, hm, one_mul]
    by_cases hg0 : g = 0
    · subst hg0
      have hcls : clsSd (0 : Fin (n + 1) → ZMod p) = 0 := by
        unfold clsSd
        simp
      rw [ite_eq_left hcls, ite_eq_left rfl, wtSd, Pi.zero_apply, ZMod.valMinAbs_zero, gaussW_zero]
    · have hcls : clsSd g ≠ 0 := by
        unfold clsSd
        split_ifs <;> decide
      rw [ite_eq_right hcls, ite_eq_right hg0]
  ·
    by_cases hg : g 0 ≠ 0
    · have hcls : clsSd g = 1 := by unfold clsSd; rw [ite_eq_left hg]
      rw [ite_eq_left hcls, lawSd, ite_eq_left rfl, ite_eq_left hg, massSd, ite_eq_left rfl, wtSd]
      field_simp
    · have hcls : clsSd g ≠ 1 := by
        unfold clsSd
        rw [ite_eq_right hg]
        split_ifs <;> decide
      rw [ite_eq_right hcls, lawSd, ite_eq_left rfl, ite_eq_right hg, mul_zero]
  ·
    have hm : massSd p n σ 2 = (p : ℝ) ^ n - 1 := by rw [massSd, ite_eq_right (by decide), ite_eq_left rfl]
    by_cases hg : g 0 = 0 ∧ g ≠ 0
    · have hcls : clsSd g = 2 := by
        unfold clsSd
        rw [ite_eq_right (not_not.2 hg.1), ite_eq_right hg.2]
      rw [ite_eq_left hcls, lawSd, ite_eq_right (by decide), ite_eq_left rfl, ite_eq_left hg, hm, wtSd, hg.1,
        ZMod.valMinAbs_zero, gaussW_zero]
      field_simp
    · have hcls : clsSd g ≠ 2 := by
        unfold clsSd
        split_ifs with h3 h4
        · decide
        · decide
        · exact absurd ⟨not_not.1 h3, h4⟩ hg
      rw [ite_eq_right hcls, lawSd, ite_eq_right (by decide), ite_eq_left rfl, ite_eq_right hg, mul_zero]

theorem wtSd_eq_sum (hn : 1 ≤ n) (σ : ℝ) (g : Fin (n + 1) → ZMod p) :
    wtSd σ g = ∑ c : Fin 3, massSd p n σ c * lawSd σ c g := by
  rw [← Finset.sum_congr rfl fun c _ => wtSd_cls_eq hn σ c g, sum_ite_eq]
  simp

theorem sum_lawSd (hn : 1 ≤ n) (σ : ℝ) (c : Fin 3) : ∑ g : Fin (n + 1) → ZMod p, lawSd σ c g = 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 := (pow_sub_one_pos (p := p) hn).ne'
  have hμ := (muP_pos (p := p) σ).ne'
  have hpn : (p : ℝ) ^ n ≠ 0 := by positivity
  obtain rfl | rfl | rfl := fin3_cases c
  · simp [lawSd]
  · have e : ∀ g : Fin (n + 1) → ZMod p, lawSd σ 1 g =
        (if g 0 ≠ 0 then gaussW σ (g 0).valMinAbs else 0) / ((p : ℝ) ^ n * muP p σ) := by
      intro g
      rw [lawSd, ite_eq_left rfl]
      split_ifs <;> simp
    simp_rw [e]
    rw [← sum_div, sum_fst_ne_zero, div_self (mul_ne_zero hpn hμ)]
  · have e : ∀ g : Fin (n + 1) → ZMod p, lawSd σ 2 g =
        (if g 0 = 0 ∧ g ≠ 0 then (1 : ℝ) else 0) / ((p : ℝ) ^ n - 1) := by
      intro g
      rw [lawSd, ite_eq_right (by decide), ite_eq_left rfl]
      split_ifs <;> simp
    simp_rw [e]
    rw [← sum_div, sum_fst_eq_zero_ne, div_self h1]

theorem sum_massSd (σ : ℝ) : ∑ c : Fin 3, massSd p n σ c = (p : ℝ) ^ n * (1 + muP p σ) := by
  rw [Fin.sum_univ_three]
  simp only [massSd]
  norm_num
  ring

section Patterns

variable {m : ℕ}

theorem sum_wtSd_le (hn : 1 ≤ n) (σ : ℝ) (F : (Fin m → Fin (n + 1) → ZMod p) → ℝ) (_hF : ∀ w, 0 ≤ F w)
    (H : (Fin m → Fin 3) → (Fin m → Fin (n + 1) → ZMod p) → ℝ)
    (hH : ∀ cls w, (∀ j, clsSd (w j) = cls j) → F w ≤ H cls w) :
    ∑ w : Fin m → Fin (n + 1) → ZMod p, (∏ j, wtSd σ (w j)) * F w ≤
      ∑ cls : Fin m → Fin 3, (∏ j, massSd p n σ (cls j)) * pexp (fun j => lawSd σ (cls j)) (H cls) := by
  classical
  have e1 : ∀ w : Fin m → Fin (n + 1) → ZMod p, ∏ j, wtSd σ (w j) =
      ∑ cls : Fin m → Fin 3, (∏ j, massSd p n σ (cls j)) * ∏ j, lawSd σ (cls j) (w j) := by
    intro w
    simp_rw [wtSd_eq_sum hn σ, Fintype.prod_sum]
    exact sum_congr rfl fun cls _ => prod_mul_distrib
  calc ∑ w : Fin m → Fin (n + 1) → ZMod p, (∏ j, wtSd σ (w j)) * F w
      = ∑ cls : Fin m → Fin 3, (∏ j, massSd p n σ (cls j)) *
          ∑ w : Fin m → Fin (n + 1) → ZMod p, (∏ j, lawSd σ (cls j) (w j)) * F w := by
        simp_rw [e1, sum_mul, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun cls _ => sum_congr rfl fun w _ => by ring
    _ ≤ ∑ cls : Fin m → Fin 3, (∏ j, massSd p n σ (cls j)) * pexp (fun j => lawSd σ (cls j)) (H cls) := by
        refine sum_le_sum fun cls _ => mul_le_mul_of_nonneg_left ?_
          (prod_nonneg fun j _ => (massSd_pos hn σ _).le)
        unfold pexp
        refine sum_le_sum fun w _ => ?_
        by_cases hw : ∀ j, clsSd (w j) = cls j
        · exact mul_le_mul_of_nonneg_left (hH cls w hw)
            (prod_nonneg fun j _ => lawSd_nonneg hn σ _ _)
        · push Not at hw
          obtain ⟨j, hj⟩ := hw
          have h0 : lawSd σ (cls j) (w j) = 0 := by
            by_contra h
            exact hj (clsSd_of_lawSd_ne_zero h)
          rw [prod_eq_zero (mem_univ j) h0, zero_mul, zero_mul]

theorem sum_prod_massSd (σ : ℝ) :
    ∑ cls : Fin m → Fin 3, ∏ j, massSd p n σ (cls j) = ((p : ℝ) ^ n * (1 + muP p σ)) ^ m := by
  classical
  rw [← Fintype.prod_sum (fun (_ : Fin m) (c : Fin 3) => massSd p n σ c), prod_const, card_univ,
    Fintype.card_fin, sum_massSd]

end Patterns

def bcSd : Fin 2 → Fin 3 := ![1, 2]

noncomputable def lawB (σ : ℝ) (X : Fin 2) : (Fin (n + 1) → ZMod p) → ℝ := lawSd σ (bcSd X)

variable (p n) in
noncomputable def massB (σ : ℝ) (X : Fin 2) : ℝ := massSd p n σ (bcSd X)

theorem fin2_cases (X : Fin 2) : X = 0 ∨ X = 1 := by fin_cases X <;> simp

theorem massB_zero_eq (σ : ℝ) : massB p n σ 0 = (p : ℝ) ^ n * muP p σ := by
  simp [massB, bcSd, massSd]

theorem massB_one_eq (σ : ℝ) : massB p n σ 1 = (p : ℝ) ^ n - 1 := by
  simp [massB, bcSd, massSd]

theorem lawB_zero_eq (σ : ℝ) :
    lawB σ 0 = fun g : Fin (n + 1) → ZMod p =>
      if g 0 ≠ 0 then gaussW σ (g 0).valMinAbs / ((p : ℝ) ^ n * muP p σ) else 0 := by
  funext g
  simp [lawB, bcSd, lawSd]

theorem lawB_one_eq (σ : ℝ) :
    lawB σ 1 = fun g : Fin (n + 1) → ZMod p => if g 0 = 0 ∧ g ≠ 0 then 1 / ((p : ℝ) ^ n - 1) else 0 := by
  funext g
  simp [lawB, bcSd, lawSd]

theorem massB_pos (hn : 1 ≤ n) (σ : ℝ) (X : Fin 2) : 0 < massB p n σ X := massSd_pos hn _ _

theorem lawB_nonneg (hn : 1 ≤ n) (σ : ℝ) (X : Fin 2) (g : Fin (n + 1) → ZMod p) : 0 ≤ lawB σ X g :=
  lawSd_nonneg hn _ _ _

theorem sum_lawB (hn : 1 ≤ n) (σ : ℝ) (X : Fin 2) : ∑ g : Fin (n + 1) → ZMod p, lawB σ X g = 1 :=
  sum_lawSd hn _ _

theorem lawB_zero (σ : ℝ) (X : Fin 2) : lawB σ X (0 : Fin (n + 1) → ZMod p) = 0 := by
  obtain rfl | rfl := fin2_cases X <;> simp [lawB, bcSd, lawSd]

theorem lawB_le (hn : 1 ≤ n) {σ : ℝ} (hσ : 0 ≤ σ) (X : Fin 2) (g : Fin (n + 1) → ZMod p) :
    lawB σ X g ≤ 1 / massB p n σ X := by
  have hm := massB_pos (p := p) hn σ X
  obtain rfl | rfl := fin2_cases X
  · rw [lawB_zero_eq, ← massB_zero_eq σ]
    dsimp only
    split_ifs
    · exact div_le_div_of_nonneg_right (gaussW_le_one hσ _) hm.le
    · positivity
  · rw [lawB_one_eq, ← massB_one_eq σ]
    dsimp only
    split_ifs <;> first | exact le_rfl | positivity

theorem massB_le {σ : ℝ} (hσ : 0 ≤ σ) (X : Fin 2) : massB p n σ X ≤ (p : ℝ) ^ (n + 1) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hμ := muP_le (p := p) hσ
  have hμ0 := muP_pos (p := p) σ
  have hpn : (0 : ℝ) < (p : ℝ) ^ n := by positivity
  rw [pow_succ]
  obtain rfl | rfl := fin2_cases X
  · rw [massB_zero_eq]
    exact mul_le_mul_of_nonneg_left (hμ.trans (by linarith)) hpn.le
  · rw [massB_one_eq]
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    nlinarith

theorem card_fiber_le {F V : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup V] [Module F V]
    [Fintype V] [DecidableEq V] (L : Submodule F V) [DecidablePred (· ∈ L)] (φ : V →ₗ[F] F) {α : F}
    (hα : α ≠ 0) :
    (univ.filter fun a : V => a ∈ L ∧ φ a = α).card ≤ Fintype.card F ^ (finrank F L - 1) := by
  classical
  by_cases hne : (univ.filter fun a : V => a ∈ L ∧ φ a = α).Nonempty
  · obtain ⟨a0, ha0⟩ := hne
    obtain ⟨ha0L, ha0φ⟩ := (mem_filter.1 ha0).2
    set K : Submodule F V := L ⊓ LinearMap.ker φ with hK
    have hKL : K < L := by
      refine lt_of_le_of_ne inf_le_left fun h => ?_
      have : a0 ∈ K := h ▸ ha0L
      have h0 : φ a0 = 0 := (Submodule.mem_inf.1 this).2
      exact hα (ha0φ ▸ h0)
    have hfin : finrank F K < finrank F L := Submodule.finrank_lt_finrank_of_lt hKL
    have hcardK : Fintype.card K = Fintype.card F ^ finrank F K := Module.card_eq_pow_finrank
    have h1 : (univ.filter fun a : V => a ∈ L ∧ φ a = α).card ≤ (univ.filter fun a : V => a ∈ K).card := by
      refine card_le_card_of_injOn (fun a => a - a0) (fun a ha => ?_) (fun a _ b _ h => sub_left_inj.1 h)
      obtain ⟨haL, haφ⟩ := (mem_filter.1 ha).2
      refine mem_filter.2 ⟨mem_univ _, Submodule.mem_inf.2 ⟨L.sub_mem haL ha0L, ?_⟩⟩
      rw [LinearMap.mem_ker, map_sub, haφ, ha0φ, sub_self]
    have h2 : (univ.filter fun a : V => a ∈ K).card = Fintype.card K := by
      rw [Fintype.card_subtype]
    rw [h2, hcardK] at h1
    refine h1.trans (Nat.pow_le_pow_right Fintype.card_pos (by omega))
  · rw [not_nonempty_iff_eq_empty.1 hne, card_empty]
    exact Nat.zero_le _

theorem sum_mem_fiber_le {F V : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup V] [Module F V]
    [Fintype V] [DecidableEq V] (L : Submodule F V) [DecidablePred (· ∈ L)] (φ : V →ₗ[F] F) (f : F → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hf0 : f 0 = 0) :
    ∑ a ∈ univ.filter (· ∈ L), f (φ a) ≤ (Fintype.card F : ℝ) ^ (finrank F L - 1) * ∑ α, f α := by
  classical
  rw [← sum_fiberwise (univ.filter (· ∈ L)) φ (fun a => f (φ a)), mul_sum]
  refine sum_le_sum fun α _ => ?_
  have e : ∑ a ∈ (univ.filter (· ∈ L)).filter (fun a => φ a = α), f (φ a) =
      ((univ.filter fun a : V => a ∈ L ∧ φ a = α).card : ℝ) * f α := by
    rw [filter_filter, ← nsmul_eq_mul, ← sum_const]
    exact sum_congr rfl fun a ha => by rw [(mem_filter.1 ha).2.2]
  rw [e]
  by_cases hα : α = 0
  · rw [hα, hf0, mul_zero, mul_zero]
  · refine mul_le_mul_of_nonneg_right ?_ (hf α)
    exact_mod_cast card_fiber_le L φ hα

def fstLin : (Fin (n + 1) → ZMod p) →ₗ[ZMod p] ZMod p := LinearMap.proj 0

@[simp] theorem fstLin_apply (g : Fin (n + 1) → ZMod p) : fstLin g = g 0 := rfl

theorem subMeas_lawB_le (hn : 1 ≤ n) (σ : ℝ) (X : Fin 2) (L : Submodule (ZMod p) (Fin (n + 1) → ZMod p)) :
    massB p n σ X * subMeas (lawB σ X) L ≤
      if X = 0 then muP p σ * (p : ℝ) ^ (finrank (ZMod p) L - 1) else (p : ℝ) ^ finrank (ZMod p) L := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 := pow_sub_one_pos (p := p) hn
  have hμ := muP_pos (p := p) σ
  have hpn : (0 : ℝ) < (p : ℝ) ^ n := by positivity
  unfold subMeas
  obtain rfl | rfl := fin2_cases X
  · rw [ite_eq_left rfl, massB_zero_eq, lawB_zero_eq]
    dsimp only
    have e : ∀ a : Fin (n + 1) → ZMod p,
        (if a 0 ≠ 0 then gaussW σ (a 0).valMinAbs / ((p : ℝ) ^ n * muP p σ) else 0) =
          (fun x : ZMod p => if x ≠ 0 then gaussW σ x.valMinAbs else 0) (fstLin a) /
            ((p : ℝ) ^ n * muP p σ) := by
      intro a
      simp only [fstLin_apply]
      by_cases ha : a 0 = 0 <;> simp [ha]
    simp_rw [e]
    rw [← sum_div, mul_div_assoc', mul_comm, mul_div_assoc, div_self (by positivity), mul_one]
    have h := sum_mem_fiber_le L fstLin (fun x : ZMod p => if x ≠ 0 then gaussW σ x.valMinAbs else 0)
      (fun x => by split_ifs <;> simp [gaussW_nonneg]) (by simp)
    rw [ZMod.card] at h
    calc ∑ a ∈ univ.filter (· ∈ L), (fun x : ZMod p => if x ≠ 0 then gaussW σ x.valMinAbs else 0) (fstLin a)
        ≤ (p : ℝ) ^ (finrank (ZMod p) L - 1) *
            ∑ α : ZMod p, (if α ≠ 0 then gaussW σ α.valMinAbs else 0) := h
      _ = muP p σ * (p : ℝ) ^ (finrank (ZMod p) L - 1) := by rw [muP, mul_comm]
  · rw [ite_eq_right (by decide), massB_one_eq, lawB_one_eq]
    dsimp only
    have hle : ∑ a ∈ univ.filter (· ∈ L), (if a 0 = 0 ∧ a ≠ 0 then 1 / ((p : ℝ) ^ n - 1) else 0) ≤
        ∑ _a ∈ univ.filter (· ∈ L), 1 / ((p : ℝ) ^ n - 1) :=
      sum_le_sum fun a _ => by split_ifs <;> first | exact le_rfl | positivity
    have hcard : ((univ.filter (· ∈ L)).card : ℝ) = (p : ℝ) ^ finrank (ZMod p) L := by
      have h2 : (univ.filter (· ∈ L)).card = Fintype.card L := by rw [Fintype.card_subtype]
      rw [h2, Module.card_eq_pow_finrank (K := ZMod p) (V := L), ZMod.card]
      push_cast
      ring
    rw [sum_const, nsmul_eq_mul, hcard] at hle
    calc ((p : ℝ) ^ n - 1) * ∑ a ∈ univ.filter (· ∈ L),
          (if a 0 = 0 ∧ a ≠ 0 then 1 / ((p : ℝ) ^ n - 1) else 0)
        ≤ ((p : ℝ) ^ n - 1) * ((p : ℝ) ^ finrank (ZMod p) L * (1 / ((p : ℝ) ^ n - 1))) :=
          mul_le_mul_of_nonneg_left hle h1.le
      _ = (p : ℝ) ^ finrank (ZMod p) L := by field_simp

section Classes

variable {m : ℕ}

def DSd (cls : Fin m → Fin 3) (X : Fin 2) : Finset (Fin m) := univ.filter fun j => cls j = bcSd X

theorem mem_DSd {cls : Fin m → Fin 3} {X : Fin 2} {j : Fin m} : j ∈ DSd cls X ↔ cls j = bcSd X := by
  simp [DSd]

theorem DSd_disjoint (cls : Fin m → Fin 3) {X Y : Fin 2} (hXY : X ≠ Y) : Disjoint (DSd cls X) (DSd cls Y) := by
  rw [Finset.disjoint_left]
  intro j hX hY
  rw [mem_DSd] at hX hY
  apply hXY
  obtain rfl | rfl := fin2_cases X <;> obtain rfl | rfl := fin2_cases Y <;>
    simp_all [bcSd]

theorem sum_card_DSd_le (cls : Fin m → Fin 3) : ∑ X : Fin 2, (DSd cls X).card ≤ m := by
  rw [← card_biUnion fun X _ Y _ hXY => DSd_disjoint cls hXY]
  calc (univ.biUnion (DSd cls)).card ≤ (univ : Finset (Fin m)).card := card_le_univ _
    _ = m := by rw [card_univ, Fintype.card_fin]

theorem lawSd_of_mem_DSd (σ : ℝ) {cls : Fin m → Fin 3} {X : Fin 2} {j : Fin m} (hj : j ∈ DSd cls X) :
    lawSd (p := p) (n := n) σ (cls j) = lawB σ X := by
  rw [mem_DSd] at hj
  rw [hj]
  rfl

theorem prod_massSd_eq (σ : ℝ) (cls : Fin m → Fin 3) :
    ∏ j, massSd p n σ (cls j) = ∏ X : Fin 2, massB p n σ X ^ (DSd cls X).card := by
  classical
  have e : ∀ j, massSd p n σ (cls j) = ∏ X : Fin 2, (if j ∈ DSd cls X then massB p n σ X else 1) := by
    intro j
    rw [Fin.prod_univ_two]
    simp only [mem_DSd]
    obtain h | h | h := fin3_cases (cls j)
    · rw [h]
      simp [bcSd, massSd]
    · rw [h]
      simp [bcSd, massB]
    · rw [h]
      simp [bcSd, massB]
  simp_rw [e]
  rw [prod_comm]
  refine prod_congr rfl fun X _ => ?_
  rw [prod_ite_mem, univ_inter, prod_const]

end Classes

end DGS
