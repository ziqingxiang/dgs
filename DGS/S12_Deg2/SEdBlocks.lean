module

public import DGS.S12_Deg2.SEdLaws

@[expose] public section

open Finset Matrix Module
open scoped Real

namespace DGS

theorem level_pair_bound' {κ : Type*} [Fintype κ] {N m k s : ℕ} {t P2 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (htP : 1 ≤ P2 * t) (mass ζ cf : κ → ℝ) (hmass0 : ∀ X, 0 ≤ mass X) (hmassP : ∀ X, mass X ≤ P2)
    (hζ0 : ∀ X, 0 ≤ ζ X) (hcf : ∀ X, mass X * ζ X * t ≤ cf X)
    (D : κ → ℕ) (hsum : ∑ X, D X ≤ m) (hNm : N + k = m) (hsk : s ≤ k) (hk : 0 < k) :
    (∏ X, mass X ^ D X) * (2 * t) ^ N * ∏ X, ζ X ^ ((k - s) * (D X / k)) ≤
      2 ^ N * P2 ^ ((Fintype.card κ + 1) * k + s * (m / k)) * ∏ X, cf X ^ ((k - s) * (D X / k)) := by
  have hP1 : 1 ≤ P2 := by nlinarith
  set M : κ → ℕ := fun X => (k - s) * (D X / k) with hM
  set r : κ → ℕ := fun X => D X - M X with hr
  have hMD : ∀ X, M X ≤ D X := fun X => chain_le
  have hDMr : ∀ X, D X = M X + r X := fun X => by
    have := hMD X
    simp only [hr]
    omega
  have hrsum : ∑ X, r X ≤ Fintype.card κ * k + s * (m / k) := by
    have h1 : ∀ X, r X ≤ k + s * (D X / k) := fun X => sub_chain_le hk hsk
    have h2 : ∑ X, D X / k ≤ m / k := by
      rw [Nat.le_div_iff_mul_le hk, sum_mul]
      exact (sum_le_sum fun X _ => Nat.div_mul_le_self (D X) k).trans hsum
    calc ∑ X, r X ≤ ∑ X : κ, (k + s * (D X / k)) := sum_le_sum fun X _ => h1 X
      _ = Fintype.card κ * k + s * ∑ X, D X / k := by
          rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, smul_eq_mul]
      _ ≤ Fintype.card κ * k + s * (m / k) := by gcongr
  have hMsum : ∑ X, M X ≤ N + k := by
    rw [hNm]
    exact (sum_le_sum fun X _ => hMD X).trans hsum
  have hmassD : ∏ X, mass X ^ D X ≤ (∏ X, mass X ^ M X) * P2 ^ (∑ X, r X) := by
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    refine prod_le_prod₀ (fun X _ => pow_nonneg (hmass0 X) _) fun X _ => ?_
    rw [hDMr X, pow_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hmass0 X) (hmassP X) _)
      (pow_nonneg (hmass0 X) _)
  have ht := pow_le_P2_pow ht0 ht1 htP hMsum
  have hchain : (∏ X, mass X ^ M X) * t ^ (∑ X, M X) * ∏ X, ζ X ^ M X ≤ ∏ X, cf X ^ M X := by
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_le_prod₀ (fun X _ => by have := hmass0 X; have := hζ0 X; positivity) fun X _ => ?_
    rw [← mul_pow, ← mul_pow]
    have h := hcf X
    have h0 : 0 ≤ mass X * t * ζ X := by have := hmass0 X; have := hζ0 X; positivity
    exact pow_le_pow_left₀ h0 (by linarith) _
  have hP : P2 ^ (k + ∑ X, r X) ≤ P2 ^ ((Fintype.card κ + 1) * k + s * (m / k)) :=
    pow_le_pow_right₀ hP1 (by rw [Nat.add_mul, one_mul]; omega)
  have hP0 : 0 ≤ P2 := by linarith
  have hζ : 0 ≤ ∏ X, ζ X ^ M X := prod_nonneg fun X _ => pow_nonneg (hζ0 X) _
  have hmD : 0 ≤ ∏ X, mass X ^ D X := prod_nonneg fun X _ => pow_nonneg (hmass0 X) _
  have hmM : 0 ≤ ∏ X, mass X ^ M X := prod_nonneg fun X _ => pow_nonneg (hmass0 X) _
  have hst : 0 ≤ (∏ X, mass X ^ M X) * t ^ (∑ X, M X) * ∏ X, ζ X ^ M X := by positivity
  calc (∏ X, mass X ^ D X) * (2 * t) ^ N * ∏ X, ζ X ^ M X
      ≤ ((∏ X, mass X ^ M X) * P2 ^ (∑ X, r X)) * (2 ^ N * (P2 ^ k * t ^ (∑ X, M X))) *
          ∏ X, ζ X ^ M X := by
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ hζ
        apply mul_le_mul hmassD _ (by positivity) (hmD.trans hmassD)
        exact mul_le_mul_of_nonneg_left ht (by positivity)
    _ = 2 ^ N * P2 ^ (k + ∑ X, r X) * ((∏ X, mass X ^ M X) * t ^ (∑ X, M X) * ∏ X, ζ X ^ M X) := by
        rw [pow_add]
        ring
    _ ≤ 2 ^ N * P2 ^ ((Fintype.card κ + 1) * k + s * (m / k)) * ∏ X, cf X ^ M X :=
        mul_le_mul (mul_le_mul_of_nonneg_left hP (by positivity)) hchain hst
          (mul_nonneg (by positivity) (pow_nonneg hP0 _))

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

def companion (b : Fin (n + 1) → ZMod p) (g : Fin (n + 1) → ZMod p) : Fin (n + 1) → ZMod p :=
  Fin.snoc (α := fun _ => ZMod p) (Fin.tail g) (-∑ l, b l * g l)

def krySys (ω : Pairs m → Bool) (b : Fin (n + 1) → ZMod p) (w : Fin m → Fin (n + 1) → ZMod p) : Prop :=
  ∀ i, ∑ j, seidelOf ω i j • w j = companion b (w i)

section Block

variable {l s : ℕ}

noncomputable def cfSd (p : ℕ) [Fact p.Prime] (l s : ℕ) (σ : ℝ) (X : Fin 2) : ℝ :=
  gam0 l s + (if X = 0 then 1.21 * muP p σ / p else 1.21)

theorem cfSd_nonneg (σ : ℝ) (X : Fin 2) : 0 ≤ cfSd p l s σ X := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have : 0 ≤ gam0 l s := by unfold gam0; positivity
  have := muP_pos (p := p) σ
  unfold cfSd
  split_ifs <;> positivity

noncomputable def gam1Sd (p n l s : ℕ) [Fact p.Prime] (σ : ℝ) (X : Fin 2) (t : ℝ) : ℝ :=
  64 * (1 + 1 / 100) * √(π * l) * (1 / massB p n σ X) / ((1 / 100) * t * √(s : ℝ))

noncomputable def kapSd (p n : ℕ) [Fact p.Prime] (σ : ℝ) (X : Fin 2) (g : ℕ) : ℝ :=
  (if X = 0 then muP p σ * (p : ℝ) ^ (g - 1) else (p : ℝ) ^ g) / massB p n σ X

open Classical in
noncomputable def zetaSd (p n l s : ℕ) [Fact p.Prime] (σ : ℝ) (X : Fin 2) (t : ℝ) : ℝ :=
  if h : ∃ g, 1 ≤ g ∧ g < n + 1 ∧ t ∈ window p l s g then
    gam1Sd p n l s σ X t + 1.1 * kapSd p n σ X (Classical.choose h)
  else gam1Sd p n l s σ X t

theorem massB_gam1Sd (hn : 1 ≤ n) (H : BDHyp p (n + 1) l s) (σ : ℝ) (X : Fin 2) {t : ℝ} (ht : 0 < t) :
    massB p n σ X * gam1Sd p n l s σ X t * t = gam0 l s := by
  have hm := (massB_pos (p := p) hn σ X).ne'
  have hs : (0 : ℝ) < √(s : ℝ) := by
    apply Real.sqrt_pos.2
    have := H.hs4
    have : 1 ≤ s := by have := H.hl; omega
    exact_mod_cast this
  unfold gam0 gam1Sd
  field_simp
  ring

theorem block_bound_d (hn : 1 ≤ n) (H : BDHyp p (n + 1) l s) {σ : ℝ} (hσ : 0 < σ) (X : Fin 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℝ} (ht : (1 + 1 / 100) / (p : ℝ) ^ (n + 1) ≤ t) :
    0 ≤ zetaSd p n l s σ X t ∧
      pexp (fun _ : ι => lawB (p := p) (n := n) σ X) (fun w => if t ≤ rhoG w then 1 else 0) ≤
        zetaSd p n l s σ X t ^ (Fintype.card ι - s) ∧
      massB p n σ X * zetaSd p n l s σ X t * t ≤ cfSd p l s σ X := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hm := massB_pos (p := p) hn σ X
  have hν0 := lawB_nonneg (p := p) hn σ X
  have hν1 := sum_lawB (p := p) hn σ X
  have hμ := muP_pos (p := p) σ
  have h1 : pexp (fun _ : ι => lawB (p := p) (n := n) σ X) (fun w => if t ≤ rhoG w then 1 else 0) ≤
      pmeas (fun _ : ι => lawB (p := p) (n := n) σ X) (fun w => t ≤ rhoHat w) := by
    rw [pmeas_eq_pexp]
    refine pexp_mono _ (fun _ a => hν0 a) fun w => ?_
    split_ifs with h2 h3
    · exact le_rfl
    · exact absurd (h2.trans (rhoG_le_rhoHat w)) h3
    · exact zero_le_one
    · exact le_rfl
  have hbd := prop_blockd (ι := ι) H (lawB σ X) hν0 hν1 (lawB_zero σ X) (lawB_le hn hσ.le X) ht
  have hγ0 : 0 ≤ gam1Sd p n l s σ X t := by unfold gam1Sd; positivity
  have hγt : massB p n σ X * gam1Sd p n l s σ X t * t = gam0 l s := massB_gam1Sd hn H σ X ht0
  have hgam0 : 0 ≤ gam0 l s := by unfold gam0; positivity
  unfold zetaSd
  split_ifs with hw
  · obtain ⟨hg1, hgd, hwin⟩ := Classical.choose_spec hw
    set g := Classical.choose hw with hgdef
    set cB : ℝ := if X = 0 then muP p σ * (p : ℝ) ^ (g - 1) else (p : ℝ) ^ g with hcB
    have hcB0 : 0 ≤ cB := by rw [hcB]; split_ifs <;> positivity
    have hκdef : kapSd p n σ X g = cB / massB p n σ X := rfl
    have hκ0 : 0 ≤ kapSd p n σ X g := by rw [hκdef]; positivity
    have hκ : ∀ L : Submodule (ZMod p) (Fin (n + 1) → ZMod p), finrank (ZMod p) L = g →
        subMeas (lawB σ X) L ≤ kapSd p n σ X g := by
      intro L hL
      have h2 := subMeas_lawB_le hn σ X L
      rw [hL] at h2
      rw [hκdef, le_div_iff₀ hm, mul_comm]
      exact h2
    have h2 := hbd.2.1 g hg1 hgd hwin (kapSd p n σ X g) hκ0 hκ
    refine ⟨by positivity, h1.trans ?_, ?_⟩
    · unfold gam1Sd at h2 ⊢
      exact h2
    have hlt : t < 1.1 / (p : ℝ) ^ g := hwin.2
    have hpg : (0 : ℝ) < (p : ℝ) ^ g := by positivity
    have hκt : massB p n σ X * (1.1 * kapSd p n σ X g) * t ≤ 1.21 * cB / (p : ℝ) ^ g := by
      have e : massB p n σ X * (1.1 * kapSd p n σ X g) * t = 1.1 * cB * t := by
        rw [hκdef]
        field_simp
      rw [e]
      calc 1.1 * cB * t ≤ 1.1 * cB * (1.1 / (p : ℝ) ^ g) :=
            mul_le_mul_of_nonneg_left hlt.le (by positivity)
        _ = 1.21 * cB / (p : ℝ) ^ g := by ring
    have hcBp : 1.21 * cB / (p : ℝ) ^ g ≤ (if X = 0 then 1.21 * muP p σ / p else 1.21) := by
      rw [hcB]
      split_ifs with hX
      · rw [div_le_div_iff₀ hpg hp]
        have e : (p : ℝ) ^ g = (p : ℝ) ^ (g - 1) * p := by
          rw [← pow_succ]
          congr 1
          omega
        rw [e]
        nlinarith [pow_pos hp (g - 1)]
      · rw [mul_div_assoc, div_self hpg.ne', mul_one]
    unfold cfSd
    calc massB p n σ X * (gam1Sd p n l s σ X t + 1.1 * kapSd p n σ X g) * t
        = massB p n σ X * gam1Sd p n l s σ X t * t + massB p n σ X * (1.1 * kapSd p n σ X g) * t := by
          ring
      _ ≤ gam0 l s + (if X = 0 then 1.21 * muP p σ / p else 1.21) := by
          rw [hγt]
          linarith
  · push Not at hw
    have h2 := hbd.2.2 (fun g hg hgd => hw g hg hgd)
    refine ⟨hγ0, h1.trans ?_, ?_⟩
    · unfold gam1Sd at h2 ⊢
      exact h2
    rw [hγt]
    unfold cfSd
    have : (0 : ℝ) ≤ (if X = 0 then 1.21 * muP p σ / p else 1.21) := by split_ifs <;> positivity
    linarith

end Block

section Pattern

variable {l s k : ℕ}

noncomputable def rhoStarSd {κ : Type*} [Fintype κ] (hne : (univ : Finset κ).Nonempty) (B : κ → Finset (Fin m))
    (w : Fin m → Fin (n + 1) → ZMod p) : ℝ :=
  univ.inf' hne fun b => rhoG (fun j : B b => w j)

theorem pattern_bound_d (hn : 1 ≤ n) (H : BDHyp p (n + 1) l s) (hsk : s ≤ k) (hk : 0 < k) (hm40 : 40 ≤ m)
    {σ : ℝ} (hσ : 0 < σ) (b : Fin (n + 1) → ZMod p) (cls : Fin m → Fin 3)
    (hbig : m ≤ 20 * (DSd cls 0).card) (hMB : ∀ q, m ≤ 20 * q → m / 40 ≤ (k - s) * (q / k))
    {A : ℕ} (hA : 1 < 2 ^ A * ((1 + 1 / 100) / (p : ℝ) ^ (n + 1)))
    (hγ : gam0 l s ≤ 0.02) (hβ : gam0 l s + 1.21 * muP p σ / p ≤ 1) :
    ∃ Hf : (Fin m → Fin (n + 1) → ZMod p) → ℝ, (∀ w, 0 ≤ Hf w) ∧
      (∀ w, prob (fun ω : Pairs m → Bool => krySys ω b w) ≤ Hf w) ∧
      (∏ j, massSd p n σ (cls j)) * pexp (fun j => lawSd σ (cls j)) Hf ≤
        (∏ j, massSd p n σ (cls j)) * ((1 + 1 / 100) / (p : ℝ) ^ (n + 1)) ^ (m - k) +
          A * (2 ^ m * ((p : ℝ) ^ (n + 1)) ^ (3 * k + s * (m / k)) * 1.23 ^ m *
            (gam0 l s + 1.21 * muP p σ / p) ^ (m / 40)) := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set D := DSd cls with hD
  set h : Fin 2 → ℕ := fun X => (D X).card / k with hh
  have hblk : ∀ X, ∃ B : Fin (h X) → Finset (Fin m), (∀ i, B i ⊆ D X) ∧ (∀ i, (B i).card = k) ∧
      Pairwise fun i i' => Disjoint (B i) (B i') :=
    fun X => exists_blocks (D X) k (h X) (Nat.div_mul_le_self _ _)
  choose BX hBXD hBXk hBXdisj using hblk
  set B : (Σ X : Fin 2, Fin (h X)) → Finset (Fin m) := fun b => BX b.1 b.2 with hB
  have hBdisj : Pairwise fun b b' : (Σ X : Fin 2, Fin (h X)) => Disjoint (B b) (B b') := by
    rintro ⟨X, i⟩ ⟨Y, i'⟩ hne
    by_cases hXY : X = Y
    · subst hXY
      have hii : i ≠ i' := fun h' => hne (by rw [h'])
      exact hBXdisj X hii
    · exact Disjoint.mono (hBXD X i) (hBXD Y i') (DSd_disjoint cls hXY)
  have hkm : k ≤ m := by
    have h1 : 1 ≤ m / 40 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
    have h2 := hMB _ hbig
    have h3 : (D 0).card ≤ m := (card_le_univ _).trans (by rw [Fintype.card_fin])
    have h4 : 1 ≤ (D 0).card / k := by
      rcases Nat.eq_zero_or_pos ((D 0).card / k) with h0 | h0
      · rw [h0, mul_zero] at h2
        omega
      · exact h0
    have h6 : k ≤ (D 0).card := by
      have := Nat.div_mul_le_self (D 0).card k
      nlinarith
    omega
  have hh0 : 1 ≤ h 0 := by
    have h1 := hMB _ hbig
    have h2 : 1 ≤ m / 40 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
    show 1 ≤ (D 0).card / k
    rcases Nat.eq_zero_or_pos ((D 0).card / k) with h0 | h0
    · rw [h0, mul_zero] at h1
      omega
    · exact h0
  have hne : (univ : Finset (Σ X : Fin 2, Fin (h X))).Nonempty := ⟨⟨0, ⟨0, hh0⟩⟩, mem_univ _⟩
  set ρs := rhoStarSd (p := p) (n := n) hne B with hρs
  have hρ0 : ∀ w, 0 ≤ ρs w := fun w => (le_inf'_iff _ _).2 fun b _ => rhoG_nonneg _
  have hρ1 : ∀ w, ρs w ≤ 1 := fun w => (inf'_le _ (mem_univ ⟨0, ⟨0, hh0⟩⟩)).trans (rhoG_le_one _)
  have hle : ∀ (w : Fin m → Fin (n + 1) → ZMod p) (t : ℝ), t ≤ ρs w ↔ ∀ b, t ≤ rhoG (fun j : B b => w j) :=
    fun w t => (le_inf'_iff _ _).trans ⟨fun h b => h b (mem_univ b), fun h b _ => h b⟩
  set N := m - k with hN
  refine ⟨fun w => ρs w ^ N, fun w => pow_nonneg (hρ0 w) _, fun w => ?_, ?_⟩
  ·
    obtain ⟨bb, -, hbb⟩ := exists_mem_eq_inf' hne fun b => rhoG (fun j : B b => w j)
    have h1 := lem_seqexp_block w (fun i => companion b (w i)) (B bb)
    have hcard : (B bb).card = k := hBXk bb.1 bb.2
    rw [hcard] at h1
    have e : ρs w = rhoG (fun j : B bb => w j) := hbb
    show prob (fun ω : Pairs m → Bool => krySys ω b w) ≤ ρs w ^ N
    rw [e, hN]
    exact h1
  ·
    set ν := fun j => lawSd (p := p) (n := n) σ (cls j) with hν
    have hν0 : ∀ j a, 0 ≤ ν j a := fun j a => lawSd_nonneg hn _ _ _
    have hν1 : ∀ j, ∑ a, ν j a = 1 := fun j => sum_lawSd hn σ _
    set r0 : ℝ := (1 + 1 / 100) / (p : ℝ) ^ (n + 1) with hr0
    have hr0pos : 0 < r0 := by positivity
    have hlev := pexp_pow_le_levels ν hν0 hν1 ρs hρ0 hρ1 hr0pos N A hA
    set Mc := ∏ j, massSd p n σ (cls j) with hMc
    have hMc0 : 0 ≤ Mc := prod_nonneg fun j _ => (massSd_pos hn σ _).le
    set β := gam0 l s + 1.21 * muP p σ / p with hβdef
    set LB : ℝ := 2 ^ m * ((p : ℝ) ^ (n + 1)) ^ (3 * k + s * (m / k)) * 1.23 ^ m * β ^ (m / 40) with hLB
    have hβ0 : 0 ≤ β := by
      have : 0 ≤ gam0 l s := by unfold gam0; positivity
      have := muP_pos (p := p) σ
      positivity
    have hlevel : ∀ a ∈ range A, Mc * ((2 * (2 ^ a * r0)) ^ N *
        pexp ν (fun w => if 2 ^ a * r0 ≤ ρs w then 1 else 0)) ≤ LB := by
      intro a _
      set t := 2 ^ a * r0 with ht
      have ht0 : 0 < t := by positivity
      have htr : r0 ≤ t := by
        have : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
        rw [ht]
        nlinarith
      have hX0 : 0 ≤ pexp ν (fun w => if t ≤ ρs w then 1 else 0) :=
        pexp_nonneg _ hν0 fun w => by split_ifs <;> norm_num
      by_cases ht1 : t ≤ 1
      ·
        set ζ : Fin 2 → ℝ := fun X => zetaSd p n l s σ X t with hζdef
        have hζ0 : ∀ X, 0 ≤ ζ X := fun X => (block_bound_d (ι := Fin 1) hn H hσ X htr).1
        have hζc : ∀ X, massB p n σ X * ζ X * t ≤ cfSd p l s σ X :=
          fun X => (block_bound_d (ι := Fin 1) hn H hσ X htr).2.2
        have hζb : ∀ (X : Fin 2) (i : Fin (h X)),
            pexp (fun j : B ⟨X, i⟩ => ν j) (fun x => if t ≤ rhoG x then 1 else 0) ≤ ζ X ^ (k - s) := by
          intro X i
          have hlaw : (fun j : B ⟨X, i⟩ => ν j) = fun _ => lawB σ X :=
            funext fun j => lawSd_of_mem_DSd σ (hBXD X i j.2)
          rw [hlaw]
          have h1 := (block_bound_d (ι := B ⟨X, i⟩) hn H hσ X htr).2.1
          rwa [Fintype.card_coe, hBXk X i] at h1
        have hprod : pexp ν (fun w => if t ≤ ρs w then 1 else 0) =
            ∏ b, pexp (fun j : B b => ν j) (fun x => if t ≤ rhoG x then 1 else 0) := by
          rw [← pexp_blocks' ν hν1 B hBdisj (fun b x => if t ≤ rhoG x then 1 else 0)]
          congr 1
          funext w
          rw [prod_boole]
          simp only [hle w t, mem_univ, true_imp_iff]
        have hX : pexp ν (fun w => if t ≤ ρs w then 1 else 0) ≤ ∏ X : Fin 2, ζ X ^ ((k - s) * h X) := by
          rw [hprod]
          calc ∏ b, pexp (fun j : B b => ν j) (fun x => if t ≤ rhoG x then 1 else 0)
              ≤ ∏ b : (Σ X : Fin 2, Fin (h X)), ζ b.1 ^ (k - s) :=
                prod_le_prod₀ (fun b _ => pexp_nonneg (fun j : B b => ν j) (fun j a => hν0 j a)
                  (F := fun x => if t ≤ rhoG x then 1 else 0) fun x => by
                  split_ifs <;> norm_num) fun b _ => hζb b.1 b.2
            _ = ∏ X : Fin 2, ζ X ^ ((k - s) * h X) := by
                rw [Fintype.prod_sigma]
                refine prod_congr rfl fun X _ => ?_
                dsimp only
                rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul]
        have hMc' : Mc = ∏ X : Fin 2, massB p n σ X ^ (D X).card := prod_massSd_eq σ cls
        have htP : 1 ≤ (p : ℝ) ^ (n + 1) * t := by
          have h2a : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
          have e : (p : ℝ) ^ (n + 1) * t = 2 ^ a * (1 + 1 / 100) := by
            rw [ht, hr0]
            field_simp
          rw [e]
          nlinarith
        have hpair := level_pair_bound' (N := N) (m := m) (k := k) (s := s) ht0 ht1
          (P2 := (p : ℝ) ^ (n + 1)) htP
          (massB p n σ) ζ (cfSd p l s σ) (fun X => (massB_pos hn σ X).le)
          (fun X => massB_le hσ.le X) hζ0 hζc (fun X => (D X).card) (sum_card_DSd_le cls)
          (by omega) hsk hk
        rw [Fintype.card_fin] at hpair
        have hcf1 : cfSd p l s σ 1 ≤ 1.23 := by
          unfold cfSd
          rw [ite_eq_right (show ¬ ((1 : Fin 2) = 0) by decide)]
          linarith
        have hcf0 : cfSd p l s σ 0 = β := by
          unfold cfSd
          rw [ite_eq_left rfl]
        have hM0 : m / 40 ≤ (k - s) * ((D 0).card / k) := hMB _ hbig
        have hM1 : (k - s) * ((D 1).card / k) ≤ m := by
          have h1 : (k - s) * ((D 1).card / k) ≤ (D 1).card := chain_le
          have h2 : (D 1).card ≤ m := (card_le_univ _).trans (by rw [Fintype.card_fin])
          omega
        have hchain : ∏ X, cfSd p l s σ X ^ ((k - s) * ((D X).card / k)) ≤ 1.23 ^ m * β ^ (m / 40) := by
          rw [Fin.prod_univ_two, hcf0]
          have h0 : β ^ ((k - s) * ((D 0).card / k)) ≤ β ^ (m / 40) := pow_le_pow_of_le_one hβ0 hβ hM0
          have h1 : cfSd p l s σ 1 ^ ((k - s) * ((D 1).card / k)) ≤ 1.23 ^ m :=
            (pow_le_pow_left₀ (cfSd_nonneg σ 1) hcf1 _).trans (pow_le_pow_right₀ (by norm_num) hM1)
          calc β ^ ((k - s) * ((D 0).card / k)) * cfSd p l s σ 1 ^ ((k - s) * ((D 1).card / k))
              ≤ β ^ (m / 40) * 1.23 ^ m :=
                mul_le_mul h0 h1 (pow_nonneg (cfSd_nonneg σ 1) _) (pow_nonneg hβ0 _)
            _ = 1.23 ^ m * β ^ (m / 40) := by ring
        have h2N : (2 : ℝ) ^ N ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
        calc Mc * ((2 * t) ^ N * pexp ν (fun w => if t ≤ ρs w then 1 else 0))
            ≤ Mc * ((2 * t) ^ N * ∏ X : Fin 2, ζ X ^ ((k - s) * h X)) := by gcongr
          _ = (∏ X : Fin 2, massB p n σ X ^ (D X).card) * (2 * t) ^ N *
                ∏ X : Fin 2, ζ X ^ ((k - s) * ((D X).card / k)) := by
              rw [hMc']
              ring
          _ ≤ 2 ^ N * ((p : ℝ) ^ (n + 1)) ^ ((2 + 1) * k + s * (m / k)) *
                ∏ X, cfSd p l s σ X ^ ((k - s) * ((D X).card / k)) := hpair
          _ ≤ 2 ^ m * ((p : ℝ) ^ (n + 1)) ^ (3 * k + s * (m / k)) * (1.23 ^ m * β ^ (m / 40)) :=
              mul_le_mul (mul_le_mul_of_nonneg_right h2N (by positivity)) hchain
                (prod_nonneg fun X _ => pow_nonneg (cfSd_nonneg σ X) _) (by positivity)
          _ = LB := by rw [hLB]; ring
      ·
        push Not at ht1
        have h0 : pexp ν (fun w => if t ≤ ρs w then 1 else 0) = 0 := by
          rw [show (fun w => if t ≤ ρs w then (1 : ℝ) else 0) = fun _ => 0 from funext fun w => by
            rw [ite_eq_right (not_le.2 (lt_of_le_of_lt (hρ1 w) ht1))]]
          unfold pexp
          simp
        rw [h0, mul_zero, mul_zero]
        positivity
    calc Mc * pexp ν (fun w => ρs w ^ N)
        ≤ Mc * (r0 ^ N + ∑ a ∈ range A, (2 * (2 ^ a * r0)) ^ N *
            pexp ν (fun w => if 2 ^ a * r0 ≤ ρs w then 1 else 0)) := mul_le_mul_of_nonneg_left hlev hMc0
      _ = Mc * r0 ^ N + ∑ a ∈ range A, Mc * ((2 * (2 ^ a * r0)) ^ N *
            pexp ν (fun w => if 2 ^ a * r0 ≤ ρs w then 1 else 0)) := by rw [mul_add, mul_sum]
      _ ≤ Mc * r0 ^ N + ∑ _a ∈ range A, LB := add_le_add le_rfl (sum_le_sum hlevel)
      _ = Mc * r0 ^ N + A * LB := by rw [sum_const, card_range, nsmul_eq_mul]

end Pattern

end DGS
