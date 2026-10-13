module

public import DGS.S11_Deg1.PtLevels
public import DGS.S10_Tools.SeqExp

@[expose] public section

open Finset Matrix Module
open scoped Real

namespace DGS

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

def pairSys (ω : Pairs m → Bool) (b0 b1 : ZMod p) (u : Fin m → ZMod p) (w : Fin m → Fin 2 → ZMod p) :
    Prop :=
  ∀ i, ∑ j, seidelOf ω i j • w j = ![w i 1, u i - b1 * w i 1 - b0 * w i 0]

noncomputable def kapX (p : ℕ) (X : Fin 3) : ℝ := if X = 2 then 1 else 1 / (p : ℝ)

noncomputable def zetaX (p : ℕ) [Fact p.Prime] (l s : ℕ) (σ : ℝ) (X : Fin 3) (t : ℝ) : ℝ :=
  64 * (1 + 1 / 100) * √(π * l) * (1 / massX p σ X) / ((1 / 100) * t * √(s : ℝ)) +
    (if t < 1.1 / p then 1.1 * kapX p X else 0)

theorem zetaX_nonneg {l s : ℕ} {σ t : ℝ} (ht : 0 < t) (X : Fin 3) : 0 ≤ zetaX p l s σ X t := by
  have hm := massX_pos (p := p) σ X
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold zetaX kapX
  split_ifs <;> positivity

section Block

variable {l s : ℕ}

theorem block_bound (H : BDHyp p 2 l s) {σ : ℝ} (hσ : 0 < σ) (ℓ : Fin 2 → ZMod p) (hℓ : ℓ ≠ 0) (X : Fin 3)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℝ} (ht : (1 + 1 / 100) / (p : ℝ) ^ 2 ≤ t) :
    pexp (fun _ : ι => lawX σ ℓ X) (fun w => if t ≤ rhoG w then 1 else 0) ≤
      zetaX p l s σ X t ^ (Fintype.card ι - s) := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hν0 := lawX_nonneg σ ℓ X
  have hν1 := sum_lawX σ ℓ hℓ X
  have h1 : pexp (fun _ : ι => lawX σ ℓ X) (fun w => if t ≤ rhoG w then 1 else 0) ≤
      pmeas (fun _ : ι => lawX σ ℓ X) (fun w => t ≤ rhoHat w) := by
    rw [pmeas_eq_pexp]
    refine pexp_mono _ (fun _ a => hν0 a) fun w => ?_
    split_ifs with h2 h3
    · exact le_rfl
    · exact absurd (h2.trans (rhoG_le_rhoHat w)) h3
    · exact zero_le_one
    · exact le_rfl
  have hbd := prop_blockd (ι := ι) H (lawX σ ℓ X) hν0 hν1 (lawX_zero σ ℓ X)
    (lawX_le hσ.le ℓ X) ht
  have hγ0 : 0 ≤ 64 * (1 + 1 / 100) * √(π * l) * (1 / massX p σ X) / ((1 / 100) * t * √(s : ℝ)) := by
    have := massX_pos (p := p) σ X
    positivity
  refine h1.trans ?_
  by_cases hw : t ∈ window p l s 1
  · have hκ0 : (0 : ℝ) ≤ kapX p X := by unfold kapX; split_ifs <;> positivity
    have hκ : ∀ L : Submodule (ZMod p) (Fin 2 → ZMod p), finrank (ZMod p) L = 1 →
        subMeas (lawX σ ℓ X) L ≤ kapX p X := by
      intro L hL
      unfold kapX
      split_ifs with hX
      · exact subMeas_le_one _ hν0 hν1 L
      · exact subMeas_lawX_le σ ℓ hℓ X hX L hL
    have h2 := hbd.2.1 1 le_rfl (by norm_num) hw (kapX p X) hκ0 hκ
    have hlt : t < 1.1 / p := by
      have := hw.2
      rwa [pow_one] at this
    rw [zetaX, ite_eq_left hlt]
    exact h2
  · have h2 := hbd.2.2 (fun g hg hg2 => by
      have hg1 : g = 1 := by omega
      subst hg1
      exact hw)
    refine h2.trans (pow_le_pow_left₀ hγ0 ?_ _)
    rw [zetaX]
    have : (0 : ℝ) ≤ (if t < 1.1 / p then 1.1 * kapX p X else 0) := by
      unfold kapX
      split_ifs <;> positivity
    linarith

noncomputable def gam0 (l s : ℕ) : ℝ := 6464 * √(π * l) / √(s : ℝ)

theorem massX_zetaX (H : BDHyp p 2 l s) (σ : ℝ) (X : Fin 3) {t : ℝ} (ht : 0 < t) :
    massX p σ X * zetaX p l s σ X t * t =
      gam0 l s + (if t < 1.1 / p then 1.1 * kapX p X * massX p σ X * t else 0) := by
  have hm := (massX_pos (p := p) σ X).ne'
  have hs : (0 : ℝ) < √(s : ℝ) := by
    apply Real.sqrt_pos.2
    have := H.hs4
    have : 1 ≤ s := by have := H.hl; omega
    exact_mod_cast this
  unfold zetaX gam0
  split_ifs
  · field_simp
    ring
  · field_simp
    ring

theorem massX_zetaX_le (H : BDHyp p 2 l s) {σ : ℝ} (_hσ : 0 ≤ σ) (X : Fin 3) {t : ℝ} (ht : 0 < t) :
    massX p σ X * zetaX p l s σ X t * t ≤
      gam0 l s + (if X = 1 then 1.21 * muP p σ / p else 1.21) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 := p_sub_one_pos (p := p)
  have hμ := muP_pos (p := p) σ
  rw [massX_zetaX H σ X ht]
  gcongr
  split_ifs with hlt hX
  ·
    subst hX
    rw [massX_one_eq, kapX, ite_eq_right (by decide)]
    calc 1.1 * (1 / (p : ℝ)) * (p * muP p σ) * t ≤ 1.1 * (1 / (p : ℝ)) * (p * muP p σ) * (1.1 / p) :=
          mul_le_mul_of_nonneg_left hlt.le (by positivity)
      _ = 1.21 * muP p σ / p := by field_simp; ring
  · obtain rfl | rfl | rfl := fin3_cases X
    · rw [massX_zero_eq, kapX, ite_eq_right (by decide)]
      calc 1.1 * (1 / (p : ℝ)) * (p * (p - 1)) * t ≤ 1.1 * (1 / (p : ℝ)) * (p * (p - 1)) * (1.1 / p) :=
            mul_le_mul_of_nonneg_left hlt.le (by positivity)
        _ = 1.21 * ((p - 1) / p) := by field_simp; ring
        _ ≤ 1.21 * 1 := by gcongr; rw [div_le_one hp]; linarith
        _ = 1.21 := by ring
    · exact absurd rfl hX
    · rw [massX_two_eq, kapX, ite_eq_left rfl]
      calc 1.1 * 1 * ((p : ℝ) - 1) * t ≤ 1.1 * 1 * ((p : ℝ) - 1) * (1.1 / p) :=
            mul_le_mul_of_nonneg_left hlt.le (by positivity)
        _ = 1.21 * ((p - 1) / p) := by field_simp; ring
        _ ≤ 1.21 * 1 := by gcongr; rw [div_le_one hp]; linarith
        _ = 1.21 := by ring
  · positivity
  · positivity

theorem muP_le {σ : ℝ} (hσ : 0 ≤ σ) : muP p σ ≤ (p : ℝ) - 1 := by
  unfold muP
  calc ∑ a : ZMod p, (if a ≠ 0 then gaussW σ a.valMinAbs else 0)
      ≤ ∑ a : ZMod p, (if a ≠ 0 then (1 : ℝ) else 0) :=
        sum_le_sum fun a _ => by split_ifs <;> simp [gaussW_le_one hσ]
    _ = (p : ℝ) - 1 := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_ne' univ (0 : ZMod p),
          card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
        have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
        push_cast [hp1]
        ring

theorem massX_le_sq {σ : ℝ} (hσ : 0 ≤ σ) (X : Fin 3) : massX p σ X ≤ (p : ℝ) ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 := p_sub_one_pos (p := p)
  have hμ := muP_le (p := p) hσ
  obtain rfl | rfl | rfl := fin3_cases X
  · rw [massX_zero_eq]
    nlinarith
  · rw [massX_one_eq]
    nlinarith
  · rw [massX_two_eq]
    nlinarith

end Block

section Pattern

variable {l s k : ℕ}

noncomputable def rhoStarG {κ : Type*} [Fintype κ] (hne : (univ : Finset κ).Nonempty) (B : κ → Finset (Fin m))
    (w : Fin m → Fin 2 → ZMod p) : ℝ :=
  univ.inf' hne fun b => rhoG (fun j : B b => w j)

theorem pattern_bound (H : BDHyp p 2 l s) (hsk : s ≤ k) (hk : 0 < k) (hkm : k ≤ m) (hm200 : 200 ≤ m)
    {σ : ℝ} (hσ : 0 < σ) (ℓ : Fin 2 → ZMod p) (hℓ : ℓ ≠ 0) (U : Finset (Fin m)) (b0 b1 : ZMod p)
    (u : Fin m → ZMod p) (cls : Fin m → Fin 3) (hbig : m ≤ 100 * (Dcls U cls 1).card)
    (hMB : ∀ n, m ≤ 100 * n → m / 200 ≤ (k - s) * (n / k))
    {A : ℕ} (hA : 1 < 2 ^ A * ((1 + 1 / 100) / (p : ℝ) ^ 2))
    (hγ : gam0 l s ≤ 0.02) (hβ : gam0 l s + 1.21 * muP p σ / p ≤ 1) :
    ∃ Hf : (Fin m → Fin 2 → ZMod p) → ℝ, (∀ w, 0 ≤ Hf w) ∧
      (∀ w, prob (fun ω : Pairs m → Bool => pairSys ω b0 b1 u w) ≤ Hf w) ∧
      (∏ j, massOf p σ (cls j) (decide (j ∈ U))) * pexp (fun j => lawOf σ ℓ (cls j) (decide (j ∈ U))) Hf ≤
        (∏ j, massOf p σ (cls j) (decide (j ∈ U))) * ((1 + 1 / 100) / (p : ℝ) ^ 2) ^ (m - k) +
          A * (2 ^ m * ((p : ℝ) ^ 2) ^ (4 * k + s * (m / k)) * 1.23 ^ m *
            (gam0 l s + 1.21 * muP p σ / p) ^ (m / 200)) := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set D := Dcls U cls with hD
  set h : Fin 3 → ℕ := fun X => (D X).card / k with hh
  have hblk : ∀ X, ∃ B : Fin (h X) → Finset (Fin m), (∀ i, B i ⊆ D X) ∧ (∀ i, (B i).card = k) ∧
      Pairwise fun i i' => Disjoint (B i) (B i') :=
    fun X => exists_blocks (D X) k (h X) (Nat.div_mul_le_self _ _)
  choose BX hBXD hBXk hBXdisj using hblk
  set B : (Σ X : Fin 3, Fin (h X)) → Finset (Fin m) := fun b => BX b.1 b.2 with hB
  have hBdisj : Pairwise fun b b' : (Σ X : Fin 3, Fin (h X)) => Disjoint (B b) (B b') := by
    rintro ⟨X, i⟩ ⟨Y, i'⟩ hne
    by_cases hXY : X = Y
    · subst hXY
      have hii : i ≠ i' := fun h' => hne (by rw [h'])
      exact hBXdisj X hii
    · exact Disjoint.mono (hBXD X i) (hBXD Y i') (Dcls_disjoint U cls hXY)
  have hh1 : 1 ≤ h 1 := by
    have h1 := hMB _ hbig
    have h2 : 1 ≤ m / 200 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
    by_contra h0
    push Not at h0
    have h3 : h 1 = 0 := by omega
    have h4 : (k - s) * ((D 1).card / k) = 0 := by
      have : (D 1).card / k = 0 := h3
      rw [this, mul_zero]
    omega
  have hne : (univ : Finset (Σ X : Fin 3, Fin (h X))).Nonempty := ⟨⟨1, ⟨0, hh1⟩⟩, mem_univ _⟩
  set ρs := rhoStarG (p := p) hne B with hρs
  have hρ0 : ∀ w, 0 ≤ ρs w := fun w => (le_inf'_iff _ _).2 fun b _ => rhoG_nonneg _
  have hρ1 : ∀ w, ρs w ≤ 1 := fun w => (inf'_le _ (mem_univ ⟨1, ⟨0, hh1⟩⟩)).trans (rhoG_le_one _)
  have hle : ∀ (w : Fin m → Fin 2 → ZMod p) (t : ℝ), t ≤ ρs w ↔ ∀ b, t ≤ rhoG (fun j : B b => w j) :=
    fun w t => (le_inf'_iff _ _).trans ⟨fun h b => h b (mem_univ b), fun h b _ => h b⟩
  set N := m - k with hN
  refine ⟨fun w => ρs w ^ N, fun w => pow_nonneg (hρ0 w) _, fun w => ?_, ?_⟩
  ·
    obtain ⟨b, -, hb⟩ := exists_mem_eq_inf' hne fun b => rhoG (fun j : B b => w j)
    have h1 := lem_seqexp_block w (fun i => ![w i 1, u i - b1 * w i 1 - b0 * w i 0]) (B b)
    have hcard : (B b).card = k := hBXk b.1 b.2
    rw [hcard] at h1
    have e : ρs w = rhoG (fun j : B b => w j) := hb
    show prob (fun ω : Pairs m → Bool => pairSys ω b0 b1 u w) ≤ ρs w ^ N
    rw [e, hN]
    exact h1
  ·
    set ν := fun j => lawOf σ ℓ (cls j) (decide (j ∈ U)) with hν
    have hν0 : ∀ j a, 0 ≤ ν j a := fun j a => lawOf_nonneg _ _ _ _ _
    have hν1 : ∀ j, ∑ a, ν j a = 1 := fun j => sum_lawOf σ ℓ hℓ _ _
    set r0 : ℝ := (1 + 1 / 100) / (p : ℝ) ^ 2 with hr0
    have hr0pos : 0 < r0 := by positivity
    have hlev := pexp_pow_le_levels ν hν0 hν1 ρs hρ0 hρ1 hr0pos N A hA
    set Mc := ∏ j, massOf p σ (cls j) (decide (j ∈ U)) with hMc
    have hMc0 : 0 ≤ Mc := prod_nonneg fun j _ => (massOf_pos σ _ _).le
    set β := gam0 l s + 1.21 * muP p σ / p with hβdef
    set LB : ℝ := 2 ^ m * ((p : ℝ) ^ 2) ^ (4 * k + s * (m / k)) * 1.23 ^ m * β ^ (m / 200) with hLB
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
        have hprod : pexp ν (fun w => if t ≤ ρs w then 1 else 0) =
            ∏ b, pexp (fun j : B b => ν j) (fun x => if t ≤ rhoG x then 1 else 0) := by
          rw [← pexp_blocks' ν hν1 B hBdisj (fun b x => if t ≤ rhoG x then 1 else 0)]
          congr 1
          funext w
          rw [prod_boole]
          simp only [hle w t, mem_univ, true_imp_iff]
        have hblock : ∀ b, pexp (fun j : B b => ν j) (fun x => if t ≤ rhoG x then 1 else 0) ≤
            zetaX p l s σ b.1 t ^ (k - s) := by
          intro b
          have hlaw : (fun j : B b => ν j) = fun _ => lawX σ ℓ b.1 :=
            funext fun j => lawOf_of_mem_Dcls σ ℓ (hBXD b.1 b.2 j.2)
          rw [hlaw]
          have h1 := block_bound (ι := B b) H hσ ℓ hℓ b.1 htr
          rwa [Fintype.card_coe, hBXk b.1 b.2] at h1
        have hX : pexp ν (fun w => if t ≤ ρs w then 1 else 0) ≤
            ∏ X : Fin 3, zetaX p l s σ X t ^ ((k - s) * h X) := by
          rw [hprod]
          calc ∏ b, pexp (fun j : B b => ν j) (fun x => if t ≤ rhoG x then 1 else 0)
              ≤ ∏ b : (Σ X : Fin 3, Fin (h X)), zetaX p l s σ b.1 t ^ (k - s) :=
                prod_le_prod₀ (fun b _ => pexp_nonneg (fun j : B b => ν j) (fun j a => hν0 j a)
                  (F := fun x => if t ≤ rhoG x then 1 else 0) fun x => by
                  split_ifs <;> norm_num) fun b _ => hblock b
            _ = ∏ X : Fin 3, zetaX p l s σ X t ^ ((k - s) * h X) := by
                rw [Fintype.prod_sigma]
                refine prod_congr rfl fun X _ => ?_
                dsimp only
                rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul]
        have hMc' : Mc = ∏ X : Fin 3, massX p σ X ^ (D X).card := prod_massOf_eq σ U cls
        set cf : Fin 3 → ℝ := fun X => gam0 l s + (if X = 1 then 1.21 * muP p σ / p else 1.21) with hcf
        have htP : 1 ≤ (p : ℝ) ^ 2 * t := by
          have h2a : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
          have e : (p : ℝ) ^ 2 * t = 2 ^ a * (1 + 1 / 100) := by
            rw [ht, hr0]
            field_simp
          rw [e]
          nlinarith
        have hpair := level_pair_bound (N := N) (m := m) (k := k) (s := s) ht0 ht1
          (P2 := (p : ℝ) ^ 2) htP
          (massX p σ) (fun X => zetaX p l s σ X t) cf (fun X => (massX_pos σ X).le)
          (fun X => massX_le_sq hσ.le X) (fun X => zetaX_nonneg ht0 X)
          (fun X => massX_zetaX_le H hσ.le X ht0) (fun X => (D X).card) (sum_card_Dcls_le U cls)
          (by omega) hsk hk
        have hcf02 : ∀ X, X ≠ 1 → cf X ≤ 1.23 := by
          intro X hX
          simp only [hcf, ite_eq_right hX]
          linarith
        have hcf0 : ∀ X, 0 ≤ cf X := by
          intro X
          have : 0 ≤ gam0 l s := by unfold gam0; positivity
          have := muP_pos (p := p) σ
          simp only [hcf]
          split_ifs <;> positivity
        have hM1 : m / 200 ≤ (k - s) * ((D 1).card / k) := hMB _ hbig
        have hM02 : (k - s) * ((D 0).card / k) + (k - s) * ((D 2).card / k) ≤ m := by
          have h1 := sum_card_Dcls_le U cls
          rw [Fin.sum_univ_three] at h1
          have h2 : (k - s) * ((D 0).card / k) ≤ (D 0).card := chain_le
          have h3 : (k - s) * ((D 2).card / k) ≤ (D 2).card := chain_le
          rw [hD] at h2 h3 ⊢
          omega
        have hchain : ∏ X, cf X ^ ((k - s) * ((D X).card / k)) ≤ 1.23 ^ m * β ^ (m / 200) := by
          rw [Fin.prod_univ_three]
          have h0 : cf 0 ^ ((k - s) * ((D 0).card / k)) ≤ 1.23 ^ ((k - s) * ((D 0).card / k)) :=
            pow_le_pow_left₀ (hcf0 0) (hcf02 0 (by decide)) _
          have h2 : cf 2 ^ ((k - s) * ((D 2).card / k)) ≤ 1.23 ^ ((k - s) * ((D 2).card / k)) :=
            pow_le_pow_left₀ (hcf0 2) (hcf02 2 (by decide)) _
          have hc1 : cf 1 = β := by simp [hcf, hβdef]
          have h1 : cf 1 ^ ((k - s) * ((D 1).card / k)) ≤ β ^ (m / 200) := by
            rw [hc1]
            exact pow_le_pow_of_le_one hβ0 hβ hM1
          have h02 : (1.23 : ℝ) ^ ((k - s) * ((D 0).card / k)) * 1.23 ^ ((k - s) * ((D 2).card / k)) ≤
              1.23 ^ m := by
            rw [← pow_add]
            exact pow_le_pow_right₀ (by norm_num) hM02
          calc cf 0 ^ ((k - s) * ((D 0).card / k)) * cf 1 ^ ((k - s) * ((D 1).card / k)) *
                cf 2 ^ ((k - s) * ((D 2).card / k))
              ≤ 1.23 ^ ((k - s) * ((D 0).card / k)) * β ^ (m / 200) *
                  1.23 ^ ((k - s) * ((D 2).card / k)) :=
                mul_le_mul (mul_le_mul h0 h1 (pow_nonneg (hcf0 1) _) (by positivity)) h2
                  (pow_nonneg (hcf0 2) _) (mul_nonneg (by positivity) (pow_nonneg hβ0 _))
            _ = (1.23 ^ ((k - s) * ((D 0).card / k)) * 1.23 ^ ((k - s) * ((D 2).card / k))) *
                  β ^ (m / 200) := by ring
            _ ≤ 1.23 ^ m * β ^ (m / 200) := by gcongr
        have h2N : (2 : ℝ) ^ N ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
        calc Mc * ((2 * t) ^ N * pexp ν (fun w => if t ≤ ρs w then 1 else 0))
            ≤ Mc * ((2 * t) ^ N * ∏ X : Fin 3, zetaX p l s σ X t ^ ((k - s) * h X)) := by gcongr
          _ = (∏ X : Fin 3, massX p σ X ^ (D X).card) * (2 * t) ^ N *
                ∏ X : Fin 3, zetaX p l s σ X t ^ ((k - s) * ((D X).card / k)) := by
              rw [hMc']
              ring
          _ ≤ 2 ^ N * ((p : ℝ) ^ 2) ^ (4 * k + s * (m / k)) * ∏ X, cf X ^ ((k - s) * ((D X).card / k)) :=
              hpair
          _ ≤ 2 ^ m * ((p : ℝ) ^ 2) ^ (4 * k + s * (m / k)) * (1.23 ^ m * β ^ (m / 200)) :=
              mul_le_mul (mul_le_mul_of_nonneg_right h2N (by positivity)) hchain
                (prod_nonneg fun X _ => pow_nonneg (hcf0 X) _) (by positivity)
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
