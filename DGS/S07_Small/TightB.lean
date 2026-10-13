module

public import DGS.S07_Small.HenselBasis

@[expose] public section

open Matrix Polynomial Filter Topology Module

namespace DGS

section Sets

variable (p : ℕ) [hp : Fact p.Prime]

open Classical in
noncomputable def hFrames (E s n r : ℕ) : Finset (Matrix (Fin n) (Fin r) (ZMod (p ^ E))) :=
  Finset.univ.filter fun V => IsRobustE p E s V ∧ IsUnit (Vᵀ * V).det

open Classical in
noncomputable def compK (E : ℕ) {n r : ℕ} (V : Matrix (Fin n) (Fin r) (ZMod (p ^ E))) :
    Finset (Matrix (Fin r) (Fin r) (ZMod (p ^ E))) :=
  Finset.univ.filter fun B => ((Vᵀ * V) * B)ᵀ = (Vᵀ * V) * B ∧
    (krylov B ((Vᵀ * V)⁻¹ *ᵥ (Vᵀ *ᵥ ones n (ZMod (p ^ E))))).det = 0

open Classical in
noncomputable def pairSet (E s n r : ℕ) :
    Finset (Matrix (Fin n) (Fin r) (ZMod (p ^ E)) × Matrix (Fin r) (Fin r) (ZMod (p ^ E))) :=
  (hFrames p E s n r ×ˢ Finset.univ).filter fun VB => VB.2 ∈ compK p E VB.1

variable {p}

theorem mem_hFrames_iff {E s n r : ℕ} {V : Matrix (Fin n) (Fin r) (ZMod (p ^ E))} :
    V ∈ hFrames p E s n r ↔ IsRobustE p E s V ∧ IsUnit (Vᵀ * V).det := by
  classical
  simp only [hFrames, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_compK_iff {E n r : ℕ} {V : Matrix (Fin n) (Fin r) (ZMod (p ^ E))}
    {B : Matrix (Fin r) (Fin r) (ZMod (p ^ E))} :
    B ∈ compK p E V ↔ ((Vᵀ * V) * B)ᵀ = (Vᵀ * V) * B ∧
      (krylov B ((Vᵀ * V)⁻¹ *ᵥ (Vᵀ *ᵥ ones n (ZMod (p ^ E))))).det = 0 := by
  classical
  simp only [compK, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_pairSet_iff {E s n r : ℕ}
    {VB : Matrix (Fin n) (Fin r) (ZMod (p ^ E)) × Matrix (Fin r) (Fin r) (ZMod (p ^ E))} :
    VB ∈ pairSet p E s n r ↔ VB.1 ∈ hFrames p E s n r ∧ VB.2 ∈ compK p E VB.1 := by
  classical
  simp only [pairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]

end Sets

def EventY (p : ℕ) [Fact p.Prime] (β : (ZMod p)[X]) (a E : ℕ) {n : ℕ} (ω : Pairs n → Bool) :
    Prop :=
  (walkMatrix (symOf 1 0 ω)).det ≠ 0 ∧ β ∈ factorsSet (redP p (symOf 1 0 ω).charpoly) ∧
    mult (redP p (symOf 1 0 ω).charpoly) β = a ∧ NoShort (1 / 4) n ω ∧
    ∃ y ∈ mPart (symOf 1 0 ω) p β (latZ n), ((p : ℤ) ^ (E - 1)) • y ∉ latC (symOf 1 0 ω)

section Count

variable {p : ℕ} [hp : Fact p.Prime]

theorem map_cast_eq_map_redE {E : ℕ} (hE : 1 ≤ E) {n r : ℕ}
    (V : Matrix (Fin n) (Fin r) (ZMod (p ^ E))) :
    V.map (ZMod.cast : ZMod (p ^ E) → ZMod p) = V.map (redE p E hE) := by
  ext i j
  simp only [Matrix.map_apply, redE, ZMod.castHom_apply]

theorem Y_count {n a E : ℕ} {β : (ZMod p)[X]} (hE : 1 ≤ E) (hn : 1 ≤ n)
    (hR : (p, a * β.natDegree) ∈ Rn (1 / 4) n) (ω : Pairs n → Bool) (hY : EventY p β a E ω) :
    p ^ ((E - 1) * ((a * β.natDegree) * (a * β.natDegree))) ≤
      ((pairSet p E (sDelta (1 / 4) n) n (a * β.natDegree)).filter fun VB =>
        modP (p ^ E) (symOf 1 0 ω) * VB.1 = VB.1 * VB.2).card := by
  classical
  obtain ⟨hW, hβ, hmult, hN, hexp⟩ := hY
  set A := symOf 1 0 ω with hAdef
  set r := a * β.natDegree with hrdef
  have hr : mult (redP p A.charpoly) β * β.natDegree = r := by rw [hmult]
  have hA : A.IsSymm := Matrix.IsSymm.ext fun i j => symOf_comm _ _ _ j i
  have hβm := monic_of_mem_factorsSet hβ
  set V0' := V0 hβ hr hE with hV0'
  set AE := modP (p ^ E) A with hAE
  have hAEs : AEᵀ = AE := (modP_isSymm (p ^ E) hA).eq
  rw [← card_fiber_one hE r]
  have hV0u : IsUnit (V0'ᵀ * V0').det := isUnit_det_gram hβ hr hE hA rfl
  set Φ : Matrix (Fin r) (Fin r) (ZMod (p ^ E)) →
      Matrix (Fin n) (Fin r) (ZMod (p ^ E)) × Matrix (Fin r) (Fin r) (ZMod (p ^ E)) :=
    fun g => (V0' * g, ((V0' * g)ᵀ * (V0' * g))⁻¹ * ((V0' * g)ᵀ * (AE * (V0' * g)))) with hΦ
  apply Finset.card_le_card_of_injOn Φ
  · intro g hg
    rw [Finset.mem_coe, Finset.mem_filter] at hg
    obtain ⟨hcol, hspan, hred⟩ := hbasis_mul hβ hr hE hg.2
    set V := V0' * g with hV
    have hΘ : IsUnit (Vᵀ * V).det := isUnit_det_gram hβ hr hE hA hred
    set B := (Vᵀ * V)⁻¹ * (Vᵀ * (AE * V)) with hB
    have hcolA : ∀ j, ∃ c, AE *ᵥ (fun k => V k j) = V *ᵥ c := fun j =>
      hspan _ (NE_isInvariant hβ (hcol j))
    choose C hC using hcolA
    have hAVC : AE * V = V * Matrix.of fun i j => C j i := by
      ext k j
      have h1 := congrFun (hC j) k
      simp only [mulVec, dotProduct] at h1
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simpa using h1
    have hBC : B = Matrix.of fun i j => C j i := by
      rw [hB, hAVC, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (Vᵀ * V)⁻¹ Vᵀ V,
        nonsing_inv_mul _ hΘ, Matrix.one_mul]
    have hAV : AE * V = V * B := by rw [hBC]; exact hAVC
    have hΘB : (Vᵀ * V) * B = Vᵀ * (AE * V) := by
      rw [hB, ← Matrix.mul_assoc, mul_nonsing_inv _ hΘ, Matrix.one_mul]
    rw [Finset.mem_coe, Finset.mem_filter, mem_pairSet_iff, mem_hFrames_iff, mem_compK_iff]
    refine ⟨⟨⟨?_, hΘ⟩, ?_, ?_⟩, hAV⟩
    ·
      show IsRobust (sDelta (1 / 4) n) (V.map (ZMod.cast : ZMod (p ^ E) → ZMod p))
      rw [map_cast_eq_map_redE hE, hred]
      intro c hc
      have hz0 := V0_map_mulVec_ne_zero hβ hr hE hc
      have hzK := V0_map_mulVec_mem hβ hr hE c
      rw [mem_kerBar, hmult] at hzK
      by_contra hlt
      push Not at hlt
      have hwt : 0 < wt (V0'.map (redE p E hE) *ᵥ c) := by
        obtain ⟨i, hi⟩ : ∃ i, (V0'.map (redE p E hE) *ᵥ c) i ≠ 0 := by
          by_contra h; push Not at h; exact hz0 (funext h)
        exact Finset.card_pos.2 ⟨i, by simp [hi]⟩
      exact hN p hp.out (β ^ a) (hβm.pow a) (by rw [natDegree_pow]; exact hR) _ hwt hlt hzK
    · rw [hΘB, transpose_mul, transpose_mul, transpose_transpose, hAEs, Matrix.mul_assoc]
    · exact lem_hensel hA hn hW hβ hE V hcol hspan hΘ B hAV hexp
  · intro g hg g' hg' h
    have h1 : V0' * g = V0' * g' := congrArg Prod.fst h
    have h2 : (V0'ᵀ * V0')⁻¹ * V0'ᵀ * (V0' * g) = (V0'ᵀ * V0')⁻¹ * V0'ᵀ * (V0' * g') := by rw [h1]
    have e : ∀ M : Matrix (Fin r) (Fin r) (ZMod (p ^ E)),
        (V0'ᵀ * V0')⁻¹ * V0'ᵀ * (V0' * M) = M := by
      intro M
      rw [← Matrix.mul_assoc, Matrix.mul_assoc _ V0'ᵀ V0', nonsing_inv_mul _ hV0u, Matrix.one_mul]
    rw [e, e] at h2
    exact h2

end Count

section GK

variable {r : ℕ} {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

open Classical in
noncomputable def gK (x : Matrix (Fin r) (Fin r) R × (Fin r → R)) : ℕ :=
  if IsUnit x.1.det then
    (Finset.univ.filter fun z : UT r → R => Fdet x.1 x.2 (symOfUT z) = 0).card
  else 0

theorem gK_le (x : Matrix (Fin r) (Fin r) R × (Fin r → R)) :
    gK x ≤ (Finset.univ.filter fun z : UT r → R => Fdet x.1 x.2 (symOfUT z) = 0).card := by
  classical
  unfold gK
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem gK_le_card (x : Matrix (Fin r) (Fin r) R × (Fin r → R)) :
    gK x ≤ Fintype.card R ^ (r * (r + 1) / 2) := by
  classical
  refine (gK_le x).trans ((Finset.card_filter_le _ _).trans (le_of_eq ?_))
  rw [Finset.card_univ, Fintype.card_fun, card_UT]

omit [Fintype R] [DecidableEq R] in
theorem symOfUT_coords {M : Matrix (Fin r) (Fin r) R} (hM : Mᵀ = M) :
    symOfUT (fun c : UT r => M c.1.1 c.1.2) = M := by
  have : Sum.elim (fun c : UT r => M c.1.1 c.1.2) (fun _ => (0 : R)) = coordsG M (fun _ => 0) := by
    funext c; rcases c with c | i <;> rfl
  rw [symOfUT, this, fromCoords_coordsG hM]

end GK

section CountB

variable {p : ℕ} [hp : Fact p.Prime]

theorem card_compK_le {E n r : ℕ} (V : Matrix (Fin n) (Fin r) (ZMod (p ^ E)))
    (hV : IsUnit (Vᵀ * V).det) :
    (compK p E V).card ≤ gK (Vᵀ * V, Vᵀ *ᵥ ones n (ZMod (p ^ E))) := by
  classical
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  unfold gK
  rw [ite_eq_left hV]
  apply Finset.card_le_card_of_injOn (fun B => fun c : UT r => ((Vᵀ * V) * B) c.1.1 c.1.2)
  · intro B hB
    rw [Finset.mem_coe, mem_compK_iff] at hB
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only
    rw [symOfUT_coords hB.1, Fdet_mul_eq hV, hB.2, mul_zero]
  · intro B hB B' hB' h
    rw [Finset.mem_coe, mem_compK_iff] at hB hB'
    have h1 : (Vᵀ * V) * B = (Vᵀ * V) * B' := by
      rw [← symOfUT_coords hB.1, ← symOfUT_coords hB'.1]
      exact congrArg symOfUT h
    have h2 := congrArg (fun M => (Vᵀ * V)⁻¹ * M) h1
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hV, Matrix.one_mul] at h2
    exact h2

theorem card_pairSet_eq {E s n r : ℕ} :
    (pairSet p E s n r).card = ∑ V ∈ hFrames p E s n r, (compK p E V).card := by
  classical
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  rw [pairSet, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [← Finset.card_filter]
  congr 1
  ext B
  simp

theorem sum_card_Fdet (q : ℕ) [NeZero q] (r : ℕ) :
    ∑ y : GI r → ZMod q, ((Finset.univ.filter fun z : UT r → ZMod q =>
      Fdet (fromCoords y).1 (fromCoords y).2 (symOfUT z) = 0).card : ℝ) =
    ((Finset.univ.filter fun x : KVar r → ZMod q =>
      MvPolynomial.eval₂ (Int.castRingHom (ZMod q)) x (FKr r) = 0).card : ℝ) := by
  classical
  simp_rw [eval_FKr]
  rw [Finset.card_filter]
  push_cast
  rw [← (Equiv.sumArrowEquivProdArrow (GI r) (UT r) (ZMod q)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun z _ => ?_
  rfl

omit hp in
theorem sum_gram_le {q : ℕ} [NeZero q]
    (hpar : ∀ w : ZMod q, (∀ b : Tor2 q, b.1 * w = 0) ↔ (p = 2 → ∃ y : ZMod q, w = 2 * y))
    {c : ℝ} (hc0 : 0 ≤ c) {r : ℕ}
    (hc : ∀ ξ : GI r → ZMod q, ξ ∉ Zset r q → ‖Sxi ξ‖ ≤ c * (q : ℝ) ^ r) (n : ℕ)
    (G : Matrix (Fin r) (Fin r) (ZMod q) × (Fin r → ZMod q) → ℝ) (hG0 : ∀ x, 0 ≤ G x) {Gmax : ℝ}
    (hGmax : ∀ x, G x ≤ Gmax) :
    ∑ V : Matrix (Fin n) (Fin r) (ZMod q), G (Vᵀ * V, Vᵀ *ᵥ (fun _ => 1)) ≤
      (q : ℝ) ^ (n * r) * (∑ x, G x * muGram p q r x +
        Gmax * ((q : ℝ) ^ (r * (r + 3) / 2) * c ^ n)) := by
  classical
  set f : Matrix (Fin n) (Fin r) (ZMod q) → Matrix (Fin r) (Fin r) (ZMod q) × (Fin r → ZMod q) :=
    fun V => (Vᵀ * V, Vᵀ *ᵥ (fun _ => 1)) with hf
  set P : Matrix (Fin r) (Fin r) (ZMod q) × (Fin r → ZMod q) → ℝ := fun x =>
    prob (fun V : Matrix (Fin n) (Fin r) (ZMod q) => Vᵀ * V = x.1 ∧ Vᵀ *ᵥ (fun _ => 1) = x.2)
    with hP
  have hcard : ((Fintype.card (Matrix (Fin n) (Fin r) (ZMod q)) : ℕ) : ℝ) = (q : ℝ) ^ (n * r) := by
    rw [show Fintype.card (Matrix (Fin n) (Fin r) (ZMod q)) =
      Fintype.card (Fin n → Fin r → ZMod q) from rfl, Fintype.card_fun, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rw [← pow_mul, mul_comm r n]
  have hfib : ∀ x, ((Finset.univ.filter fun V => f V = x).card : ℝ) = (q : ℝ) ^ (n * r) * P x := by
    intro x
    simp only [hP]
    rw [prob_eq_card_filter, hcard]
    have : (Finset.univ.filter fun V => f V = x) = Finset.univ.filter fun V : Matrix (Fin n) (Fin r) (ZMod q) =>
        Vᵀ * V = x.1 ∧ Vᵀ *ᵥ (fun _ => 1) = x.2 := by
      ext V; simp [hf, Prod.ext_iff]
    rw [this]
    have hq0 : (q : ℝ) ^ (n * r) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne q)
    field_simp
  have h1 : ∑ V : Matrix (Fin n) (Fin r) (ZMod q), G (f V) = ∑ x, (q : ℝ) ^ (n * r) * P x * G x := by
    rw [← Finset.sum_fiberwise' Finset.univ f G]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, hfib]
  have htv := sum_abs_prob_gram_sub_le hpar hc0 hc n
  have h2 : ∑ x, P x * G x ≤ ∑ x, G x * muGram p q r x + Gmax * ((q : ℝ) ^ (r * (r + 3) / 2) * c ^ n) := by
    have hGmax0 : 0 ≤ Gmax := (hG0 0).trans (hGmax 0)
    calc ∑ x, P x * G x ≤ ∑ x, (G x * muGram p q r x + Gmax * |P x - muGram p q r x|) := by
          refine Finset.sum_le_sum fun x _ => ?_
          have h3 : P x ≤ muGram p q r x + |P x - muGram p q r x| := by
            have := le_abs_self (P x - muGram p q r x); linarith
          have h4 : 0 ≤ |P x - muGram p q r x| := abs_nonneg _
          calc P x * G x ≤ (muGram p q r x + |P x - muGram p q r x|) * G x :=
                mul_le_mul_of_nonneg_right h3 (hG0 x)
            _ = G x * muGram p q r x + G x * |P x - muGram p q r x| := by ring
            _ ≤ G x * muGram p q r x + Gmax * |P x - muGram p q r x| := by
                gcongr; exact hGmax x
      _ = ∑ x, G x * muGram p q r x + Gmax * ∑ x, |P x - muGram p q r x| := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ x, G x * muGram p q r x + Gmax * ((q : ℝ) ^ (r * (r + 3) / 2) * c ^ n) := by
          gcongr
  calc ∑ V : Matrix (Fin n) (Fin r) (ZMod q), G (Vᵀ * V, Vᵀ *ᵥ (fun _ => 1))
      = ∑ x, (q : ℝ) ^ (n * r) * P x * G x := h1
    _ = (q : ℝ) ^ (n * r) * ∑ x, P x * G x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ (q : ℝ) ^ (n * r) * (∑ x, G x * muGram p q r x +
        Gmax * ((q : ℝ) ^ (r * (r + 3) / 2) * c ^ n)) := by
        gcongr

omit hp in
theorem sum_mul_muGram_le {q : ℕ} [NeZero q] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) (ZMod q) × (Fin r → ZMod q) → ℝ) (hG0 : ∀ x, 0 ≤ G x) :
    ∑ x, G x * muGram p q r x ≤
      ((GramSet p q r).card : ℝ)⁻¹ * ∑ y : GI r → ZMod q, G (fromCoords y) := by
  classical
  have h1 : ∑ x, G x * muGram p q r x = ((GramSet p q r).card : ℝ)⁻¹ * ∑ x ∈ GramSet p q r, G x := by
    rw [Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ (GramSet p q r))]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [muGram, ite_eq_left hx, mul_comm]
    · intro x _ hx
      rw [muGram, ite_eq_right hx, mul_zero]
  have hsub : GramSet p q r ⊆ Finset.univ.image fromCoords := by
    intro x hx
    have hsym : x.1ᵀ = x.1 := by
      simp only [GramSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx.1
    rw [Finset.mem_image]
    exact ⟨coordsG x.1 x.2, Finset.mem_univ _, fromCoords_coordsG hsym x.2⟩
  have h2 : ∑ x ∈ GramSet p q r, G x ≤ ∑ y : GI r → ZMod q, G (fromCoords y) := by
    calc ∑ x ∈ GramSet p q r, G x ≤ ∑ x ∈ Finset.univ.image fromCoords, G x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hG0 x
      _ = ∑ y : GI r → ZMod q, G (fromCoords y) :=
          Finset.sum_image fun y _ y' _ h => fromCoords_injective h
  rw [h1]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

end CountB

section ProbY

variable {p : ℕ} [hp : Fact p.Prime]

noncomputable def Zcount (p : ℕ) [Fact p.Prime] (E r : ℕ) : ℝ :=
  ((Finset.univ.filter fun x : KVar r → ZMod (p ^ E) =>
    MvPolynomial.eval₂ (Int.castRingHom (ZMod (p ^ E))) x (FKr r) = 0).card : ℝ)

theorem prob_Y_le_sum {n a E : ℕ} {β : (ZMod p)[X]} (hE : 1 ≤ E) (hn1 : 1 ≤ n)
    (hR : (p, a * β.natDegree) ∈ Rn (1 / 4) n) :
    prob (fun ω : Pairs n → Bool => EventY p β a E ω) *
        (p : ℝ) ^ ((E - 1) * ((a * β.natDegree) * (a * β.natDegree))) ≤
      ∑ VB ∈ pairSet p E (sDelta (1 / 4) n) n (a * β.natDegree),
        prob (fun ω : Pairs n → Bool => modP (p ^ E) (symOf 1 0 ω) * VB.1 = VB.1 * VB.2) := by
  classical
  rw [← expect_indicator', mul_comm, ← expect_const_mul]
  have hind : ∀ ω : Pairs n → Bool,
      (p : ℝ) ^ ((E - 1) * ((a * β.natDegree) * (a * β.natDegree))) *
        @ite ℝ (EventY p β a E ω) (Classical.dec _) 1 0 ≤
      ∑ VB ∈ pairSet p E (sDelta (1 / 4) n) n (a * β.natDegree),
        (if modP (p ^ E) (symOf 1 0 ω) * VB.1 = VB.1 * VB.2 then (1 : ℝ) else 0) := by
    intro ω
    by_cases h : EventY p β a E ω
    · rw [ite_eq_left h, mul_one]
      have h1 := Y_count hE hn1 hR ω h
      rw [← Nat.cast_le (α := ℝ)] at h1
      push_cast at h1
      refine h1.trans (le_of_eq ?_)
      rw [Finset.card_filter]
      push_cast
      rfl
    · rw [ite_eq_right h, mul_zero]
      exact Finset.sum_nonneg fun _ _ => by positivity
  refine (expect_mono hind).trans (le_of_eq ?_)
  rw [expect_sum]
  exact Finset.sum_congr rfl fun VB _ => expect_indicator _

theorem card_pairSet_le {E s n r : ℕ} (hE : 1 ≤ E) (hr1 : 1 ≤ r) :
    ((pairSet p E s n r).card : ℝ) ≤ ((p ^ E : ℕ) : ℝ) ^ (n * r) *
      (((GramSet p (p ^ E) r).card : ℝ)⁻¹ * Zcount p E r +
        ((p ^ E : ℕ) : ℝ) ^ (r * (r + 1) / 2) *
          (((p ^ E : ℕ) : ℝ) ^ (r * (r + 3) / 2) * cGram (p ^ E) r ^ n)) := by
  classical
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  obtain ⟨hc0, -, hc⟩ := cGram_bounds (two_le_pow (p := p) hE) hr1
  have hpar := fun w => tor2_mul_eq_zero_iff (p := p) hE w
  have hGmax : ∀ x : Matrix (Fin r) (Fin r) (ZMod (p ^ E)) × (Fin r → ZMod (p ^ E)),
      (gK x : ℝ) ≤ ((p ^ E : ℕ) : ℝ) ^ (r * (r + 1) / 2) := by
    intro x
    have h := gK_le_card x
    rw [ZMod.card] at h
    exact_mod_cast h
  have h1 : ((pairSet p E s n r).card : ℝ) ≤ ∑ V : Matrix (Fin n) (Fin r) (ZMod (p ^ E)),
      (gK (Vᵀ * V, Vᵀ *ᵥ (fun _ => (1 : ZMod (p ^ E)))) : ℝ) := by
    rw [card_pairSet_eq]
    push_cast
    calc ∑ V ∈ hFrames p E s n r, ((compK p E V).card : ℝ)
        ≤ ∑ V ∈ hFrames p E s n r,
            (gK (Vᵀ * V, Vᵀ *ᵥ (fun _ => (1 : ZMod (p ^ E)))) : ℝ) := by
          refine Finset.sum_le_sum fun V hV => ?_
          rw [mem_hFrames_iff] at hV
          exact_mod_cast card_compK_le V hV.2
      _ ≤ ∑ V : Matrix (Fin n) (Fin r) (ZMod (p ^ E)),
            (gK (Vᵀ * V, Vᵀ *ᵥ (fun _ => (1 : ZMod (p ^ E)))) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.cast_nonneg _
  have h2 := sum_gram_le hpar hc0 hc n
    (fun x : Matrix (Fin r) (Fin r) (ZMod (p ^ E)) × (Fin r → ZMod (p ^ E)) => (gK x : ℝ))
    (fun x => Nat.cast_nonneg _) hGmax
  have h3 := sum_mul_muGram_le (p := p) (q := p ^ E) (r := r)
    (fun x : Matrix (Fin r) (Fin r) (ZMod (p ^ E)) × (Fin r → ZMod (p ^ E)) => (gK x : ℝ))
    (fun x => Nat.cast_nonneg _)
  have h4 : ∑ y : GI r → ZMod (p ^ E), (gK (fromCoords y) : ℝ) ≤ Zcount p E r := by
    rw [Zcount, ← sum_card_Fdet (p ^ E) r]
    refine Finset.sum_le_sum fun y _ => ?_
    exact_mod_cast gK_le (fromCoords y)
  have hG0 : (0 : ℝ) ≤ ((GramSet p (p ^ E) r).card : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  have hq0 : (0 : ℝ) ≤ ((p ^ E : ℕ) : ℝ) ^ (n * r) := pow_nonneg (Nat.cast_nonneg _) _
  refine h1.trans (h2.trans ?_)
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hq0
  exact h3.trans (mul_le_mul_of_nonneg_left h4 hG0)

theorem prob_Y_le {β : (ZMod p)[X]} {a E : ℕ} (hd : 1 ≤ β.natDegree) (ha : 1 ≤ a) (hE : 1 ≤ E) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      prob (fun ω : Pairs n → Bool => EventY p β a E ω) *
          (p : ℝ) ^ ((E - 1) * ((a * β.natDegree) * (a * β.natDegree))) ≤
        (1 + |ε n|) * ((antisymm (a * β.natDegree) (p ^ E)).card *
          (((GramSet p (p ^ E) (a * β.natDegree)).card : ℝ)⁻¹ * Zcount p E (a * β.natDegree) +
            ((p ^ E : ℕ) : ℝ) ^ ((a * β.natDegree) * ((a * β.natDegree) + 1) / 2) *
              (((p ^ E : ℕ) : ℝ) ^ ((a * β.natDegree) * ((a * β.natDegree) + 3) / 2) *
                cGram (p ^ E) (a * β.natDegree) ^ n))) := by
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  obtain ⟨ε, hε, hev⟩ := lem_fourier_b_gen (δ := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨ε, hε, ?_⟩
  have hr1 : 1 ≤ a * β.natDegree := Nat.mul_pos ha hd
  filter_upwards [hev, eventually_mem_Rn (δ := 1 / 4) (by norm_num) (by norm_num) hp.out hr1,
    eventually_mem_Rn (δ := 1 / 4) (by norm_num) (by norm_num) hp.out
      (show 1 ≤ p ^ (E - 1) * (a * β.natDegree) from Nat.mul_pos (pow_pos hp.out.pos _) hr1),
    eventually_ge_atTop 1] with n hn hR hR' hn1
  obtain ⟨-, -, hmδ, hqm⟩ := hR'
  have hmδ' : ((a * β.natDegree : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) / Real.log n ^ 2 := by
    refine le_trans ?_ hmδ
    have : a * β.natDegree ≤ p ^ (E - 1) * (a * β.natDegree) :=
      Nat.le_mul_of_pos_left _ (pow_pos hp.out.pos _)
    exact_mod_cast this
  have hqm' : ((p ^ E * (a * β.natDegree) : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 2 - 1 / 4 : ℝ) / Real.log n := by
    have hpE : p ^ E = p * p ^ (E - 1) := by rw [← pow_succ', Nat.sub_add_cancel hE]
    have : p ^ E * (a * β.natDegree) = p * (p ^ (E - 1) * (a * β.natDegree)) := by
      rw [hpE]; ring
    rw [this]
    exact hqm
  set b : ℝ := (1 + |ε n|) * ((((p ^ E : ℕ) : ℝ) ^ (n * (a * β.natDegree)))⁻¹ *
    (antisymm (a * β.natDegree) (p ^ E)).card) with hb
  have hB : ∀ VB ∈ pairSet p E (sDelta (1 / 4) n) n (a * β.natDegree),
      prob (fun ω : Pairs n → Bool => modP (p ^ E) (symOf 1 0 ω) * VB.1 = VB.1 * VB.2) ≤ b := by
    intro VB hVB
    rw [mem_pairSet_iff, mem_hFrames_iff] at hVB
    have h := hn p E (p ^ E) (a * β.natDegree) rfl hE hr1 hmδ' hqm' VB.1 hVB.1.1 (VB.1 * VB.2)
    refine h.trans ?_
    rw [hb]
    gcongr
    exact le_abs_self _
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hqpos : (0 : ℝ) < ((p ^ E : ℕ) : ℝ) ^ (n * (a * β.natDegree)) := by
    have : (0 : ℝ) < ((p ^ E : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.out.pos E
    positivity
  have hC := card_pairSet_le (p := p) (s := sDelta (1 / 4) n) (n := n) hE hr1
  calc prob (fun ω : Pairs n → Bool => EventY p β a E ω) *
        (p : ℝ) ^ ((E - 1) * ((a * β.natDegree) * (a * β.natDegree)))
      ≤ ∑ VB ∈ pairSet p E (sDelta (1 / 4) n) n (a * β.natDegree),
          prob (fun ω : Pairs n → Bool => modP (p ^ E) (symOf 1 0 ω) * VB.1 = VB.1 * VB.2) :=
        prob_Y_le_sum hE hn1 hR
    _ ≤ ∑ _VB ∈ pairSet p E (sDelta (1 / 4) n) n (a * β.natDegree), b := Finset.sum_le_sum hB
    _ = (pairSet p E (sDelta (1 / 4) n) n (a * β.natDegree)).card * b := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((p ^ E : ℕ) : ℝ) ^ (n * (a * β.natDegree)) *
          (((GramSet p (p ^ E) (a * β.natDegree)).card : ℝ)⁻¹ * Zcount p E (a * β.natDegree) +
            ((p ^ E : ℕ) : ℝ) ^ ((a * β.natDegree) * ((a * β.natDegree) + 1) / 2) *
              (((p ^ E : ℕ) : ℝ) ^ ((a * β.natDegree) * ((a * β.natDegree) + 3) / 2) *
                cGram (p ^ E) (a * β.natDegree) ^ n))) * b :=
        mul_le_mul_of_nonneg_right hC hb0
    _ = _ := by
        rw [hb]
        field_simp

end ProbY

section Limit

variable {p : ℕ} [hp : Fact p.Prime]

theorem card_tor2_le_two {E : ℕ} (hE : 1 ≤ E) : Fintype.card (Tor2 (p ^ E)) ≤ 2 := by
  by_cases hp2 : p = 2
  · subst hp2
    exact (card_two_torsion_two hE).le
  · rw [card_two_torsion_odd hp2 E]; norm_num

theorem tri_add_tri (r : ℕ) : r * (r - 1) / 2 + r * (r + 1) / 2 = r * r := by
  rw [sym_dim_eq]
  have h := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self r)
  have h2 : r * (r - 1) + r = r * r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
  generalize r * (r - 1) / 2 = X at *
  generalize r * (r - 1) = Y at *
  generalize r * r = Z at *
  omega

theorem prob_Y_small {β : (ZMod p)[X]} (hd : 1 ≤ β.natDegree) {a : ℕ} (ha : 1 ≤ a) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ E0 : ℕ, ∀ E ≥ E0, ∀ᶠ n : ℕ in atTop,
      prob (fun ω : Pairs n → Bool => EventY p β a E ω) ≤ θ := by
  set r := a * β.natDegree with hrdef
  have hr1 : 1 ≤ r := Nat.mul_pos ha hd
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  set ε' : ℝ := θ / (2 * 4 ^ r * (p : ℝ) ^ (r * r)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨E1, hE1⟩ := zeroDensity p (FKr r) (FKr_ne_zero r) hε'0
  refine ⟨max E1 1, fun E hE => ?_⟩
  have hE1' : E1 ≤ E := le_of_max_le_left hE
  have hE' : 1 ≤ E := le_of_max_le_right hE
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  obtain ⟨ε, hε, hev⟩ := prob_Y_le (p := p) hd ha hE'
  obtain ⟨hc0, hc1, -⟩ := cGram_bounds (two_le_pow (p := p) hE') hr1
  have hqpow : ∀ m : ℕ, ((p ^ E : ℕ) : ℝ) ^ m = (p : ℝ) ^ (E * m) := fun m => by
    push_cast; rw [← pow_mul]
  have hZ : Zcount p E r ≤ ε' * (p : ℝ) ^ (E * (r * (r + 3) / 2 + r * (r + 1) / 2)) := by
    have h := hE1 E hE1'
    rw [Fintype.card_sum, card_GI, card_UT] at h
    exact h
  have hZ0 : 0 ≤ Zcount p E r := by rw [Zcount]; exact Nat.cast_nonneg _
  have hT0 : (0 : ℝ) < (Fintype.card (Tor2 (p ^ E)) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨(⟨0, add_zero 0⟩ : Tor2 (p ^ E))⟩
  have hT2 : (Fintype.card (Tor2 (p ^ E)) : ℝ) ≤ 2 := by exact_mod_cast card_tor2_le_two hE'
  have hA : ((antisymm r (p ^ E)).card : ℝ) =
      (p : ℝ) ^ (E * (r * (r - 1) / 2)) * (Fintype.card (Tor2 (p ^ E)) : ℝ) ^ r := by
    rw [card_antisymm]; push_cast; rw [← pow_mul]
  have hGc : ((GramSet p (p ^ E) r).card : ℝ) * (Fintype.card (Tor2 (p ^ E)) : ℝ) ^ r =
      (p : ℝ) ^ (E * (r * (r + 3) / 2)) := by
    have h1 := card_GramCoord (r := r) (q := p ^ E)
    rw [card_GI] at h1
    have h2 : (GramCoord r (p ^ E)).card * Fintype.card (Tor2 (p ^ E)) ^ r =
        (p ^ E) ^ (r * (r + 3) / 2) := by exact_mod_cast h1
    rw [card_GramSet_eq (fun w => tor2_mul_eq_zero_iff hE' w), ← hqpow]
    exact_mod_cast h2
  set T : ℝ := (Fintype.card (Tor2 (p ^ E)) : ℝ) with hTdef
  set A : ℝ := ((antisymm r (p ^ E)).card : ℝ) with hAdef
  set G : ℝ := ((GramSet p (p ^ E) r).card : ℝ)⁻¹ with hGdef
  set Z : ℝ := Zcount p E r with hZdef
  set P : ℝ := (p : ℝ) ^ ((E - 1) * (r * r)) with hPdef
  have hG : G = T ^ r / (p : ℝ) ^ (E * (r * (r + 3) / 2)) := by
    have hTr : T ^ r ≠ 0 := pow_ne_zero _ hT0.ne'
    rw [hGdef, ← hGc]
    field_simp
  have hP : 0 < P := by rw [hPdef]; positivity
  clear_value T A G Z P
  have hL : A * (G * Z) ≤ θ / 2 * P := by
    have hTr : T ^ r ≤ 2 ^ r := pow_le_pow_left₀ hT0.le hT2 r
    have hk1 : (0 : ℝ) < (p : ℝ) ^ (E * (r * (r + 3) / 2)) := by positivity
    have hpa : (0 : ℝ) ≤ (p : ℝ) ^ (E * (r * (r - 1) / 2)) := by positivity
    rw [hA, hG]
    have step1 : (p : ℝ) ^ (E * (r * (r - 1) / 2)) * T ^ r *
          (T ^ r / (p : ℝ) ^ (E * (r * (r + 3) / 2)) * Z)
        ≤ (p : ℝ) ^ (E * (r * (r - 1) / 2)) * 2 ^ r *
          (2 ^ r / (p : ℝ) ^ (E * (r * (r + 3) / 2)) *
            (ε' * (p : ℝ) ^ (E * (r * (r + 3) / 2 + r * (r + 1) / 2)))) := by
      have h1 : (p : ℝ) ^ (E * (r * (r - 1) / 2)) * T ^ r ≤
          (p : ℝ) ^ (E * (r * (r - 1) / 2)) * 2 ^ r := mul_le_mul_of_nonneg_left hTr hpa
      have h2 : T ^ r / (p : ℝ) ^ (E * (r * (r + 3) / 2)) * Z ≤
          2 ^ r / (p : ℝ) ^ (E * (r * (r + 3) / 2)) *
            (ε' * (p : ℝ) ^ (E * (r * (r + 3) / 2 + r * (r + 1) / 2))) :=
        mul_le_mul (div_le_div_of_nonneg_right hTr hk1.le) hZ hZ0 (by positivity)
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have step2 : (p : ℝ) ^ (E * (r * (r - 1) / 2)) * 2 ^ r *
          (2 ^ r / (p : ℝ) ^ (E * (r * (r + 3) / 2)) *
            (ε' * (p : ℝ) ^ (E * (r * (r + 3) / 2 + r * (r + 1) / 2)))) =
        4 ^ r * ε' * (p : ℝ) ^ (E * (r * (r - 1) / 2 + r * (r + 1) / 2)) := by
      rw [show E * (r * (r + 3) / 2 + r * (r + 1) / 2) =
          E * (r * (r + 3) / 2) + E * (r * (r + 1) / 2) from mul_add _ _ _, pow_add,
        show E * (r * (r - 1) / 2 + r * (r + 1) / 2) =
          E * (r * (r - 1) / 2) + E * (r * (r + 1) / 2) from mul_add _ _ _, pow_add,
        show (4 : ℝ) ^ r = 2 ^ r * 2 ^ r by rw [← mul_pow]; norm_num]
      field_simp
    have step3 : (p : ℝ) ^ (E * (r * (r - 1) / 2 + r * (r + 1) / 2)) =
        (p : ℝ) ^ (r * r) * P := by
      rw [tri_add_tri, hPdef, ← pow_add]
      congr 1
      rw [show E * (r * r) = ((E - 1) + 1) * (r * r) by rw [Nat.sub_add_cancel hE']]
      ring
    have step4 : (4 : ℝ) ^ r * ε' * (p : ℝ) ^ (r * r) = θ / 2 := by
      rw [hε']
      have h5 : (0 : ℝ) < 4 ^ r := by positivity
      have h6 : (0 : ℝ) < (p : ℝ) ^ (r * r) := by positivity
      field_simp
    calc (p : ℝ) ^ (E * (r * (r - 1) / 2)) * T ^ r *
          (T ^ r / (p : ℝ) ^ (E * (r * (r + 3) / 2)) * Z) ≤ _ := step1
      _ = 4 ^ r * ε' * (p : ℝ) ^ (E * (r * (r - 1) / 2 + r * (r + 1) / 2)) := step2
      _ = (4 ^ r * ε' * (p : ℝ) ^ (r * r)) * P := by rw [step3]; ring
      _ = θ / 2 * P := by rw [step4]
  have hlim : Tendsto (fun n : ℕ => (1 + |ε n|) * (A * (G * Z +
      ((p ^ E : ℕ) : ℝ) ^ (r * (r + 1) / 2) *
        (((p ^ E : ℕ) : ℝ) ^ (r * (r + 3) / 2) * cGram (p ^ E) r ^ n)))) atTop
      (𝓝 (A * (G * Z))) := by
    have h := tendsto_tight_term A (G * Z)
      (((p ^ E : ℕ) : ℝ) ^ (r * (r + 1) / 2) * ((p ^ E : ℕ) : ℝ) ^ (r * (r + 3) / 2))
      (cGram (p ^ E) r) hc0 hc1 hε
    refine h.congr fun n => ?_
    ring
  filter_upwards [hev, (tendsto_order.1 hlim).2 (A * (G * Z) + θ / 2 * P)
    (by have := mul_pos (half_pos hθ) hP; linarith)] with n h1 h2
  have h3 : prob (fun ω : Pairs n → Bool => EventY p β a E ω) * P < θ * P := by
    have := h1.trans_lt h2
    linarith
  exact le_of_lt ((mul_lt_mul_iff_left₀ hP).1 h3)

end Limit

section PropB

variable {p : ℕ} [hp : Fact p.Prime]

def EventX (p : ℕ) [Fact p.Prime] (d E : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (walkMatrix A).det ≠ 0 ∧
    ∃ β ∈ irrSet p d, ∃ y ∈ mPart A p β (latZ n), ((p : ℤ) ^ (E - 1)) • y ∉ latC A

theorem eventX_subset {n d E k : ℕ} (ω : Pairs n → Bool) (h : EventX p d E (symOf 1 0 ω)) :
    (∃ β ∈ irrSet p d, β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly) ∨ ¬ NoShort (1 / 4) n ω ∨
      ∃ β ∈ irrSet p d, ∃ a ∈ Finset.Ico 1 k, EventY p β a E ω := by
  obtain ⟨hW, β, hβ, y, hy, hyC⟩ := h
  by_cases hk : β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly
  · exact Or.inl ⟨β, hβ, hk⟩
  by_cases hN : NoShort (1 / 4) n ω
  · right; right
    obtain ⟨hβm, hβi, -⟩ := mem_irrSet_iff.1 hβ
    have hφ : (redP p (symOf 1 0 ω).charpoly).Monic := (charpoly_monic _).map _
    have hdvd : β ∣ redP p (symOf 1 0 ω).charpoly := by
      by_contra hnd
      exact hyC (Submodule.smul_mem _ _ (mem_latC_of_not_dvd hβi hnd hy))
    have hfac := mem_factorsSet_of_dvd hφ hβm hβi hdvd
    refine ⟨β, hβ, mult (redP p (symOf 1 0 ω).charpoly) β, Finset.mem_Ico.2 ⟨mult_pos hfac, ?_⟩,
      hW, hfac, rfl, hN, y, hy, hyC⟩
    by_contra hka
    push Not at hka
    apply hk
    rw [charpoly_modP_eq]
    exact (pow_dvd_pow β hka).trans (pow_mult_dvd hφ hfac)
  · exact Or.inr (Or.inl hN)

omit hp in
theorem tendsto_two_mul_add_one_div_pow (hp1 : (1 : ℝ) < p) :
    Tendsto (fun m : ℕ => (2 * (m : ℝ) + 1) / (p : ℝ) ^ m) atTop (𝓝 0) := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hp1
  have h2 : Tendsto (fun m : ℕ => ((p : ℝ)⁻¹) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
  have h3 := (h1.const_mul 2).add h2
  simp only [pow_one, mul_zero, add_zero] at h3
  refine h3.congr fun m => ?_
  rw [inv_pow]
  field_simp

theorem prop_tight_b (p : ℕ) [hp : Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) :
    ∃ E0 : ℕ, ∀ E ≥ E0, ∀ᶠ n : ℕ in atTop,
      prob (fun ω : Pairs n → Bool => EventX p d E (symOf 1 0 ω)) ≤ η := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set π := (piCount p d : ℝ) with hπ
  obtain ⟨m, hm⟩ := ((tendsto_order.1 ((tendsto_two_mul_add_one_div_pow hp1).const_mul (π + 1))).2
    (η / 4) (by simp only [mul_zero]; positivity)).exists
  set k := 2 * m with hk
  have hkm : k / 2 = m := by omega
  have hbound_k : ((k : ℝ) + 1) * π * ((p : ℝ) ^ (k / 2 * d))⁻¹ ≤ η / 4 := by
    rw [hkm]
    have h1 : (p : ℝ) ^ m ≤ (p : ℝ) ^ (m * d) :=
      pow_le_pow_right₀ hp1.le (Nat.le_mul_of_pos_right m hd)
    have h2 : (0 : ℝ) < (p : ℝ) ^ m := by positivity
    have hπ0 : 0 ≤ π := by rw [hπ]; exact Nat.cast_nonneg _
    have h3 : ((k : ℝ) + 1) * π * ((p : ℝ) ^ (m * d))⁻¹ ≤ (π + 1) * ((2 * (m : ℝ) + 1) / (p : ℝ) ^ m) := by
      rw [hk]; push_cast
      have h4 : ((p : ℝ) ^ (m * d))⁻¹ ≤ ((p : ℝ) ^ m)⁻¹ := inv_anti₀ h2 h1
      calc (2 * (m : ℝ) + 1) * π * ((p : ℝ) ^ (m * d))⁻¹
          ≤ (2 * (m : ℝ) + 1) * π * ((p : ℝ) ^ m)⁻¹ := by gcongr
        _ ≤ (2 * (m : ℝ) + 1) * (π + 1) * ((p : ℝ) ^ m)⁻¹ := by gcongr; linarith
        _ = (π + 1) * ((2 * (m : ℝ) + 1) / (p : ℝ) ^ m) := by ring
    exact h3.trans hm.le
  set I := irrSet p d ×ˢ Finset.Ico 1 k with hI
  set θ : ℝ := η / (4 * ((I.card : ℝ) + 1)) with hθ
  have hθ0 : 0 < θ := by positivity
  have hY : ∀ βa ∈ I, ∃ E0 : ℕ, ∀ E ≥ E0, ∀ᶠ n : ℕ in atTop,
      prob (fun ω : Pairs n → Bool => EventY p βa.1 βa.2 E ω) ≤ θ := by
    intro βa hβa
    rw [hI, Finset.mem_product, Finset.mem_Ico] at hβa
    have hdeg : 1 ≤ βa.1.natDegree := by rw [(mem_irrSet_iff.1 hβa.1).2.2]; exact hd
    exact prob_Y_small hdeg hβa.2.1 hθ0
  choose! E0f hE0f using hY
  refine ⟨I.sup E0f, fun E hE => ?_⟩
  have hYE : ∀ᶠ n : ℕ in atTop, ∀ βa ∈ I,
      prob (fun ω : Pairs n → Bool => EventY p βa.1 βa.2 E ω) ≤ θ := by
    rw [Filter.eventually_all_finset]
    intro βa hβa
    exact hE0f βa hβa E ((Finset.le_sup hβa).trans hE)
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) / 8)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (show (0 : ℝ) < 8 by norm_num))
    refine this.congr fun n => ?_
    simp only [Function.comp]; ring_nf
  filter_upwards [prop_tight_a p hd k (show 0 < η / 4 by positivity), hYE,
    prob_not_noShort (δ := 1 / 4) (by norm_num) le_rfl,
    (tendsto_order.1 hexp).2 (η / 4) (by positivity)] with n h1 h2 h3 h4
  have hsub : prob (fun ω : Pairs n → Bool => EventX p d E (symOf 1 0 ω)) ≤
      prob (fun ω : Pairs n → Bool => ∃ β ∈ irrSet p d, β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly) +
        (prob (fun ω : Pairs n → Bool => ¬ NoShort (1 / 4) n ω) +
          ∑ βa ∈ I, prob (fun ω : Pairs n → Bool => EventY p βa.1 βa.2 E ω)) := by
    refine (prob_mono fun ω hω => eventX_subset (k := k) ω hω).trans ((prob_or_le _ _).trans ?_)
    refine add_le_add le_rfl ((prob_or_le _ _).trans (add_le_add le_rfl ?_))
    have h5 : prob (fun ω : Pairs n → Bool =>
        ∃ β ∈ irrSet p d, ∃ a ∈ Finset.Ico 1 k, EventY p β a E ω) ≤
        prob (fun ω : Pairs n → Bool => ∃ βa ∈ I, EventY p βa.1 βa.2 E ω) :=
      prob_mono fun ω ⟨β, hβ, a, ha, hY⟩ =>
        ⟨(β, a), by rw [hI, Finset.mem_product]; exact ⟨hβ, ha⟩, hY⟩
    exact h5.trans (prob_exists_le_sum I _)
  have hsum : ∑ βa ∈ I, prob (fun ω : Pairs n → Bool => EventY p βa.1 βa.2 E ω) ≤ η / 4 := by
    calc ∑ βa ∈ I, prob (fun ω : Pairs n → Bool => EventY p βa.1 βa.2 E ω)
        ≤ ∑ _βa ∈ I, θ := Finset.sum_le_sum h2
      _ = I.card * θ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ η / 4 := by
          rw [hθ]
          have hc : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have h1' : prob (fun ω : Pairs n → Bool => ∃ β ∈ irrSet p d, β ^ k ∣ (modP p (symOf 1 0 ω)).charpoly) ≤
      η / 4 + η / 4 := by
    refine h1.trans ?_
    have := hbound_k
    rw [hπ] at this
    linarith
  linarith

end PropB

end DGS
