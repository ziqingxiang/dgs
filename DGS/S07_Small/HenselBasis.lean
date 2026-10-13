module

public import DGS.S07_Small.PrimaryDim
public import DGS.S07_Small.KrylovPoly

@[expose] public section

open Matrix Polynomial Module

namespace DGS

section Red

variable {p : ℕ} [hp : Fact p.Prime] {E : ℕ}

theorem isUnit_of_redE_ne_zero (hE : 1 ≤ E) {x : ZMod (p ^ E)} (hx : redE p E hE x ≠ 0) :
    IsUnit x := by
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  have h1 : redE p E hE x = ((x.val : ℕ) : ZMod p) := by
    rw [redE, ZMod.castHom_apply, ZMod.natCast_val]
  rw [h1, Ne, ZMod.natCast_eq_zero_iff] at hx
  have hcop : Nat.Coprime x.val (p ^ E) :=
    Nat.Coprime.pow_right E ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hx).symm
  rw [← ZMod.natCast_zmod_val x]
  exact (ZMod.isUnit_iff_coprime _ _).2 hcop

omit hp in
theorem redE_surjective (hE : 1 ≤ E) : Function.Surjective (redE p E hE) :=
  ZMod.castHom_surjective _

theorem card_fiber_one (hE : 1 ≤ E) (r : ℕ) :
    (Finset.univ.filter fun g : Matrix (Fin r) (Fin r) (ZMod (p ^ E)) =>
      g.map (redE p E hE) = 1).card = p ^ ((E - 1) * (r * r)) := by
  classical
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  set ρ : Matrix (Fin r) (Fin r) (ZMod (p ^ E)) →+ Matrix (Fin r) (Fin r) (ZMod p) :=
    ((redE p E hE).mapMatrix : Matrix (Fin r) (Fin r) (ZMod (p ^ E)) →+* _).toAddMonoidHom with hρ
  have hρapp : ∀ g, ρ g = g.map (redE p E hE) := fun g => rfl
  have hsurj : Function.Surjective ρ := by
    intro M
    choose lift hlift using redE_surjective (p := p) hE
    exact ⟨M.map lift, by rw [hρapp, Matrix.map_map]; ext i j; exact hlift _⟩
  have hfib : ∀ y, (Finset.univ.filter fun g => ρ g = y).card =
      (Finset.univ.filter fun g => ρ g = 1).card := fun y =>
    AddMonoidHom.card_fiber_eq_of_mem_range ρ (hsurj y) (hsurj 1)
  have htot : (Finset.univ : Finset (Matrix (Fin r) (Fin r) (ZMod (p ^ E)))).card =
      ∑ y : Matrix (Fin r) (Fin r) (ZMod p), (Finset.univ.filter fun g => ρ g = y).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  simp_rw [hfib] at htot
  rw [Finset.sum_const, Finset.card_univ, Finset.card_univ, smul_eq_mul] at htot
  have hc1 : Fintype.card (Matrix (Fin r) (Fin r) (ZMod (p ^ E))) = p ^ (E * (r * r)) := by
    rw [show Fintype.card (Matrix (Fin r) (Fin r) (ZMod (p ^ E))) =
      Fintype.card (Fin r → Fin r → ZMod (p ^ E)) from rfl, Fintype.card_fun, Fintype.card_fun,
      ZMod.card, Fintype.card_fin]
    ring
  have hc2 : Fintype.card (Matrix (Fin r) (Fin r) (ZMod p)) = p ^ (r * r) := by
    rw [show Fintype.card (Matrix (Fin r) (Fin r) (ZMod p)) =
      Fintype.card (Fin r → Fin r → ZMod p) from rfl, Fintype.card_fun, Fintype.card_fun,
      ZMod.card, Fintype.card_fin]
    ring
  rw [hc1, hc2] at htot
  have hE' : E * (r * r) = (E - 1) * (r * r) + r * r := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hE]
  rw [hE', pow_add, mul_comm] at htot
  have hpos : 0 < p ^ (r * r) := pow_pos hp.out.pos _
  have : (Finset.univ.filter fun g => ρ g = 1).card = p ^ ((E - 1) * (r * r)) :=
    (Nat.eq_of_mul_eq_mul_left hpos htot).symm
  rw [← this]
  rfl

end Red

section Basis

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} {p : ℕ} [hp : Fact p.Prime] {β : (ZMod p)[X]}
  {E : ℕ}

variable (A p β) in
noncomputable def kerBar : Submodule (ZMod p) (Fin n → ZMod p) :=
  LinearMap.ker (Matrix.toLin' (aeval (modP p A) (β ^ mult (redP p A.charpoly) β)))

theorem mem_kerBar {v : Fin n → ZMod p} :
    v ∈ kerBar A p β ↔ aeval (modP p A) (β ^ mult (redP p A.charpoly) β) *ᵥ v = 0 := by
  rw [kerBar, LinearMap.mem_ker, Matrix.toLin'_apply]

omit hp in
theorem charpoly_modP_eq : (modP p A).charpoly = redP p A.charpoly := by
  rw [modP, Matrix.charpoly_map]

theorem finrank_kerBar (hβ : β ∈ factorsSet (redP p A.charpoly)) :
    finrank (ZMod p) (kerBar A p β) = mult (redP p A.charpoly) β * β.natDegree := by
  have hφ : (redP p A.charpoly).Monic := (charpoly_monic A).map _
  have h := finrank_ker_eq_of_exact (modP p A) (irreducible_of_mem_factorsSet hβ)
    (by rw [charpoly_modP_eq]; exact pow_mult_dvd hφ hβ)
    (by rw [charpoly_modP_eq]; exact not_pow_succ_mult_dvd hφ hβ)
  have he : kerBar A p β =
      LinearMap.ker (aeval (Matrix.toLin' (modP p A)) (β ^ mult (redP p A.charpoly) β)) := by
    ext z
    rw [mem_kerBar, LinearMap.mem_ker, aeval_toLin'_apply]
  rw [he, h]

variable (hβ : β ∈ factorsSet (redP p A.charpoly)) {r : ℕ}
  (hr : mult (redP p A.charpoly) β * β.natDegree = r) (hE : 1 ≤ E)

noncomputable def kBasis :
    Basis (Fin r) (ZMod p) (kerBar A p β) :=
  Module.finBasisOfFinrankEq _ _ ((finrank_kerBar hβ).trans hr)

theorem exists_lift (i : Fin r) :
    ∃ x ∈ NE A p β E, redVecE hE x = ((kBasis hβ hr i : kerBar A p β) : Fin n → ZMod p) :=
  (reduction_NE hβ hE).2 _ (mem_kerBar.1 (kBasis hβ hr i).2)

noncomputable def V0 : Matrix (Fin n) (Fin r)
    (ZMod (p ^ E)) :=
  Matrix.of fun k i => (exists_lift hβ hr hE i).choose k

theorem V0_col_mem (i : Fin r) :
    (fun k => V0 hβ hr hE k i) ∈ NE A p β E :=
  (exists_lift hβ hr hE i).choose_spec.1

theorem V0_map (k : Fin n) (i : Fin r) :
    (V0 hβ hr hE).map (redE p E hE) k i = ((kBasis hβ hr i : kerBar A p β) : Fin n → ZMod p) k := by
  have h := congrFun (exists_lift hβ hr hE i).choose_spec.2 k
  rw [Matrix.map_apply]
  exact h

theorem V0_map_mulVec (c : Fin r → ZMod p) :
    (V0 hβ hr hE).map (redE p E hE) *ᵥ c =
      ((∑ i, c i • kBasis hβ hr i : kerBar A p β) : Fin n → ZMod p) := by
  funext k
  simp only [mulVec, dotProduct, V0_map, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem V0_map_mulVec_mem (c : Fin r → ZMod p) :
    (V0 hβ hr hE).map (redE p E hE) *ᵥ c ∈ kerBar A p β := by
  rw [V0_map_mulVec]
  exact Submodule.coe_mem _

theorem V0_map_mulVec_ne_zero {c : Fin r → ZMod p}
    (hc : c ≠ 0) : (V0 hβ hr hE).map (redE p E hE) *ᵥ c ≠ 0 := by
  rw [V0_map_mulVec]
  intro h0
  apply hc
  have h1 : (∑ i, c i • kBasis hβ hr i : kerBar A p β) = 0 := Subtype.ext h0
  exact (Fintype.linearIndependent_iff.1 (kBasis hβ hr).linearIndependent) c h1 |> funext

theorem det_gram_V0_map_ne_zero (hA : A.IsSymm) :
    (((V0 hβ hr hE).map (redE p E hE))ᵀ * (V0 hβ hr hE).map (redE p E hE)).det ≠ 0 := by
  set Vb := (V0 hβ hr hE).map (redE p E hE) with hVb
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  set u := Vb *ᵥ c with hu
  have huK : u ∈ kerBar A p β := V0_map_mulVec_mem hβ hr hE c
  have hbj : ∀ j, u ⬝ᵥ ((kBasis hβ hr j : kerBar A p β) : Fin n → ZMod p) = 0 := by
    intro j
    have h1 := congrFun hc j
    rw [← mulVec_mulVec, Pi.zero_apply] at h1
    rw [← h1, dotProduct_comm, hu]
    simp only [mulVec, dotProduct, transpose_apply, hVb, V0_map]
  have horth : ∀ v : Fin n → ZMod p,
      aeval (modP p A) (β ^ mult (redP p A.charpoly) β) *ᵥ v = 0 → u ⬝ᵥ v = 0 := by
    intro v hv
    have hvK : v ∈ kerBar A p β := mem_kerBar.2 hv
    have hsum := (kBasis hβ hr).sum_repr ⟨v, hvK⟩
    have hv' : v = ∑ j, ((kBasis hβ hr).repr ⟨v, hvK⟩ j) • ((kBasis hβ hr j : kerBar A p β) :
        Fin n → ZMod p) := by
      have := congrArg Subtype.val hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hv', dotProduct_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [dotProduct_smul, hbj j, smul_zero]
  have hu0 : u = 0 := dot_nondegenerate_ker hβ hA hE (mem_kerBar.1 huK) horth
  exact V0_map_mulVec_ne_zero hβ hr hE hc0 hu0

theorem isUnit_det_gram (hA : A.IsSymm)
    {V : Matrix (Fin n) (Fin r) (ZMod (p ^ E))}
    (hV : V.map (redE p E hE) = (V0 hβ hr hE).map (redE p E hE)) : IsUnit (Vᵀ * V).det := by
  apply isUnit_of_redE_ne_zero hE
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map, hV]
  exact det_gram_V0_map_ne_zero hβ hr hE hA

theorem mulVec_mem_NE {r : ℕ} {V : Matrix (Fin n) (Fin r) (ZMod (p ^ E))}
    (hV : ∀ i, (fun k => V k i) ∈ NE A p β E) (c : Fin r → ZMod (p ^ E)) :
    V *ᵥ c ∈ NE A p β E := by
  have h : V *ᵥ c = ∑ i, c i • (fun k => V k i) := by
    funext k
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hV i)

theorem V0_span {x : Fin n → ZMod (p ^ E)} (hx : x ∈ NE A p β E) :
    ∃ c, x = V0 hβ hr hE *ᵥ c := by
  have : NeZero (p ^ E) := ⟨pow_ne_zero E hp.out.ne_zero⟩
  have key : ∀ j : ℕ, ∃ c : Fin r → ZMod (p ^ E),
      ∃ y ∈ NE A p β E, x = V0 hβ hr hE *ᵥ c + ((p : ZMod (p ^ E)) ^ j) • y := by
    intro j
    induction j with
    | zero => exact ⟨0, x, hx, by simp⟩
    | succ j ih =>
      obtain ⟨c, y, hy, hxy⟩ := ih
      have hyK : redVecE hE y ∈ kerBar A p β := mem_kerBar.2 ((reduction_NE hβ hE).1 y hy)
      set e := (kBasis hβ hr).repr ⟨redVecE hE y, hyK⟩ with he
      choose lift hlift using redE_surjective (p := p) hE
      set e' : Fin r → ZMod (p ^ E) :=
        fun i => lift (e i) with he'
      have hred : redVecE hE (y - V0 hβ hr hE *ᵥ e') = 0 := by
        have h1 : redVecE hE (V0 hβ hr hE *ᵥ e') = redVecE hE y := by
          funext k
          have h2 : redVecE hE (V0 hβ hr hE *ᵥ e') k = ((V0 hβ hr hE).map (redE p E hE) *ᵥ e) k := by
            simp only [redVecE, mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, he',
              hlift]
          rw [h2, V0_map_mulVec]
          have h3 := (kBasis hβ hr).sum_repr ⟨redVecE hE y, hyK⟩
          rw [← he] at h3
          exact congrFun (congrArg Subtype.val h3) k
        funext k
        have : redVecE hE (y - V0 hβ hr hE *ᵥ e') k = redVecE hE y k - redVecE hE (V0 hβ hr hE *ᵥ e') k := by
          simp [redVecE]
        rw [this, h1, sub_self, Pi.zero_apply]
      have hz : ∀ k, ∃ w : ZMod (p ^ E), (y - V0 hβ hr hE *ᵥ e') k = (p : ZMod (p ^ E)) * w := by
        intro k
        apply exists_eq_p_mul_of_cast_eq_zero hE
        have := congrFun hred k
        rw [redVecE, redE, ZMod.castHom_apply] at this
        exact this
      choose z hz using hz
      set z' := piQ A p β E (p ^ E) *ᵥ z with hz'
      have hmem : y - V0 hβ hr hE *ᵥ e' ∈ NE A p β E :=
        sub_mem hy (mulVec_mem_NE (V0_col_mem hβ hr hE) e')
      have hpz : y - V0 hβ hr hE *ᵥ e' = (p : ZMod (p ^ E)) • z' := by
        have h1 : y - V0 hβ hr hE *ᵥ e' = (p : ZMod (p ^ E)) • z := by
          funext k; rw [hz k]; rfl
        rw [hz', ← mulVec_smul, ← h1]
        exact ((mem_NE_iff hβ).1 hmem).symm
      refine ⟨c + ((p : ZMod (p ^ E)) ^ j) • e', z', piQ_mulVec_mem_NE _, ?_⟩
      have hy' : y = V0 hβ hr hE *ᵥ e' + (p : ZMod (p ^ E)) • z' := by
        rw [← hpz]; abel
      rw [hxy, hy', mulVec_add, mulVec_smul, smul_add, smul_smul, ← pow_succ]
      abel
  obtain ⟨c, y, -, hxy⟩ := key E
  refine ⟨c, ?_⟩
  have hpE : (p : ZMod (p ^ E)) ^ E = 0 := by exact_mod_cast ZMod.natCast_self (p ^ E)
  rw [hxy, hpE, zero_smul, add_zero]

theorem hbasis_mul
    {g : Matrix (Fin r)
      (Fin r) (ZMod (p ^ E))}
    (hg : g.map (redE p E hE) = 1) :
    (∀ i, (fun k => (V0 hβ hr hE * g) k i) ∈ NE A p β E) ∧
      (∀ x ∈ NE A p β E, ∃ c, x = (V0 hβ hr hE * g) *ᵥ c) ∧
      (V0 hβ hr hE * g).map (redE p E hE) = (V0 hβ hr hE).map (redE p E hE) := by
  have hgu : IsUnit g.det := by
    apply isUnit_of_redE_ne_zero hE
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hg, det_one]
    exact one_ne_zero
  refine ⟨fun i => ?_, fun x hx => ?_, ?_⟩
  · have : (fun k => (V0 hβ hr hE * g) k i) = V0 hβ hr hE *ᵥ (fun l => g l i) := by
      funext k; simp [Matrix.mul_apply, mulVec, dotProduct]
    rw [this]
    exact mulVec_mem_NE (V0_col_mem hβ hr hE) _
  · obtain ⟨c, rfl⟩ := V0_span hβ hr hE hx
    refine ⟨g⁻¹ *ᵥ c, ?_⟩
    rw [mulVec_mulVec, Matrix.mul_assoc, mul_nonsing_inv _ hgu, Matrix.mul_one]
  · rw [Matrix.map_mul, hg, Matrix.mul_one]

end Basis

end DGS
