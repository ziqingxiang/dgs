module

public import DGS.S08_Two.Parity

@[expose] public section

open Matrix Polynomial

namespace DGS

section Res

variable {R : Type*} [CommRing R]

noncomputable def resP (F G : R[X]) : R := (F %ₘ G).coeff (G.natDegree - 1)

theorem resP_add (F₁ F₂ G : R[X]) : resP (F₁ + F₂) G = resP F₁ G + resP F₂ G := by
  rw [resP, resP, resP, add_modByMonic, coeff_add]

theorem resP_C_mul (c : R) (F G : R[X]) : resP (C c * F) G = c * resP F G := by
  rw [resP, resP, ← smul_eq_C_mul, smul_modByMonic, coeff_smul, smul_eq_mul]

theorem resP_mul_self (F : R[X]) {G : R[X]} (hG : G.Monic) : resP (F * G) G = 0 := by
  rw [resP, (modByMonic_eq_zero_iff_dvd hG).2 (dvd_mul_left _ _), coeff_zero]

theorem resP_map {S : Type*} [CommRing S] [Nontrivial S] (f : R →+* S) (F : R[X]) {G : R[X]}
    (hG : G.Monic) : f (resP F G) = resP (F.map f) (G.map f) := by
  rw [resP, resP, ← coeff_map, map_modByMonic f hG, hG.natDegree_map]

variable [IsDomain R]

theorem resP_X (g : R[X]) : resP g X = g.coeff 0 := by
  rw [resP, modByMonic_X, natDegree_X, coeff_C_zero, coeff_zero_eq_eval_zero]

theorem resP_mul_right (F : R[X]) {G H : R[X]} (hG : G.Monic) (hH : H.Monic)
    (hG1 : 1 ≤ G.natDegree) : resP (F * H) (G * H) = resP F G := by
  have hG1' : G ≠ 1 := by rintro rfl; simp at hG1
  have hlt := natDegree_modByMonic_lt F hG hG1'
  have hdecomp : F %ₘ G * H + G * H * (F /ₘ G) = F * H := by
    have h1 := modByMonic_add_div F G
    calc F %ₘ G * H + G * H * (F /ₘ G) = (F %ₘ G + G * (F /ₘ G)) * H := by ring
      _ = F * H := by rw [h1]
  have hdeg : degree (F %ₘ G * H) < degree (G * H) := by
    by_cases hr0 : F %ₘ G = 0
    · rw [hr0, zero_mul, degree_zero]
      exact bot_lt_iff_ne_bot.2 (fun h => (hG.mul hH).ne_zero (degree_eq_bot.1 h))
    · apply degree_lt_degree
      rw [natDegree_mul hr0 hH.ne_zero, natDegree_mul hG.ne_zero hH.ne_zero]
      omega
  have hmod : (F * H) %ₘ (G * H) = F %ₘ G * H :=
    (div_modByMonic_unique (F /ₘ G) (F %ₘ G * H) (hG.mul hH) ⟨hdecomp, hdeg⟩).2
  rw [resP, resP, hmod, natDegree_mul hG.ne_zero hH.ne_zero,
    show G.natDegree + H.natDegree - 1 = (G.natDegree - 1) + H.natDegree by omega,
    coeff_mul_add_eq_of_natDegree_le (by omega) le_rfl, hH.coeff_natDegree, mul_one]

end Res

section Omega

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

noncomputable def hNum : ℤ[X] :=
  X ^ (n % 2) * psiPoly A - C ((n % 2 * n : ℕ) : ℤ) * A.charpoly

open Classical in
noncomputable def hPoly : ℤ[X] := if h : C (2 : ℤ) ∣ hNum A then h.choose else 0

noncomputable def gamo : (ZMod 2)[X] := X ^ (n % 2) * gam A

noncomputable def omegaF (f : (ZMod 2)[X]) : ZMod 2 :=
  (((ones n ℤ ⬝ᵥ (aeval A (liftZ 2 f) *ᵥ ones n ℤ) -
    ((n % 2 * n : ℕ) : ℤ) * (liftZ 2 f).coeff 0) / 2 : ℤ) : ZMod 2)

variable {A} (hA : A.IsSymm) (hd : ∀ i, A i i = 0)
include hA hd

theorem gamo_monic : (gamo A).Monic := (monic_X_pow _).mul (gam_monic hA hd)

theorem gamo_sq : gamo A ^ 2 = redP 2 A.charpoly * X ^ (n % 2) := by
  rw [gamo, redP_charpoly_eq hA hd]
  ring

theorem map_hNum : (hNum A).map (Int.castRingHom (ZMod 2)) = 0 := by
  rw [hNum, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h, pow_zero, one_mul, zero_mul, Nat.cast_zero, map_zero, C_0, zero_mul, sub_zero]
    exact psi_mod2_even hA hd h
  · rw [h, pow_one, one_mul, eq_intCast, Int.cast_natCast, map_natCast C]
    rw [X_mul_psi_mod2 hA hd, sub_self]

theorem C_two_mul_hPoly : C (2 : ℤ) * hPoly A = hNum A := by
  have h : C (2 : ℤ) ∣ hNum A := by
    have := (map_eq_zero_iff_C_dvd 2 (hNum A)).1 (map_hNum hA hd)
    simpa using this
  rw [hPoly, dite_eq_left h]
  exact h.choose_spec.symm

theorem C_two_mul_hPoly_mem : C (2 : ℤ) * hPoly A ∈ idealT A := by
  rw [C_two_mul_hPoly hA hd, hNum, idealT, Ideal.mem_span_pair]
  exact ⟨-C ((n % 2 * n : ℕ) : ℤ), X ^ (n % 2), by ring⟩

variable (hn : 1 ≤ n)
include hn

theorem walk_eq_resP (g : ℤ[X]) :
    ones n ℤ ⬝ᵥ (aeval A g *ᵥ ones n ℤ) - ((n % 2 * n : ℕ) : ℤ) * g.coeff 0 =
      2 * resP (g * hPoly A) (A.charpoly * X ^ (n % 2)) := by
  have hφ := charpoly_monic A
  have hφdeg : A.charpoly.natDegree = n := by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  have h1 : ones n ℤ ⬝ᵥ (aeval A g *ᵥ ones n ℤ) = resP (g * psiPoly A) A.charpoly := by
    rw [ones_dot_aeval_eq_tauF A hn, tauF, resP, hφdeg]
  rw [h1, ← resP_mul_right (g * psiPoly A) hφ (monic_X_pow _) (by omega)]
  have h2 : g * psiPoly A * X ^ (n % 2) =
      C 2 * (g * hPoly A) + C ((n % 2 * n : ℕ) : ℤ) * (g * A.charpoly) := by
    have := C_two_mul_hPoly hA hd
    rw [hNum] at this
    linear_combination (-g) * this
  rw [h2, resP_add, resP_C_mul, resP_C_mul]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h]; simp
  · rw [h, pow_one, mul_comm A.charpoly X, resP_mul_right g monic_X hφ (by simp), resP_X]
    ring

theorem omegaF_eq_resP (f : (ZMod 2)[X]) :
    omegaF A f = resP (f * redP 2 (hPoly A)) (gamo A ^ 2) := by
  rw [omegaF, walk_eq_resP hA hd hn (liftZ 2 f), Int.mul_ediv_cancel_left _ two_ne_zero,
    ← eq_intCast (Int.castRingHom (ZMod 2)),
    resP_map _ _ ((charpoly_monic A).mul (monic_X_pow _)), Polynomial.map_mul, map_liftZ,
    Polynomial.map_mul, Polynomial.map_pow, map_X, gamo_sq hA hd]

theorem omegaF_eq_of_lift (g : ℤ[X]) :
    omegaF A (g.map (Int.castRingHom (ZMod 2))) =
      (((ones n ℤ ⬝ᵥ (aeval A g *ᵥ ones n ℤ) - ((n % 2 * n : ℕ) : ℤ) * g.coeff 0) / 2 : ℤ) :
        ZMod 2) := by
  rw [omegaF_eq_resP hA hd hn, walk_eq_resP hA hd hn g, Int.mul_ediv_cancel_left _ two_ne_zero,
    ← eq_intCast (Int.castRingHom (ZMod 2)),
    resP_map _ _ ((charpoly_monic A).mul (monic_X_pow _)), Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_pow, map_X, gamo_sq hA hd]

theorem omegaF_add (f₁ f₂ : (ZMod 2)[X]) : omegaF A (f₁ + f₂) = omegaF A f₁ + omegaF A f₂ := by
  rw [omegaF_eq_resP hA hd hn, omegaF_eq_resP hA hd hn, omegaF_eq_resP hA hd hn, add_mul, resP_add]

theorem omegaF_zero : omegaF A 0 = 0 := by
  rw [omegaF_eq_resP hA hd hn, zero_mul, resP, zero_modByMonic, coeff_zero]

end Omega

theorem map_C_two : (C (2 : ℤ)).map (Int.castRingHom (ZMod 2)) = 0 := by
  rw [map_C]
  have : (Int.castRingHom (ZMod 2)) 2 = 0 := rfl
  rw [this, C_0]

theorem C_two_mul_not_mem_sq {β : (ZMod 2)[X]} (hβ : β ≠ 0) {h : ℤ[X]} (hh : h ∉ idealM 2 β) :
    C (2 : ℤ) * h ∉ idealM 2 β ^ 2 := by
  intro hmem
  set b := liftZ 2 β with hb
  have h2m : C (2 : ℤ) ∈ idealM 2 β := by
    have : C ((2 : ℕ) : ℤ) ∈ idealM 2 β := Ideal.subset_span (Set.mem_insert _ _)
    simpa using this
  have hbm : b ∈ idealM 2 β := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hle : idealM 2 β ^ 2 ≤ Ideal.span {C (2 : ℤ)} * idealM 2 β ⊔ Ideal.span {b ^ 2} := by
    rw [sq, Ideal.mul_le]
    intro r hr s hs
    obtain ⟨r1, r2, hr'⟩ := Ideal.mem_span_pair.1 hr
    obtain ⟨s1, s2, hs'⟩ := Ideal.mem_span_pair.1 hs
    simp only [Nat.cast_ofNat] at hr' hs'
    have e : r * s = C (2 : ℤ) * (r1 * s + r2 * s1 * b) + b ^ 2 * (r2 * s2) := by
      linear_combination (-s) * hr' + (-(r2 * b)) * hs'
    rw [e]
    refine Submodule.add_mem_sup ?_ ?_
    · exact Ideal.mem_span_singleton_mul.2
        ⟨_, add_mem (Ideal.mul_mem_left _ _ hs) (Ideal.mul_mem_left _ _ hbm), rfl⟩
    · exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hle hmem)
  obtain ⟨u, hu, rfl⟩ := Ideal.mem_span_singleton_mul.1 hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hc : C ((2 : ℕ) : ℤ) ∣ c := by
    rw [← map_eq_zero_iff_C_dvd]
    have := congrArg (Polynomial.map (Int.castRingHom (ZMod 2))) hyz
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, map_C_two,
      zero_mul, zero_mul, zero_add, Polynomial.map_pow, hb, map_liftZ] at this
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ hβ)
  obtain ⟨c', rfl⟩ := hc
  simp only [Nat.cast_ofNat] at hyz
  have h2 : h = u + c' * b ^ 2 := by
    apply mul_left_cancel₀ (C_ne_zero.2 (two_ne_zero : (2 : ℤ) ≠ 0))
    rw [← hyz]
    ring
  apply hh
  rw [h2]
  exact add_mem hu (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hbm 2 two_pos))

section WangLC

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hd : ∀ i, A i i = 0) (hn : 1 ≤ n)
  (hW : (walkMatrix A).det ≠ 0)
include hA hd hn hW

theorem lem_wangLC {β : (ZMod 2)[X]} (hβm : β.Monic) (hβ : Irreducible β) (hβγ : β ∣ gam A)
    {c : (ZMod 2)[X]} (hc : c * β = gamo A ^ 2) (hω : ∃ t, omegaF A (c * t) ≠ 0) :
    IsChainComponent A 2 β ∧ ∀ Q : Matrix (Fin n) (Fin n) ℚ, IsMateMatrix A Q → β ∉ Fset A Q 2 := by
  have hβf := mem_factorsSet_of_dvd_gam hA hd hβm hβ hβγ
  have hh : hPoly A ∉ idealM 2 β := by
    intro hm
    rw [mem_idealM_iff] at hm
    obtain ⟨h', hh'⟩ := hm
    obtain ⟨t, ht⟩ := hω
    apply ht
    rw [omegaF_eq_resP hA hd hn]
    have : c * t * redP 2 (hPoly A) = t * h' * gamo A ^ 2 := by
      change c * t * (hPoly A).map (Int.castRingHom (ZMod 2)) = _
      rw [hh', ← hc]; ring
    rw [this, resP_mul_self _ ((gamo_monic hA hd).pow 2)]
  obtain ⟨t, ht⟩ := cor_chain_b hA hn hW hβf
    ⟨_, C_two_mul_hPoly_mem hA hd, C_two_mul_not_mem_sq hβ.ne_zero hh⟩
  exact cor_chain_a hA hn hW hβf ht

end WangLC

end DGS
