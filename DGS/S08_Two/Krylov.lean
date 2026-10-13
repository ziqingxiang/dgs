module

public import DGS.S08_Two.Quadratic
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

open Matrix Polynomial Module

namespace DGS

section Orth

variable {F : Type*} [Field F] {n : ℕ}

def orthC (W : Submodule F (Fin n → F)) : Submodule F (Fin n → F) where
  carrier := {y | ∀ w ∈ W, w ⬝ᵥ y = 0}
  add_mem' := by
    intro y z hy hz w hw
    rw [dotProduct_add, hy w hw, hz w hw, add_zero]
  zero_mem' := by intro w _; exact dotProduct_zero w
  smul_mem' := by
    intro c y hy w hw
    rw [dotProduct_smul, hy w hw, smul_zero]

theorem mem_orthC {W : Submodule F (Fin n → F)} {y : Fin n → F} :
    y ∈ orthC W ↔ ∀ w ∈ W, w ⬝ᵥ y = 0 := Iff.rfl

theorem orthC_eq_comap (W : Submodule F (Fin n → F)) :
    orthC W = W.dualAnnihilator.comap (dotProductEquiv F (Fin n)).toLinearMap := by
  ext y
  rw [mem_orthC, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  refine forall₂_congr fun w _ => ?_
  rw [LinearEquiv.coe_coe, dotProductEquiv_apply_apply, dotProduct_comm]

theorem finrank_orthC_add (W : Submodule F (Fin n → F)) :
    finrank F W + finrank F (orthC W) = n := by
  rw [orthC_eq_comap, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    Subspace.finrank_add_finrank_dualAnnihilator_eq, Module.finrank_fin_fun]

theorem le_orthC_orthC (W : Submodule F (Fin n → F)) : W ≤ orthC (orthC W) :=
  fun w hw y hy => by rw [dotProduct_comm]; exact hy w hw

theorem orthC_orthC (W : Submodule F (Fin n → F)) : orthC (orthC W) = W := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (le_orthC_orthC W)
  have h1 := finrank_orthC_add W
  have h2 := finrank_orthC_add (orthC W)
  omega

theorem orthC_anti {W W' : Submodule F (Fin n → F)} (h : W ≤ W') : orthC W' ≤ orthC W :=
  fun _ hy w hw => hy w (h hw)

end Orth

section Cyclic

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
  (v : Fin n → F)

noncomputable def evalVec : F[X] →ₗ[F] (Fin n → F) where
  toFun g := aeval M g *ᵥ v
  map_add' g h := by rw [map_add, add_mulVec]
  map_smul' c g := by rw [map_smul, smul_mulVec, RingHom.id_apply]

omit [DecidableEq F] in
theorem evalVec_apply (g : F[X]) : evalVec M v g = aeval M g *ᵥ v := rfl

noncomputable def cyc : Submodule F (Fin n → F) := LinearMap.range (evalVec M v)

variable {M v} in
omit [DecidableEq F] in
theorem mem_cyc {y : Fin n → F} : y ∈ cyc M v ↔ ∃ g : F[X], aeval M g *ᵥ v = y := Iff.rfl

omit [DecidableEq F] in
theorem aeval_mulVec_mem_cyc (g : F[X]) : aeval M g *ᵥ v ∈ cyc M v := ⟨g, rfl⟩

omit [DecidableEq F] in
theorem self_mem_cyc : v ∈ cyc M v := ⟨1, by rw [evalVec_apply, map_one, one_mulVec]⟩

variable {M v} in
omit [DecidableEq F] in
theorem mulVec_mem_cyc {y : Fin n → F} (hy : y ∈ cyc M v) : M *ᵥ y ∈ cyc M v := by
  obtain ⟨g, rfl⟩ := hy
  exact ⟨X * g, by rw [evalVec_apply, evalVec_apply, map_mul, aeval_X, ← mulVec_mulVec]⟩

noncomputable def annF : Ideal F[X] where
  carrier := {g | aeval M g *ᵥ v = 0}
  add_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, add_mulVec, hg, hh, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c g hg
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    rw [map_mul, ← mulVec_mulVec, hg, mulVec_zero]

noncomputable def muVec : F[X] := normalize (Submodule.IsPrincipal.generator (annF M v))

theorem annF_eq_span : annF M v = Ideal.span {muVec M v} := by
  rw [muVec, Ideal.span_singleton_eq_span_singleton.2 (normalize_associated _)]
  exact (Ideal.span_singleton_generator (annF M v)).symm

theorem muVec_dvd_iff {g : F[X]} : muVec M v ∣ g ↔ aeval M g *ᵥ v = 0 := by
  rw [← Ideal.mem_span_singleton, ← annF_eq_span]
  rfl

theorem aeval_muVec : aeval M (muVec M v) *ᵥ v = 0 := (muVec_dvd_iff M v).1 dvd_rfl

theorem muVec_ne_zero : muVec M v ≠ 0 := by
  intro h
  have := (muVec_dvd_iff M v).2 (by rw [aeval_self_charpoly, zero_mulVec])
  rw [h, zero_dvd_iff] at this
  exact M.charpoly_monic.ne_zero this

theorem muVec_monic : (muVec M v).Monic := by
  have hg : Submodule.IsPrincipal.generator (annF M v) ≠ 0 := by
    intro h; apply muVec_ne_zero M v; rw [muVec, h, normalize_zero]
  rw [muVec]
  convert Polynomial.monic_normalize hg

theorem muVec_eq_of {r : F[X]} (hr : r.Monic) (h : ∀ g, aeval M g *ᵥ v = 0 ↔ r ∣ g) :
    muVec M v = r := by
  have h1 : muVec M v ∣ r := (muVec_dvd_iff M v).2 ((h r).2 dvd_rfl)
  have h2 : r ∣ muVec M v := (h _).1 (aeval_muVec M v)
  exact eq_of_monic_of_associated (muVec_monic M v) hr (associated_of_dvd_dvd h1 h2)

theorem muVec_aeval {q r : F[X]} (hr : r.Monic) (hqr : q * r = muVec M v) :
    muVec M (aeval M q *ᵥ v) = r := by
  have hq : q ≠ 0 := by
    rintro rfl; rw [zero_mul] at hqr; exact muVec_ne_zero M v hqr.symm
  apply muVec_eq_of M _ hr
  intro g
  rw [mulVec_mulVec, ← map_mul, ← muVec_dvd_iff, ← hqr, mul_comm g q]
  exact mul_dvd_mul_iff_left hq

theorem finrank_cyc : finrank F (cyc M v) = (muVec M v).natDegree := by
  set d := (muVec M v).natDegree with hd
  set L := (evalVec M v).comp (Polynomial.degreeLT F d).subtype with hL
  have hμ := muVec_monic M v
  have hrange : LinearMap.range L = cyc M v := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      exact ⟨g.1, rfl⟩
    · rintro _ ⟨g, rfl⟩
      refine ⟨⟨g %ₘ muVec M v, ?_⟩, ?_⟩
      · rw [Polynomial.mem_degreeLT, hd, ← degree_eq_natDegree hμ.ne_zero]
        exact degree_modByMonic_lt _ hμ
      · show aeval M (g %ₘ muVec M v) *ᵥ v = aeval M g *ᵥ v
        conv_rhs => rw [← modByMonic_add_div g (muVec M v)]
        rw [map_add, add_mulVec, mul_comm (muVec M v), map_mul, ← mulVec_mulVec, aeval_muVec,
          mulVec_zero, add_zero]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨g, hg⟩ h0
    have h1 : aeval M g *ᵥ v = 0 := h0
    have h2 := (muVec_dvd_iff M v).2 h1
    rw [Polynomial.mem_degreeLT, hd, ← degree_eq_natDegree hμ.ne_zero] at hg
    have := eq_zero_of_dvd_of_degree_lt h2 hg
    exact Subtype.ext this
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, (Polynomial.degreeLTEquiv F d).finrank_eq,
    Module.finrank_fin_fun]

end Cyclic

section Isotropic

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {M : Matrix (Fin n) (Fin n) F}

omit [DecidableEq F] in
theorem aeval_transpose_of_symm (hM : Mᵀ = M) (g : F[X]) : (aeval M g)ᵀ = aeval M g := by
  rw [aeval_eq_sum_range, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.transpose_smul, Matrix.transpose_pow, hM]

theorem pow_two_mul_dvd_charpoly (hM : Mᵀ = M) {β : F[X]} (hβ : Irreducible β) {c : ℕ}
    {w : Fin n → F} (hw : muVec M w = β ^ c)
    (hiso : ∀ y ∈ cyc M w, ∀ z ∈ cyc M w, y ⬝ᵥ z = 0) : β ^ (2 * c) ∣ M.charpoly := by
  by_contra hndvd
  have hc : 1 ≤ c := by
    by_contra h0
    push Not at h0
    interval_cases c
    exact hndvd (by rw [mul_zero, pow_zero]; exact one_dvd _)
  set f := Matrix.toLin' M with hf
  set T := aeval f β with hT
  obtain ⟨m, hm, hmc⟩ :=
    ((T.eventually_isCompl_ker_pow_range_pow).and (Filter.eventually_ge_atTop c)).exists
  set P := LinearMap.ker (T ^ m) with hP
  set Q := LinearMap.range (T ^ m) with hQ
  have hTm : ∀ z, (T ^ m) z = aeval M (β ^ m) *ᵥ z := by
    intro z
    rw [hT, ← map_pow, hf, aeval_toLin'_apply]
  have hIP : cyc M w ≤ P := by
    rintro _ ⟨g, rfl⟩
    rw [hP, LinearMap.mem_ker, hTm, evalVec_apply, mulVec_mulVec, ← map_mul, mul_comm, map_mul,
      ← mulVec_mulVec]
    have : aeval M (β ^ m) *ᵥ w = 0 := by
      rw [← muVec_dvd_iff, hw]
      exact pow_dvd_pow β hmc
    rw [this, mulVec_zero]
  have hPQ : ∀ y ∈ P, ∀ z ∈ Q, y ⬝ᵥ z = 0 := by
    rintro y hy _ ⟨x, rfl⟩
    rw [hP, LinearMap.mem_ker, hTm] at hy
    rw [hTm, dotProduct_mulVec, ← mulVec_transpose, aeval_transpose_of_symm hM, hy,
      zero_dotProduct]
  set I := cyc M w with hI
  have hIQ : I ⊔ Q ≤ orthC I := by
    refine sup_le (fun y hy z hz => hiso z hz y hy) (fun z hz y hy => hPQ y (hIP hy) z hz)
  have hinf : I ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro y ⟨hy1, hy2⟩
    have := hm.inf_eq_bot
    rw [Submodule.mem_bot]
    have h3 : y ∈ P ⊓ Q := ⟨hIP hy1, hy2⟩
    rw [this] at h3
    exact h3
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq I Q
  rw [hinf, finrank_bot, add_zero] at h1
  have h2 := Submodule.finrank_mono hIQ
  have h3 := finrank_orthC_add I
  have h4 := Submodule.finrank_add_eq_of_isCompl hm
  rw [Module.finrank_fin_fun] at h4
  have hdimI : finrank F I = c * β.natDegree := by
    rw [hI, finrank_cyc, hw, natDegree_pow]
  have hPdim : 2 * (c * β.natDegree) ≤ finrank F P := by omega
  have hle := finrank_ker_aeval_pow_le f hβ (a := 2 * c - 1)
    (by rw [hf, charpoly_toLin', show 2 * c - 1 + 1 = 2 * c by omega]; exact hndvd) m
  rw [map_pow, ← hT, ← hP] at hle
  have hdeg := Irreducible.natDegree_pos hβ
  have : (2 * c - 1) * β.natDegree < 2 * (c * β.natDegree) := by
    have : (2 * c - 1) * β.natDegree + β.natDegree = 2 * (c * β.natDegree) := by
      rw [← Nat.succ_mul, show (2 * c - 1).succ = 2 * c by omega]; ring
    omega
  omega

end Isotropic

section Alt

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) (ZMod 2)}

theorem dot_aeval_aeval (hM : Mᵀ = M) (hd : ∀ i, M i i = 0) (a b : (ZMod 2)[X]) :
    (aeval M a *ᵥ ones n (ZMod 2)) ⬝ᵥ (aeval M b *ᵥ ones n (ZMod 2)) = (a * b).coeff 0 * n := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, aeval_transpose_of_symm hM,
    mulVec_mulVec, ← map_mul, dotProduct_comm, ones_dot_aeval hM hd]

theorem X_dvd_muVec (hM : Mᵀ = M) (hd : ∀ i, M i i = 0) (hodd : n % 2 = 1) :
    X ∣ muVec M (ones n (ZMod 2)) := by
  rw [X_dvd_iff]
  have h := congrArg (ones n (ZMod 2) ⬝ᵥ ·) (aeval_muVec M (ones n (ZMod 2)))
  simp only [dotProduct_zero] at h
  rw [ones_dot_aeval hM hd] at h
  have hn : (n : ZMod 2) = 1 := by rw [← ZMod.natCast_mod, hodd, Nat.cast_one]
  rwa [hn, mul_one] at h

theorem cyc_isotropic (hM : Mᵀ = M) (hd : ∀ i, M i i = 0) {q : (ZMod 2)[X]}
    (hq : n % 2 = 0 ∨ q.coeff 0 = 0) :
    ∀ y ∈ cyc M (aeval M q *ᵥ ones n (ZMod 2)), ∀ z ∈ cyc M (aeval M q *ᵥ ones n (ZMod 2)),
      y ⬝ᵥ z = 0 := by
  rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
  rw [evalVec_apply, evalVec_apply, mulVec_mulVec, mulVec_mulVec, ← map_mul, ← map_mul,
    dot_aeval_aeval hM hd, mul_coeff_zero, mul_coeff_zero, mul_coeff_zero]
  rcases hq with h0 | h0
  · rw [(ZMod.natCast_eq_zero_iff n 2).2 (Nat.dvd_of_mod_eq_zero h0), mul_zero]
  · rw [h0]; ring

theorem pow_dvd_of_pow_dvd_pow_mul_sq {p f : (ZMod 2)[X]} (hp : Irreducible p) {k r a : ℕ}
    (h : p ^ k ∣ p ^ r * f ^ 2) (ha : 2 * a + r ≤ k + 1) : p ^ a ∣ f := by
  have hpr := hp.prime
  by_cases hf : f = 0
  · rw [hf]; exact dvd_zero _
  obtain ⟨b, g, hg, rfl⟩ := WfDvdMonoid.max_power_factor hf hp
  have hkb : k ≤ r + 2 * b := by
    by_contra hlt
    push Not at hlt
    obtain ⟨t, ht⟩ := h
    have e : p ^ (r + 2 * b) * g ^ 2 = p ^ (r + 2 * b) * (p ^ (k - (r + 2 * b)) * t) := by
      rw [← mul_assoc, ← pow_add, show r + 2 * b + (k - (r + 2 * b)) = k by omega, ← ht]
      ring
    have e2 := mul_left_cancel₀ (pow_ne_zero _ hp.ne_zero) e
    have : p ∣ g ^ 2 := by
      rw [e2]
      exact (dvd_pow_self p (by omega)).mul_right _
    exact hg (hpr.dvd_of_dvd_pow this)
  exact (pow_dvd_pow p (by omega)).mul_right g

variable {A : Matrix (Fin n) (Fin n) ℤ}

theorem muVec_dvd_gamo (hA : A.IsSymm) (hd : ∀ i, A i i = 0) :
    muVec (modP 2 A) (ones n (ZMod 2)) ∣ gamo A := by
  set M := modP 2 A with hMdef
  have hM := modP_two_transpose hA
  have hMd := modP_two_diag hd
  set μ := muVec M (ones n (ZMod 2)) with hμ
  have hμm : μ.Monic := muVec_monic _ _
  have hchar : M.charpoly = X ^ (n % 2) * gam A ^ 2 := by
    rw [hMdef, charpoly_modP_eq, redP_charpoly_eq hA hd]
  refine dvd_of_forall_pow_mult_dvd hμm fun β hβ => ?_
  have hβi := irreducible_of_mem_factorsSet hβ
  have hβm := monic_of_mem_factorsSet hβ
  set c := mult μ β with hc
  have hc1 : 1 ≤ c := mult_pos hβ
  have hcof := pow_mul_cofactor hμm hβ
  set q := cofactor μ β with hq
  by_cases hcase : n % 2 = 0 ∨ β ≠ X
  ·
    have hw : muVec M (aeval M q *ᵥ ones n (ZMod 2)) = β ^ c :=
      muVec_aeval M _ (hβm.pow c) (by rw [mul_comm]; exact hcof)
    have hq0 : n % 2 = 0 ∨ q.coeff 0 = 0 := by
      rcases hcase with h | h
      · exact Or.inl h
      · rcases Nat.mod_two_eq_zero_or_one n with h' | h'
        · exact Or.inl h'
        right
        rw [← X_dvd_iff]
        have hXμ : X ∣ μ := X_dvd_muVec hM hMd h'
        rw [← hcof] at hXμ
        have hcop : IsCoprime X (β ^ c) := by
          refine IsCoprime.pow_right ?_
          rw [Irreducible.coprime_iff_not_dvd irreducible_X]
          intro hXβ
          exact h (eq_of_monic_of_associated monic_X hβm
            (associated_of_dvd_dvd hXβ ((irreducible_X.dvd_symm hβi hXβ)))).symm
        exact hcop.dvd_of_dvd_mul_left hXμ
    have h2c := pow_two_mul_dvd_charpoly hM hβi hw (cyc_isotropic hM hMd hq0)
    rw [hchar] at h2c
    have : β ^ (2 * c) ∣ β ^ 0 * gamo A ^ 2 := by
      rw [pow_zero, one_mul, gamo, mul_pow, ← pow_mul, show n % 2 * 2 = n % 2 + n % 2 by ring,
        pow_add, mul_assoc]
      exact h2c.mul_left _
    exact pow_dvd_of_pow_dvd_pow_mul_sq hβi this (by omega)
  ·
    push Not at hcase
    obtain ⟨hodd, rfl⟩ := hcase
    have hodd' : n % 2 = 1 := by omega
    have hw : muVec M (aeval M (X * q) *ᵥ ones n (ZMod 2)) = X ^ (c - 1) := by
      apply muVec_aeval M _ (monic_X_pow _)
      calc X * q * X ^ (c - 1) = X ^ (c - 1 + 1) * q := by ring
        _ = X ^ c * q := by rw [Nat.sub_add_cancel hc1]
        _ = μ := hcof
    have h2c := pow_two_mul_dvd_charpoly hM irreducible_X hw
      (cyc_isotropic hM hMd (Or.inr (by rw [coeff_X_mul_zero])))
    rw [hchar, hodd', pow_one] at h2c
    have : X ^ (c - 1) ∣ gam A :=
      pow_dvd_of_pow_dvd_pow_mul_sq irreducible_X (k := 2 * (c - 1)) (r := 1) (a := c - 1)
        (by rw [pow_one]; exact h2c) (by omega)
    rw [gamo, hodd', pow_one, show c = (c - 1) + 1 by omega, pow_succ', ]
    exact mul_dvd_mul_left X this

theorem natDegree_gamo (hA : A.IsSymm) (hd : ∀ i, A i i = 0) :
    (gamo A).natDegree = (n + 1) / 2 := by
  rw [gamo, natDegree_mul (pow_ne_zero _ X_ne_zero) (gam_ne_zero hA hd), natDegree_X_pow,
    natDegree_gam hA hd]
  omega

theorem lem_krylovlaw_a (hA : A.IsSymm) (hd : ∀ i, A i i = 0) :
    (muVec (modP 2 A) (ones n (ZMod 2))).natDegree ≤ (n + 1) / 2 ∧
      ∃ γ' : (ZMod 2)[X], γ'.Monic ∧
        γ'.natDegree = (n + 1) / 2 - (muVec (modP 2 A) (ones n (ZMod 2))).natDegree ∧
        gamo A = muVec (modP 2 A) (ones n (ZMod 2)) * γ' := by
  set μ := muVec (modP 2 A) (ones n (ZMod 2))
  obtain ⟨γ', hγ'⟩ := muVec_dvd_gamo hA hd
  have hμm : μ.Monic := muVec_monic _ _
  have hgo : (gamo A).Monic := gamo_monic hA hd
  have hγ'0 : γ' ≠ 0 := by
    rintro rfl; rw [mul_zero] at hγ'; exact hgo.ne_zero hγ'
  have hdeg : (gamo A).natDegree = μ.natDegree + γ'.natDegree := by
    rw [hγ', natDegree_mul hμm.ne_zero hγ'0]
  rw [natDegree_gamo hA hd] at hdeg
  refine ⟨by omega, γ', ?_, by omega, hγ'⟩
  have := hgo
  rw [hγ'] at this
  exact hμm.of_mul_monic_left this

end Alt

section Lambda

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) (ZMod 2)} (hM : Mᵀ = M) (hd : ∀ i, M i i = 0)
include hM hd

theorem qForm_add_cyc_A {y z : Fin n → ZMod 2} (hy : y ∈ cyc M (ones n (ZMod 2)))
    (hz : z ∈ cyc M (ones n (ZMod 2))) : qForm M (y + z) = qForm M y + qForm M z := by
  rw [qForm_polar hM hd]
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  have h1 : M *ᵥ (aeval M b *ᵥ ones n (ZMod 2)) = aeval M (X * b) *ᵥ ones n (ZMod 2) := by
    rw [map_mul, aeval_X, mulVec_mulVec]
  rw [evalVec_apply, evalVec_apply, h1, dot_aeval_aeval hM hd, mul_coeff_zero, mul_coeff_zero,
    coeff_X_zero]
  ring

theorem qForm_add_cyc_J {y z : Fin n → ZMod 2} (hy : y ∈ cyc M (ones n (ZMod 2)))
    (hz : z ∈ cyc M (ones n (ZMod 2))) :
    qForm (offDiag n (ZMod 2)) (y + z) = qForm (offDiag n (ZMod 2)) y + qForm (offDiag n (ZMod 2)) z := by
  rw [qForm_polar offDiag_transpose offDiag_diag]
  have hJ : offDiag n (ZMod 2) *ᵥ z = fun i => ones n (ZMod 2) ⬝ᵥ z - z i := by
    funext i
    simp only [mulVec, dotProduct, offDiag, of_apply, ones, one_mul]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), ite_eq_left rfl, zero_mul, add_zero,
      ← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_sub_cancel_right]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [ite_eq_right (Finset.ne_of_mem_erase hl).symm, one_mul]
  have hdot : y ⬝ᵥ (offDiag n (ZMod 2) *ᵥ z) =
      (ones n (ZMod 2) ⬝ᵥ y) * (ones n (ZMod 2) ⬝ᵥ z) - y ⬝ᵥ z := by
    rw [hJ]
    simp only [dotProduct, ones, one_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hdot]
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  rw [evalVec_apply, evalVec_apply, dot_aeval_aeval hM hd, ones_dot_aeval hM hd,
    ones_dot_aeval hM hd, mul_coeff_zero]
  have hsq : (n : ZMod 2) * n = n := by rw [← sq]; exact ZMod.pow_card _
  linear_combination (a.coeff 0 * b.coeff 0) * hsq

omit hM hd in
theorem qForm_add_of_kills {B : Matrix (Fin n) (Fin n) (ZMod 2)} (hB : Bᵀ = B)
    (hBd : ∀ i, B i i = 0) (hBK : ∀ y ∈ cyc M (ones n (ZMod 2)), B *ᵥ y = 0) {y z : Fin n → ZMod 2}
    (hz : z ∈ cyc M (ones n (ZMod 2))) : qForm B (y + z) = qForm B y + qForm B z := by
  rw [qForm_polar hB hBd, hBK z hz, dotProduct_zero, add_zero]

end Lambda

section LambdaIII

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hd : ∀ i, A i i = 0) (hn : 1 ≤ n)
include hA hd hn

theorem lem_Lambda_iii (h : (ZMod 2)[X]) :
    omegaF A (muVec (modP 2 A) (ones n (ZMod 2)) ^ 2 * h) = 0 := by
  set M := modP 2 A
  set μ := muVec M (ones n (ZMod 2))
  have hdec := sq_decomp h
  have h1 : μ ^ 2 * h = (μ * contract 2 h) ^ 2 + X * (μ * contract 2 (divX h)) ^ 2 := by
    conv_lhs => rw [hdec]
    ring
  have hzero : ∀ g : (ZMod 2)[X], aeval M (μ * g) *ᵥ ones n (ZMod 2) = 0 := by
    intro g
    rw [mul_comm, map_mul, ← mulVec_mulVec, aeval_muVec, mulVec_zero]
  rw [h1, lem_Lambda_ii hA hd hn, hzero, hzero, qForm_zero_right, qForm_zero_right, add_zero]
  intro hodd
  rw [mul_coeff_zero, (X_dvd_iff).1 (X_dvd_muVec (modP_two_transpose hA) (modP_two_diag hd) hodd),
    zero_mul]

end LambdaIII

end DGS
