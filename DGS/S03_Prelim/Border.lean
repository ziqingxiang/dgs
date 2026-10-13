module

public import DGS.S03_Prelim.SignVectors

@[expose] public section

open Matrix Module

namespace DGS

section Border

variable {F : Type*} [Field F] {r : ℕ}

noncomputable def corank {k : ℕ} (A : Matrix (Fin k) (Fin k) F) : ℕ :=
  finrank F (LinearMap.ker A.mulVecLin)

theorem mem_ker_mulVecLin {k : ℕ} {A : Matrix (Fin k) (Fin k) F} {x : Fin k → F} :
    x ∈ LinearMap.ker A.mulVecLin ↔ A *ᵥ x = 0 := by
  rw [LinearMap.mem_ker, mulVecLin_apply]

def dotProductLin {k : ℕ} (y : Fin k → F) : (Fin k → F) →ₗ[F] F where
  toFun v := y ⬝ᵥ v
  map_add' v w := dotProduct_add y v w
  map_smul' a v := dotProduct_smul a y v

def border (L : Matrix (Fin r) (Fin r) F) (y : Fin r → F) (c : F) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) F :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases c y j)
    (fun i' => Fin.lastCases (y i') (fun j' => L i' j') j) i

variable (L : Matrix (Fin r) (Fin r) F) (y : Fin r → F) (c : F)

omit [Field F] in
@[simp] theorem border_castSucc_castSucc (i j : Fin r) :
    border L y c i.castSucc j.castSucc = L i j := by simp [border]

omit [Field F] in
@[simp] theorem border_castSucc_last (i : Fin r) : border L y c i.castSucc (Fin.last r) = y i := by
  simp [border]

omit [Field F] in
@[simp] theorem border_last_castSucc (j : Fin r) : border L y c (Fin.last r) j.castSucc = y j := by
  simp [border]

omit [Field F] in
@[simp] theorem border_last_last : border L y c (Fin.last r) (Fin.last r) = c := by simp [border]

theorem border_mulVec_snoc (v : Fin r → F) (t : F) :
    border L y c *ᵥ Fin.snoc v t = Fin.snoc (L *ᵥ v + t • y) (y ⬝ᵥ v + c * t) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, border_last_castSucc, Fin.snoc_castSucc,
      border_last_last, Fin.snoc_last]
  · simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, border_castSucc_castSucc,
      Fin.snoc_castSucc, border_castSucc_last, Fin.snoc_last, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

omit [Field F] in
theorem border_transpose (hL : Lᵀ = L) : (border L y c)ᵀ = border L y c := by
  ext i j
  rw [transpose_apply]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · simp
  · simp
  · simp only [border_castSucc_castSucc]
    simpa [transpose_apply] using congrFun (congrFun hL i) j

omit [Field F] in
theorem snoc_inj {α : Type*} {v v' : Fin r → α} {t t' : α} :
    (Fin.snoc v t : Fin (r + 1) → α) = Fin.snoc v' t' ↔ v = v' ∧ t = t' := by
  constructor
  · intro h
    exact ⟨funext fun i => by simpa using congrFun h i.castSucc,
      by simpa using congrFun h (Fin.last r)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem snoc_eq_zero_iff {v : Fin r → F} {t : F} :
    (Fin.snoc v t : Fin (r + 1) → F) = 0 ↔ v = 0 ∧ t = 0 := by
  rw [show (0 : Fin (r + 1) → F) = Fin.snoc (0 : Fin r → F) 0 from
    (Fin.snoc_init_self (0 : Fin (r + 1) → F)).symm, snoc_inj]

variable {L y c}

theorem mem_ker_border {v : Fin r → F} {t : F} :
    (Fin.snoc v t : Fin (r + 1) → F) ∈ LinearMap.ker (border L y c).mulVecLin ↔
      L *ᵥ v + t • y = 0 ∧ y ⬝ᵥ v + c * t = 0 := by
  rw [mem_ker_mulVecLin, border_mulVec_snoc, snoc_eq_zero_iff]

variable (F r) in
def snocLin : ((Fin r → F) × F) →ₗ[F] (Fin (r + 1) → F) where
  toFun x := Fin.snoc x.1 x.2
  map_add' x x' := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
  map_smul' a x := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

theorem snocLin_apply (x : (Fin r → F) × F) : snocLin F r x = Fin.snoc x.1 x.2 := rfl

theorem snocLin_injective : Function.Injective (snocLin F r) := by
  intro x x' h
  rw [snocLin_apply, snocLin_apply, snoc_inj] at h
  exact Prod.ext h.1 h.2

theorem mulVec_dotProduct_of_symm {k : ℕ} {L : Matrix (Fin k) (Fin k) F} (hL : Lᵀ = L)
    (v w : Fin k → F) : (L *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (L *ᵥ w) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hL]

theorem exists_mulVec_eq_of_perp {k : ℕ} {L : Matrix (Fin k) (Fin k) F} (hL : Lᵀ = L)
    {y : Fin k → F} (hy : ∀ v ∈ LinearMap.ker L.mulVecLin, y ⬝ᵥ v = 0) : ∃ y0, L *ᵥ y0 = y := by
  obtain ⟨V, hV, hVdim⟩ := finrank_orthogonal_dotProduct (LinearMap.ker L.mulVecLin)
  have hrange : LinearMap.range L.mulVecLin = V := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, rfl⟩
      rw [hV]
      intro w hw
      rw [mem_ker_mulVecLin] at hw
      rw [mulVecLin_apply, mulVec_dotProduct_of_symm hL, hw, dotProduct_zero]
    · have hrk := LinearMap.finrank_range_add_finrank_ker L.mulVecLin
      rw [Module.finrank_fin_fun] at hrk
      omega
  have hyV : y ∈ V := (hV y).2 hy
  rw [← hrange] at hyV
  obtain ⟨y0, hy0⟩ := hyV
  exact ⟨y0, hy0⟩

theorem finrank_inf_perp_add_one {k : ℕ} {K : Submodule F (Fin k → F)} {y : Fin k → F} {k0 : Fin k → F}
    (hk0 : k0 ∈ K) (hyk0 : y ⬝ᵥ k0 ≠ 0) :
    finrank F ↥(K ⊓ LinearMap.ker (dotProductLin y)) + 1 = finrank F K := by
  have hk0' : k0 ≠ 0 := by
    rintro rfl
    exact hyk0 (dotProduct_zero y)
  have hlt : K ⊓ LinearMap.ker (dotProductLin y) < K := by
    refine lt_of_le_of_ne inf_le_left (fun h => hyk0 ?_)
    have : k0 ∈ K ⊓ LinearMap.ker (dotProductLin y) := by rw [h]; exact hk0
    exact LinearMap.mem_ker.1 this.2
  have hle : K ≤ (K ⊓ LinearMap.ker (dotProductLin y)) ⊔ (F ∙ k0) := by
    intro x hx
    rw [Submodule.mem_sup]
    refine ⟨x - ((y ⬝ᵥ x) / (y ⬝ᵥ k0)) • k0, ⟨K.sub_mem hx (K.smul_mem _ hk0), ?_⟩,
      ((y ⬝ᵥ x) / (y ⬝ᵥ k0)) • k0, Submodule.mem_span_singleton.2 ⟨_, rfl⟩, by abel⟩
    show y ⬝ᵥ (x - ((y ⬝ᵥ x) / (y ⬝ᵥ k0)) • k0) = 0
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hyk0, sub_self]
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := (Submodule.finrank_mono hle).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ (F ∙ k0))
  have h3 : finrank F (F ∙ k0) = 1 := finrank_span_singleton hk0'
  omega

theorem lem_border_a (hL : Lᵀ = L) (hy : ¬ ∀ k ∈ LinearMap.ker L.mulVecLin, y ⬝ᵥ k = 0) :
    (∀ v t, (Fin.snoc v t : Fin (r + 1) → F) ∈ LinearMap.ker (border L y c).mulVecLin ↔
      v ∈ LinearMap.ker L.mulVecLin ∧ y ⬝ᵥ v = 0 ∧ t = 0) ∧
    corank (border L y c) + 1 = corank L := by
  push Not at hy
  obtain ⟨k0, hk0, hyk0⟩ := hy
  have hker : ∀ v t, (Fin.snoc v t : Fin (r + 1) → F) ∈ LinearMap.ker (border L y c).mulVecLin ↔
      v ∈ LinearMap.ker L.mulVecLin ∧ y ⬝ᵥ v = 0 ∧ t = 0 := by
    intro v t
    rw [mem_ker_border, mem_ker_mulVecLin]
    constructor
    · rintro ⟨h1, h2⟩
      have ht : t = 0 := by
        have h3 : (L *ᵥ v + t • y) ⬝ᵥ k0 = 0 := by rw [h1, zero_dotProduct]
        rw [add_dotProduct, mulVec_dotProduct_of_symm hL, (mem_ker_mulVecLin.1 hk0),
          dotProduct_zero, zero_add, smul_dotProduct, smul_eq_mul] at h3
        exact (mul_eq_zero.1 h3).resolve_right hyk0
      subst ht
      refine ⟨by simpa using h1, by simpa using h2, rfl⟩
    · rintro ⟨h1, h2, rfl⟩
      exact ⟨by simpa using h1, by simpa using h2⟩
  refine ⟨hker, ?_⟩
  let ι0 : (Fin r → F) →ₗ[F] (Fin (r + 1) → F) := snocLin F r ∘ₗ LinearMap.inl F _ F
  have hι0 : Function.Injective ι0 := snocLin_injective.comp (LinearMap.inl_injective)
  have hmap : LinearMap.ker (border L y c).mulVecLin =
      (LinearMap.ker L.mulVecLin ⊓ LinearMap.ker (dotProductLin y)).map ι0 := by
    ext x
    obtain ⟨v, t, rfl⟩ : ∃ v t, x = Fin.snoc v t :=
      ⟨Fin.init x, x (Fin.last r), (Fin.snoc_init_self x).symm⟩
    rw [hker, Submodule.mem_map]
    constructor
    · rintro ⟨h1, h2, rfl⟩
      exact ⟨v, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨w, ⟨h1, h2⟩, hw⟩
      have hw' : (Fin.snoc w 0 : Fin (r + 1) → F) = Fin.snoc v t := hw
      rw [snoc_inj] at hw'
      obtain ⟨rfl, rfl⟩ := hw'
      exact ⟨h1, h2, rfl⟩
  unfold corank
  rw [hmap, ← (Submodule.equivMapOfInjective ι0 hι0 _).finrank_eq]
  exact finrank_inf_perp_add_one hk0 hyk0

theorem lem_border_b (hL : Lᵀ = L) (hy : ∀ k ∈ LinearMap.ker L.mulVecLin, y ⬝ᵥ k = 0) :
    (∃ y0, L *ᵥ y0 = y) ∧
    (∀ y0 y0', L *ᵥ y0 = y → L *ᵥ y0' = y → y ⬝ᵥ y0 = y ⬝ᵥ y0') ∧
    (∀ y0, L *ᵥ y0 = y → c ≠ y ⬝ᵥ y0 →
      (∀ v t, (Fin.snoc v t : Fin (r + 1) → F) ∈ LinearMap.ker (border L y c).mulVecLin ↔
        v ∈ LinearMap.ker L.mulVecLin ∧ t = 0) ∧ corank (border L y c) = corank L) ∧
    (∀ y0, L *ᵥ y0 = y → c = y ⬝ᵥ y0 →
      (∀ x, x ∈ LinearMap.ker (border L y c).mulVecLin ↔
        ∃ v ∈ LinearMap.ker L.mulVecLin, ∃ t, x = Fin.snoc (v - t • y0) t) ∧
      corank (border L y c) = corank L + 1) := by
  have key : ∀ y0, L *ᵥ y0 = y → ∀ v t,
      (Fin.snoc v t : Fin (r + 1) → F) ∈ LinearMap.ker (border L y c).mulVecLin ↔
        v + t • y0 ∈ LinearMap.ker L.mulVecLin ∧ t * (c - y ⬝ᵥ y0) = 0 := by
    intro y0 hy0 v t
    rw [mem_ker_border, mem_ker_mulVecLin, mulVec_add, mulVec_smul, hy0]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have h3 : y ⬝ᵥ (v + t • y0) = 0 := hy _ (mem_ker_mulVecLin.2 (by rw [mulVec_add, mulVec_smul, hy0]; exact h1))
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h3
      linear_combination h2 - h3
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have h3 : y ⬝ᵥ (v + t • y0) = 0 := hy _ (mem_ker_mulVecLin.2 (by rw [mulVec_add, mulVec_smul, hy0]; exact h1))
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h3
      linear_combination h2 + h3
  have hind : ∀ y0 y0', L *ᵥ y0 = y → L *ᵥ y0' = y → y ⬝ᵥ y0 = y ⬝ᵥ y0' := by
    intro y0 y0' h0 h0'
    have h1 : y0 - y0' ∈ LinearMap.ker L.mulVecLin := by
      rw [mem_ker_mulVecLin, mulVec_sub, h0, h0', sub_self]
    have h2 := hy _ h1
    rw [dotProduct_sub, sub_eq_zero] at h2
    exact h2
  refine ⟨exists_mulVec_eq_of_perp hL hy, hind, ?_, ?_⟩
  · intro y0 hy0 hc
    have hc' : c - y ⬝ᵥ y0 ≠ 0 := sub_ne_zero.2 hc
    have hker : ∀ v t, (Fin.snoc v t : Fin (r + 1) → F) ∈ LinearMap.ker (border L y c).mulVecLin ↔
        v ∈ LinearMap.ker L.mulVecLin ∧ t = 0 := by
      intro v t
      rw [key y0 hy0]
      constructor
      · rintro ⟨h1, h2⟩
        have ht : t = 0 := (mul_eq_zero.1 h2).resolve_right hc'
        subst ht
        exact ⟨by simpa using h1, rfl⟩
      · rintro ⟨h1, rfl⟩
        exact ⟨by simpa using h1, by simp⟩
    refine ⟨hker, ?_⟩
    let ι0 : (Fin r → F) →ₗ[F] (Fin (r + 1) → F) := snocLin F r ∘ₗ LinearMap.inl F _ F
    have hι0 : Function.Injective ι0 := snocLin_injective.comp (LinearMap.inl_injective)
    have hmap : LinearMap.ker (border L y c).mulVecLin = (LinearMap.ker L.mulVecLin).map ι0 := by
      ext x
      obtain ⟨v, t, rfl⟩ : ∃ v t, x = Fin.snoc v t :=
        ⟨Fin.init x, x (Fin.last r), (Fin.snoc_init_self x).symm⟩
      rw [hker, Submodule.mem_map]
      constructor
      · rintro ⟨h1, rfl⟩
        exact ⟨v, h1, rfl⟩
      · rintro ⟨w, h1, hw⟩
        have hw' : (Fin.snoc w 0 : Fin (r + 1) → F) = Fin.snoc v t := hw
        rw [snoc_inj] at hw'
        obtain ⟨rfl, rfl⟩ := hw'
        exact ⟨h1, rfl⟩
    unfold corank
    rw [hmap, ← (Submodule.equivMapOfInjective ι0 hι0 _).finrank_eq]
  · intro y0 hy0 hc
    have hc' : c - y ⬝ᵥ y0 = 0 := sub_eq_zero.2 hc
    have hker : ∀ x, x ∈ LinearMap.ker (border L y c).mulVecLin ↔
        ∃ v ∈ LinearMap.ker L.mulVecLin, ∃ t, x = Fin.snoc (v - t • y0) t := by
      intro x
      obtain ⟨v, t, rfl⟩ : ∃ v t, x = Fin.snoc v t :=
        ⟨Fin.init x, x (Fin.last r), (Fin.snoc_init_self x).symm⟩
      rw [key y0 hy0, hc', mul_zero]
      constructor
      · rintro ⟨h1, -⟩
        exact ⟨v + t • y0, h1, t, by rw [add_sub_cancel_right]⟩
      · rintro ⟨w, hw, t', h⟩
        rw [snoc_inj] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by rwa [sub_add_cancel], rfl⟩
    refine ⟨hker, ?_⟩
    let K := LinearMap.ker L.mulVecLin
    let Ψ' : (K × F) →ₗ[F] ((Fin r → F) × F) :=
      LinearMap.prod (K.subtype ∘ₗ LinearMap.fst F K F - (LinearMap.snd F K F).smulRight y0)
        (LinearMap.snd F K F)
    let Ψ : (K × F) →ₗ[F] (Fin (r + 1) → F) := snocLin F r ∘ₗ Ψ'
    have hΨ : ∀ x : K × F, Ψ x = Fin.snoc ((x.1 : Fin r → F) - x.2 • y0) x.2 := fun x => rfl
    have hΨinj : Function.Injective Ψ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      rw [hΨ, snoc_eq_zero_iff] at hx
      obtain ⟨h1, h2⟩ := hx
      rw [h2, zero_smul, sub_zero] at h1
      exact Prod.ext (Subtype.ext h1) h2
    have hrange : LinearMap.range Ψ = LinearMap.ker (border L y c).mulVecLin := by
      ext x
      rw [hker, LinearMap.mem_range]
      constructor
      · rintro ⟨⟨k, t⟩, rfl⟩
        exact ⟨k, k.2, t, hΨ _⟩
      · rintro ⟨v, hv, t, rfl⟩
        exact ⟨(⟨v, hv⟩, t), hΨ _⟩
    unfold corank
    rw [← hrange, LinearMap.finrank_range_of_inj hΨinj, Module.finrank_prod, Module.finrank_self]

theorem lem_border_corank (hL : Lᵀ = L) :
    corank (border L y c) ≤ corank L + 1 ∧ corank L ≤ corank (border L y c) + 1 ∧
      (corank L ≤ corank (border L y c) ↔ ∀ k ∈ LinearMap.ker L.mulVecLin, y ⬝ᵥ k = 0) := by
  by_cases hy : ∀ k ∈ LinearMap.ker L.mulVecLin, y ⬝ᵥ k = 0
  · obtain ⟨⟨y0, hy0⟩, -, h1, h2⟩ := lem_border_b (c := c) hL hy
    by_cases hc : c = y ⬝ᵥ y0
    · have := (h2 y0 hy0 hc).2
      refine ⟨by omega, by omega, ⟨fun _ => hy, fun _ => by omega⟩⟩
    · have := (h1 y0 hy0 hc).2
      refine ⟨by omega, by omega, ⟨fun _ => hy, fun _ => by omega⟩⟩
  · have := (lem_border_a (c := c) hL hy).2
    exact ⟨by omega, by omega, ⟨fun h => (by omega : False).elim, fun h => absurd h hy⟩⟩

theorem lem_border_inv (hL : Lᵀ = L) (hdet : IsUnit L.det) :
    corank (border L y c) ≤ 1 ∧ (corank (border L y c) = 1 ↔ c = y ⬝ᵥ (L⁻¹ *ᵥ y)) ∧
      (c = y ⬝ᵥ (L⁻¹ *ᵥ y) → ∀ x, x ∈ LinearMap.ker (border L y c).mulVecLin ↔
        ∃ t : F, x = t • (Fin.snoc (L⁻¹ *ᵥ y) (-1) : Fin (r + 1) → F)) := by
  have hK : ∀ v, v ∈ LinearMap.ker L.mulVecLin ↔ v = 0 := by
    intro v
    rw [mem_ker_mulVecLin]
    constructor
    · intro h
      have := congrArg (fun w => L⁻¹ *ᵥ w) h
      simpa [mulVec_mulVec, nonsing_inv_mul _ hdet] using this
    · rintro rfl
      exact mulVec_zero _
  have hK0 : corank L = 0 := by
    unfold corank
    rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    exact fun v hv => (hK v).1 hv
  have hy : ∀ k ∈ LinearMap.ker L.mulVecLin, y ⬝ᵥ k = 0 := fun k hk => by
    rw [(hK k).1 hk, dotProduct_zero]
  have hy0 : L *ᵥ (L⁻¹ *ᵥ y) = y := by rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  obtain ⟨-, -, h1, h2⟩ := lem_border_b (c := c) hL hy
  refine ⟨?_, ⟨fun h => ?_, fun h => by rw [(h2 _ hy0 h).2, hK0]⟩, fun h x => ?_⟩
  · by_cases hc : c = y ⬝ᵥ (L⁻¹ *ᵥ y)
    · rw [(h2 _ hy0 hc).2, hK0]
    · rw [(h1 _ hy0 hc).2, hK0]
      exact zero_le_one
  · by_contra hc
    rw [(h1 _ hy0 hc).2, hK0] at h
    exact zero_ne_one h
  · rw [((h2 _ hy0 h).1 x)]
    constructor
    · rintro ⟨v, hv, t, rfl⟩
      rw [(hK v).1 hv]
      refine ⟨-t, ?_⟩
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
    · rintro ⟨t, rfl⟩
      refine ⟨0, (hK 0).2 rfl, -t, ?_⟩
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

end Border

end DGS
