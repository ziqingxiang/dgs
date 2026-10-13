module

public import DGS.Core.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

open Matrix

namespace DGS

def twoValued {F : Type*} {N : ℕ} (a b : F) (s : Fin N → Bool) : Fin N → F :=
  fun i => if s i then a else b

variable {F : Type*} [Field F] {N : ℕ}

omit [Field F] in
theorem twoValued_injective {a b : F} (hab : a ≠ b) : Function.Injective (twoValued (N := N) a b) := by
  intro s s' h
  funext i
  have hi := congrFun h i
  simp only [twoValued] at hi
  cases h1 : s i <;> cases h2 : s' i
  · rfl
  · simp [h1, h2] at hi
    exact absurd hi.symm hab
  · simp [h1, h2] at hi
    exact absurd hi hab
  · rfl

theorem exists_coords_injective (V : Submodule F (Fin N → F)) :
    ∃ (κ : Type) (_ : Fintype κ) (ι : κ → Fin N), Fintype.card κ ≤ Module.finrank F V ∧
      ∀ v ∈ V, (∀ t, v (ι t) = 0) → v = 0 := by
  classical
  set k := Module.finrank F V
  let bV := Module.finBasis F V
  let r : Fin N → (Fin k → F) := fun i j => (bV j : Fin N → F) i
  obtain ⟨κ, ι, -, hspan, hli⟩ := exists_linearIndependent' F r
  have : Finite κ := hli.finite
  let : Fintype κ := Fintype.ofFinite κ
  refine ⟨κ, inferInstance, ι, ?_, ?_⟩
  · have := hli.fintype_card_le_finrank
    simpa using this
  · intro v hv h0
    let c : Fin k → F := fun j => bV.repr ⟨v, hv⟩ j
    have hvi : ∀ i, v i = r i ⬝ᵥ c := by
      intro i
      have h := congrArg (fun u : V => (u : Fin N → F) i) (bV.sum_repr ⟨v, hv⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at h
      rw [← h]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hperp : ∀ w ∈ Submodule.span F (Set.range (r ∘ ι)), w ⬝ᵥ c = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨t, rfl⟩ := hw
        rw [Function.comp_apply, ← hvi]
        exact h0 t
      | zero => exact zero_dotProduct c
      | add w w' _ _ h h' => rw [add_dotProduct, h, h', add_zero]
      | smul a w _ h => rw [smul_dotProduct, h, smul_zero]
    funext i
    rw [hvi, hperp _ (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)]
    rfl

theorem lem_odlyzko (a b : F) (hab : a ≠ b) (V : Submodule F (Fin N → F)) (x : Fin N → F) :
    Nat.card {s : Fin N → Bool // twoValued a b s - x ∈ V} ≤ 2 ^ Module.finrank F V := by
  classical
  obtain ⟨κ, _, ι, hcard, key⟩ := exists_coords_injective V
  let f : {s : Fin N → Bool // twoValued a b s - x ∈ V} → (κ → Bool) := fun s => s.1 ∘ ι
  have hf : Function.Injective f := by
    intro s s' h
    have hdiff : twoValued a b s.1 - twoValued a b s'.1 ∈ V := by
      have := V.sub_mem s.2 s'.2
      simpa using this
    have hzero : ∀ t, (twoValued a b s.1 - twoValued a b s'.1) (ι t) = 0 := by
      intro t
      have : s.1 (ι t) = s'.1 (ι t) := congrFun h t
      simp [twoValued, this]
    have := key _ hdiff hzero
    exact Subtype.ext (twoValued_injective hab (sub_eq_zero.1 this))
  calc Nat.card {s : Fin N → Bool // twoValued a b s - x ∈ V} ≤ Nat.card (κ → Bool) :=
        Nat.card_le_card_of_injective f hf
    _ = 2 ^ Fintype.card κ := by rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool]
    _ ≤ 2 ^ Module.finrank F V := Nat.pow_le_pow_right (by norm_num) hcard

theorem finrank_orthogonal_dotProduct (U : Submodule F (Fin N → F)) :
    ∃ V : Submodule F (Fin N → F), (∀ v, v ∈ V ↔ ∀ w ∈ U, v ⬝ᵥ w = 0) ∧
      Module.finrank F V + Module.finrank F U = N := by
  classical
  set d := Module.finrank F U
  let bU := Module.finBasis F U
  let M : Matrix (Fin d) (Fin N) F := Matrix.of fun j i => (bU j : Fin N → F) i
  refine ⟨LinearMap.ker M.mulVecLin, ?_, ?_⟩
  · intro v
    rw [LinearMap.mem_ker, mulVecLin_apply]
    constructor
    · intro hv w hw
      have hw' : (⟨w, hw⟩ : U) = ∑ j, bU.repr ⟨w, hw⟩ j • bU j := (bU.sum_repr _).symm
      have : w = ∑ j, bU.repr ⟨w, hw⟩ j • (bU j : Fin N → F) := by
        have := congrArg Subtype.val hw'
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this
      rw [this, dotProduct_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [dotProduct_smul, dotProduct_comm]
      have := congrFun hv j
      simp only [mulVec, M, Matrix.of_apply] at this
      rw [smul_eq_mul, show (bU j : Fin N → F) ⬝ᵥ v = 0 from this, mul_zero]
    · intro hv
      funext j
      show (fun i => M j i) ⬝ᵥ v = 0
      have hMj : (fun i => M j i) = (bU j : Fin N → F) := by
        funext i
        simp [M]
      rw [hMj, dotProduct_comm]
      exact hv _ (bU j).2
  · have hrank : M.rank = d := by
      rw [← rank_transpose, rank_eq_finrank_span_cols]
      have hli : LinearIndependent F Mᵀ.col := by
        have : Mᵀ.col = fun j => (bU j : Fin N → F) := by
          funext j i
          simp [M, Matrix.col]
        rw [this]
        exact bU.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fin_fun] at h
    have hr : Module.finrank F (LinearMap.range M.mulVecLin) = d := hrank
    omega

theorem lem_odlyzko_perp (a b : F) (hab : a ≠ b) (U : Submodule F (Fin N → F)) :
    prob (fun s : Fin N → Bool => ∀ w ∈ U, twoValued a b s ⬝ᵥ w = 0) ≤
      (2 : ℝ)⁻¹ ^ Module.finrank F U := by
  classical
  obtain ⟨V, hV, hdim⟩ := finrank_orthogonal_dotProduct U
  have hcount := lem_odlyzko a b hab V 0
  have hcongr : prob (fun s : Fin N → Bool => ∀ w ∈ U, twoValued a b s ⬝ᵥ w = 0) =
      prob (fun s : Fin N → Bool => twoValued a b s - 0 ∈ V) :=
    prob_congr fun s => by rw [sub_zero, hV]
  rw [hcongr]
  unfold prob
  have hN : Nat.card (Fin N → Bool) = 2 ^ N := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [hN]
  have h1 : (Nat.card {s : Fin N → Bool // twoValued a b s - 0 ∈ V} : ℝ) ≤ 2 ^ Module.finrank F V := by
    exact_mod_cast hcount
  have h2 : (2 : ℝ) ^ Module.finrank F V / 2 ^ N = (2 : ℝ)⁻¹ ^ Module.finrank F U := by
    have hpow : (2 : ℝ) ^ N = 2 ^ Module.finrank F V * 2 ^ Module.finrank F U := by
      rw [← pow_add, hdim]
    rw [hpow, inv_pow]
    field_simp
  calc (Nat.card {s : Fin N → Bool // twoValued a b s - 0 ∈ V} : ℝ) / ((2 ^ N : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ Module.finrank F V / 2 ^ N := by
        push_cast
        exact div_le_div_of_nonneg_right h1 (by positivity)
    _ = (2 : ℝ)⁻¹ ^ Module.finrank F U := h2

theorem prob_not_linearIndependent (a b : F) (hab : a ≠ b) (l : ℕ) :
    prob (fun s : Fin l → Fin N → Bool => ¬ LinearIndependent F (fun j => twoValued a b (s j))) ≤
      ((2 : ℝ) ^ l - 1) / 2 ^ N := by
  classical
  induction l with
  | zero =>
    have : prob (fun s : Fin 0 → Fin N → Bool => ¬ LinearIndependent F (fun j => twoValued a b (s j))) =
        prob (fun _ : Fin 0 → Fin N → Bool => False) :=
      prob_congr fun s => by simp
    rw [this, prob_false]
    simp
  | succ l ih =>
    let e := Fin.snocEquiv (fun _ : Fin (l + 1) => Fin N → Bool)
    have he : ∀ x : (Fin N → Bool) × (Fin l → Fin N → Bool),
        (fun j => twoValued a b (e x j)) = Fin.snoc (fun j => twoValued a b (x.2 j)) (twoValued a b x.1) := by
      intro x
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [e, Fin.snocEquiv]
    rw [← prob_equiv e]
    have hsplit : ∀ x : (Fin N → Bool) × (Fin l → Fin N → Bool),
        ¬ LinearIndependent F (fun j => twoValued a b (e x j)) →
          ¬ LinearIndependent F (fun j => twoValued a b (x.2 j)) ∨
            twoValued a b x.1 - 0 ∈ Submodule.span F (Set.range fun j => twoValued a b (x.2 j)) := by
      intro x hx
      rw [he, linearIndependent_finSnoc] at hx
      by_cases h : LinearIndependent F (fun j => twoValued a b (x.2 j))
      · right
        rw [sub_zero]
        by_contra h'
        exact hx ⟨h, h'⟩
      · exact Or.inl h
    refine (prob_mono hsplit).trans ((prob_or_le _ _).trans ?_)
    have h1 : prob (fun x : (Fin N → Bool) × (Fin l → Fin N → Bool) =>
        ¬ LinearIndependent F (fun j => twoValued a b (x.2 j))) ≤ ((2 : ℝ) ^ l - 1) / 2 ^ N := by
      rw [prob_snd (fun s : Fin l → Fin N → Bool => ¬ LinearIndependent F (fun j => twoValued a b (s j)))]
      exact ih
    have h2 : prob (fun x : (Fin N → Bool) × (Fin l → Fin N → Bool) =>
        twoValued a b x.1 - 0 ∈ Submodule.span F (Set.range fun j => twoValued a b (x.2 j))) ≤
          (2 : ℝ) ^ l / 2 ^ N := by
      apply prob_le_of_forall_snd _ (by positivity)
      intro t
      have hc := lem_odlyzko a b hab (Submodule.span F (Set.range fun j => twoValued a b (t j))) 0
      have hdim : Module.finrank F (Submodule.span F (Set.range fun j => twoValued a b (t j))) ≤ l := by
        have := finrank_range_le_card (R := F) (b := fun j => twoValued a b (t j))
        rw [Fintype.card_fin] at this
        exact this
      unfold prob
      have hN : Nat.card (Fin N → Bool) = 2 ^ N := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      rw [hN]
      push_cast
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (Nat.card {s : Fin N → Bool //
          twoValued a b s - 0 ∈ Submodule.span F (Set.range fun j => twoValued a b (t j))} : ℝ) ≤
          (2 : ℝ) ^ Module.finrank F (Submodule.span F (Set.range fun j => twoValued a b (t j))) := by
        exact_mod_cast hc
      exact this.trans (pow_le_pow_right₀ (by norm_num) hdim)
    calc _ ≤ ((2 : ℝ) ^ l - 1) / 2 ^ N + (2 : ℝ) ^ l / 2 ^ N := add_le_add h1 h2
      _ = ((2 : ℝ) ^ (l + 1) - 1) / 2 ^ N := by ring

theorem lem_odlyzko_rank (a b : F) (hab : a ≠ b) (l : ℕ) :
    prob (fun s : Fin l → Fin N → Bool =>
      (Matrix.of fun i j => twoValued a b (s j) i : Matrix (Fin N) (Fin l) F).rank < l) <
      (2 : ℝ) ^ ((l : ℤ) - N) := by
  classical
  have hsub : ∀ s : Fin l → Fin N → Bool,
      (Matrix.of fun i j => twoValued a b (s j) i : Matrix (Fin N) (Fin l) F).rank < l →
        ¬ LinearIndependent F (fun j => twoValued a b (s j)) := by
    intro s hs hli
    apply (lt_irrefl l)
    calc l = Module.finrank F (Submodule.span F (Set.range fun j => twoValued a b (s j))) := by
          rw [finrank_span_eq_card hli, Fintype.card_fin]
      _ = (Matrix.of fun i j => twoValued a b (s j) i : Matrix (Fin N) (Fin l) F).rank := by
          rw [rank_eq_finrank_span_cols]
          rfl
      _ < l := hs
  calc _ ≤ prob (fun s : Fin l → Fin N → Bool => ¬ LinearIndependent F (fun j => twoValued a b (s j))) :=
        prob_mono hsub
    _ ≤ ((2 : ℝ) ^ l - 1) / 2 ^ N := prob_not_linearIndependent a b hab l
    _ < (2 : ℝ) ^ l / 2 ^ N := by
        apply div_lt_div_of_pos_right _ (by positivity)
        linarith
    _ = (2 : ℝ) ^ ((l : ℤ) - N) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]

end DGS
