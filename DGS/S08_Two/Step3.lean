module

public import DGS.S08_Two.CondLaw

@[expose] public section

open Matrix Polynomial Module

namespace DGS

variable {n : ℕ}

local notation "V" => Fin n → ZMod 2
local notation "Mat" => Matrix (Fin n) (Fin n) (ZMod 2)

def linComb {k : ℕ} (w : Fin k → V) (c : Fin k → ZMod 2) : V := ∑ i, c i • w i

theorem linComb_mem_span {k : ℕ} (w : Fin k → V) (c : Fin k → ZMod 2) :
    linComb w c ∈ Submodule.span (ZMod 2) (Set.range w) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem linComb_injective {k : ℕ} {w : Fin k → V} (hw : LinearIndependent (ZMod 2) w) :
    Function.Injective (linComb w) := by
  intro c c' h
  have h1 : ∑ i, (c - c') i • w i = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 h
  funext i
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hw _ h1 i)

open Classical in
noncomputable def coordsOf {k : ℕ} (w : Fin k → V) (z : V) : Fin k → ZMod 2 :=
  if h : ∃ c, linComb w c = z then h.choose else 0

theorem linComb_coordsOf {k : ℕ} {w : Fin k → V} {z : V}
    (hz : z ∈ Submodule.span (ZMod 2) (Set.range w)) : linComb w (coordsOf w z) = z := by
  have h : ∃ c, linComb w c = z := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hz
    exact ⟨c, hc⟩
  rw [coordsOf, dite_eq_left h]
  exact h.choose_spec

theorem aeval_polyOfFin_eq_linComb {k : ℕ} {M : Mat} (c : Fin k → ZMod 2) :
    aeval M (polyOfFin c) *ᵥ ones n (ZMod 2) = linComb (kseq k M) c := by
  rw [aeval_polyOfFin_mulVec]
  rfl

theorem muVec_eq_of_fiber {k : ℕ} {M : Mat} (hw : LinearIndependent (ZMod 2) (kseq k M))
    {c : Fin k → ZMod 2} (hz : M ^ k *ᵥ ones n (ZMod 2) = linComb (kseq k M) c) :
    muVec M (ones n (ZMod 2)) = X ^ k - polyOfFin c := by
  have h1 : muVec M (ones n (ZMod 2)) ∣ X ^ k - polyOfFin c := by
    rw [muVec_dvd_iff, map_sub, sub_mulVec, map_pow, aeval_X, aeval_polyOfFin_eq_linComb, hz,
      sub_self]
  have hdeg : (muVec M (ones n (ZMod 2))).natDegree = k :=
    (natDegree_muVec_eq_iff M k).2 ⟨hw, by rw [hz]; exact linComb_mem_span _ _⟩
  exact (eq_of_monic_of_dvd_of_natDegree_le (muVec_monic _ _) (monic_X_pow_sub_polyOfFin c) h1
    (by rw [natDegree_X_pow_sub_polyOfFin, hdeg])).symm

theorem linComb_mem_orthC_iff {k : ℕ} {M : Mat} (hM : IsAlt M) (c : Fin (k + 1) → ZMod 2) :
    linComb (kseq (k + 1) M) c ∈ orthC (Submodule.span (ZMod 2) (Set.range (kseq (k + 1) M))) ↔
      (n % 2 = 1 → c 0 = 0) := by
  rw [mem_orthC_span_iff]
  have hdot : ∀ j : Fin (k + 1), kseq (k + 1) M j ⬝ᵥ linComb (kseq (k + 1) M) c =
      if (j : ℕ) = 0 then c 0 * n else 0 := by
    intro j
    rw [linComb, dotProduct_sum]
    split_ifs with hj
    · have hj' : j = 0 := Fin.ext hj
      subst hj'
      rw [Finset.sum_eq_single 0]
      · rw [dotProduct_smul, smul_eq_mul]
        have : kseq (k + 1) M 0 ⬝ᵥ kseq (k + 1) M 0 = n := by simp [kseq, ones, dotProduct]
        rw [this]
      · intro i _ hi
        rw [dotProduct_smul, kseq_dot hM 0 i (Or.inr (fun h => hi (Fin.ext h))), smul_zero]
      · simp
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [dotProduct_smul, kseq_dot hM j i (Or.inl hj), smul_zero]
  simp_rw [hdot]
  constructor
  · intro h hodd
    have := h 0
    simp only [Fin.val_zero, ite_true] at this
    have hn : (n : ZMod 2) = 1 := by rw [← ZMod.natCast_mod, hodd, Nat.cast_one]
    rwa [hn, mul_one] at this
  · intro h j
    split_ifs with hj
    · rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · rw [(ZMod.natCast_eq_zero_iff n 2).2 (Nat.dvd_of_mod_eq_zero h0), mul_zero]
      · rw [h h1, zero_mul]
    · rfl

theorem natCard_eq_sum_range {α : Type*} [Finite α] (P : α → Prop) (f : α → ℕ) (N : ℕ)
    (hf : ∀ a, P a → f a ≤ N) :
    Nat.card {a // P a} = ∑ k ∈ Finset.range (N + 1), Nat.card {a // P a ∧ f a = k} := by
  rw [natCard_subtype_eq_sum P (fun a => (⟨min (f a) N, by omega⟩ : Fin (N + 1))),
    ← Fin.sum_univ_eq_sum_range (fun k => Nat.card {a // P a ∧ f a = k})]
  refine Finset.sum_congr rfl fun k _ => Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  constructor
  · rintro ⟨hP, hk⟩
    refine ⟨hP, ?_⟩
    have := congrArg Fin.val hk
    simp only at this
    have := hf a hP
    omega
  · rintro ⟨hP, hk⟩
    refine ⟨hP, Fin.ext ?_⟩
    simp only
    have := hf a hP
    omega

theorem natDegree_muVec_le (M : Mat) : (muVec M (ones n (ZMod 2))).natDegree ≤ n := by
  have h := natDegree_le_of_dvd
    ((muVec_dvd_iff M (ones n (ZMod 2))).2 (by rw [aeval_self_charpoly, zero_mulVec]))
    M.charpoly_monic.ne_zero
  rwa [charpoly_natDegree_eq_dim, Fintype.card_fin] at h

theorem cyc_eq_span_kseq (M : Mat) :
    cyc M (ones n (ZMod 2)) = Submodule.span (ZMod 2)
      (Set.range (kseq (muVec M (ones n (ZMod 2))).natDegree M)) := by
  have hle : Submodule.span (ZMod 2) (Set.range (kseq (muVec M (ones n (ZMod 2))).natDegree M)) ≤
      cyc M (ones n (ZMod 2)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have := aeval_mulVec_mem_cyc M (ones n (ZMod 2)) (X ^ (i : ℕ))
    rwa [map_pow, aeval_X] at this
  have hind : LinearIndependent (ZMod 2) (kseq (muVec M (ones n (ZMod 2))).natDegree M) :=
    (linearIndependent_kseq_iff M _).2 le_rfl
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_eq_card hind, Fintype.card_fin, finrank_cyc]

theorem coordsOf_linComb {k : ℕ} {w : Fin k → V} (hw : LinearIndependent (ZMod 2) w)
    (c : Fin k → ZMod 2) : coordsOf w (linComb w c) = c :=
  linComb_injective hw (linComb_coordsOf (linComb_mem_span w c))

theorem k0_coords_iff {k : ℕ} {M : Mat} {w : Fin k → V} (hw : LinearIndependent (ZMod 2) w)
    (hMw : kseq k M = w) (c : Fin k → ZMod 2) :
    ((muVec M (ones n (ZMod 2))).natDegree = k ∧ coordsOf w (M ^ k *ᵥ ones n (ZMod 2)) = c) ↔
      M ^ k *ᵥ ones n (ZMod 2) = linComb w c := by
  rw [natDegree_muVec_eq_iff, hMw]
  constructor
  · rintro ⟨⟨-, hmem⟩, hc⟩
    rw [← hc, linComb_coordsOf hmem]
  · intro h
    exact ⟨⟨hw, by rw [h]; exact linComb_mem_span w c⟩, by rw [h, coordsOf_linComb hw]⟩

theorem fiber_muVec_iff {k : ℕ} {w : Fin (k + 1) → V} (hw : LinearIndependent (ZMod 2) w)
    (c : Fin (k + 1) → ZMod 2) (M : Mat) :
    ((IsAlt M ∧ kseq (k + 1) M = w) ∧ muVec M (ones n (ZMod 2)) = X ^ (k + 1) - polyOfFin c) ↔
      (IsAlt M ∧ kseq (k + 1 + 1) M = Fin.snoc w (linComb w c)) := by
  rw [kseq_succ_eq_iff]
  constructor
  · rintro ⟨⟨hM, hMw⟩, hμ⟩
    refine ⟨hM, hMw, ?_⟩
    have h := aeval_muVec M (ones n (ZMod 2))
    rw [hμ, map_sub, sub_mulVec, map_pow, aeval_X, aeval_polyOfFin_eq_linComb, hMw,
      sub_eq_zero] at h
    exact h
  · rintro ⟨hM, hMw, hz⟩
    refine ⟨⟨hM, hMw⟩, ?_⟩
    have hw' : LinearIndependent (ZMod 2) (kseq (k + 1) M) := by rw [hMw]; exact hw
    have hz' : M ^ (k + 1) *ᵥ ones n (ZMod 2) = linComb (kseq (k + 1) M) c := by rw [hMw]; exact hz
    exact muVec_eq_of_fiber hw' hz'

theorem lem_krylovlaw_c {k : ℕ} {w : Fin (k + 1) → V} (hw : LinearIndependent (ZMod 2) w)
    {c c' : Fin (k + 1) → ZMod 2} (hc : n % 2 = 1 → c 0 = 0) (hc' : n % 2 = 1 → c' 0 = 0) :
    Nat.card {M : Mat // (IsAlt M ∧ kseq (k + 1) M = w) ∧
        muVec M (ones n (ZMod 2)) = X ^ (k + 1) - polyOfFin c} =
      Nat.card {M : Mat // (IsAlt M ∧ kseq (k + 1) M = w) ∧
        muVec M (ones n (ZMod 2)) = X ^ (k + 1) - polyOfFin c'} := by
  have e1 : ∀ c : Fin (k + 1) → ZMod 2, Nat.card {M : Mat // (IsAlt M ∧ kseq (k + 1) M = w) ∧
      muVec M (ones n (ZMod 2)) = X ^ (k + 1) - polyOfFin c} = kcount (k + 1 + 1) (Fin.snoc w (linComb w c)) := by
    intro c
    unfold kcount
    exact Nat.card_congr (Equiv.subtypeEquivRight fun M => fiber_muVec_iff hw c M)
  rw [e1, e1]
  by_cases hne : Nonempty {M : Mat // IsAlt M ∧ kseq (k + 1) M = w}
  · obtain ⟨⟨M₁, hM₁, rfl⟩⟩ := hne
    refine Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos (n - (k + 1))) ?_
    rw [lem_krylov hw, lem_krylov hw, ite_eq_left ((linComb_mem_orthC_iff hM₁ c).2 hc),
      ite_eq_left ((linComb_mem_orthC_iff hM₁ c').2 hc')]
  · rw [not_nonempty_iff] at hne
    have h0 : ∀ z, kcount (k + 1 + 1) (Fin.snoc w z) = 0 := by
      intro z
      have : IsEmpty {M : Mat // IsAlt M ∧ kseq (k + 1 + 1) M = Fin.snoc w z} :=
        ⟨fun M => hne.false ⟨M.1, M.2.1, (kseq_succ_eq_iff.1 M.2.2).1⟩⟩
      exact Nat.card_of_isEmpty
    rw [h0, h0]

section Step3

variable {β : (ZMod 2)[X]} (hβm : β.Monic) (hβ : Irreducible β)
include hβm hβ

omit hβm hβ in
theorem step3_fiber_c_zero {k : ℕ} {w : Fin (k + 1) → V} (hw : LinearIndependent (ZMod 2) w)
    (c : Fin (k + 1) → ZMod 2) (hdvd : ¬ β ∣ X ^ (k + 1) - polyOfFin c) :
    Nat.card {M : Mat // (IsAlt M ∧ kseq (k + 1 + 1) M = Fin.snoc w (linComb w c)) ∧ ZEv M β} = 0 := by
  have : IsEmpty {M : Mat // (IsAlt M ∧ kseq (k + 1 + 1) M = Fin.snoc w (linComb w c)) ∧ ZEv M β} := by
    refine ⟨fun M => hdvd ?_⟩
    obtain ⟨h1, h2⟩ := kseq_succ_eq_iff.1 M.2.1.2
    have := M.2.2.1
    have hw' : LinearIndependent (ZMod 2) (kseq (k + 1) M.1) := by rw [h1]; exact hw
    have h2' : M.1 ^ (k + 1) *ᵥ ones n (ZMod 2) = linComb (kseq (k + 1) M.1) c := by
      rw [h1]; exact h2
    rwa [muVec_eq_of_fiber hw' h2'] at this
  exact Nat.card_of_isEmpty

theorem step3_fiber_c (hn : 1 ≤ n) {k : ℕ} {w : Fin (k + 1) → V}
    (hw : LinearIndependent (ZMod 2) w)
    (hB : ¬ BadK (Submodule.span (ZMod 2) (Set.range w))) (c : Fin (k + 1) → ZMod 2)
    (hdvd : β ∣ X ^ (k + 1) - polyOfFin c) :
    Nat.card {M : Mat // (IsAlt M ∧ kseq (k + 1 + 1) M = Fin.snoc w (linComb w c)) ∧ ZEv M β} *
        2 ^ (β.natDegree - 1) ≤ kcount (k + 1 + 1) (Fin.snoc w (linComb w c)) := by
  by_cases hne : Nonempty {M : Mat // IsAlt M ∧ kseq (k + 1 + 1) M = Fin.snoc w (linComb w c)}
  · obtain ⟨⟨M₀, hM₀, hM₀w⟩⟩ := hne
    obtain ⟨h1, h2⟩ := kseq_succ_eq_iff.1 hM₀w
    have hw' := hw
    rw [← h1] at hw' h2
    have hμ₀ := muVec_eq_of_fiber hw' h2
    have hK : cyc M₀ (ones n (ZMod 2)) = Submodule.span (ZMod 2) (Set.range w) := by
      rw [cyc_eq_span_kseq, hμ₀, natDegree_X_pow_sub_polyOfFin, h1]
    have hcoset : ∀ M, (IsAlt M ∧ kseq (k + 1 + 1) M = Fin.snoc w (linComb w c)) ↔
        M - M₀ ∈ altKill (cyc M₀ (ones n (ZMod 2))) := by
      intro M
      rw [fiber_eq_coset hM₀ hM₀w M, Fin.init_snoc, hK]
    have h2c := step2_count hM₀ hβm hβ (by rw [hμ₀]; exact hdvd) hn (by rw [hK]; exact hB)
    have e1 : Nat.card {M : Mat // (IsAlt M ∧ kseq (k + 1 + 1) M = Fin.snoc w (linComb w c)) ∧
          ZEv M β} =
        Nat.card {M : Mat // M - M₀ ∈ altKill (cyc M₀ (ones n (ZMod 2))) ∧ ZEv M β} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun M => by rw [hcoset M])
    have e2 : kcount (k + 1 + 1) (Fin.snoc w (linComb w c)) =
        Nat.card {M : Mat // M - M₀ ∈ altKill (cyc M₀ (ones n (ZMod 2)))} := by
      unfold kcount
      exact Nat.card_congr (Equiv.subtypeEquivRight fun M => hcoset M)
    rw [e1, e2]
    exact h2c
  · rw [not_nonempty_iff] at hne
    have : IsEmpty {M : Mat // (IsAlt M ∧ kseq (k + 1 + 1) M = Fin.snoc w (linComb w c)) ∧
        ZEv M β} := ⟨fun M => hne.false ⟨M.1, M.2.1⟩⟩
    rw [Nat.card_of_isEmpty, zero_mul]
    exact Nat.zero_le _

theorem card_dvd_par (hβX : β ≠ X) (k : ℕ) :
    Nat.card {c : Fin (k + 1) → ZMod 2 //
        (n % 2 = 1 → c 0 = 0) ∧ β ∣ X ^ (k + 1) - polyOfFin c} * 2 ^ β.natDegree ≤
      2 ^ (k + 1 - n % 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · have hexp : k + 1 - n % 2 = k + 1 := by omega
    have e : Nat.card {c : Fin (k + 1) → ZMod 2 //
          (n % 2 = 1 → c 0 = 0) ∧ β ∣ X ^ (k + 1) - polyOfFin c} =
        Nat.card {c : Fin (k + 1) → ZMod 2 // β ∣ X ^ (k + 1) - polyOfFin c} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        ⟨fun h => h.2, fun h => ⟨fun h' => absurd h' (by omega), h⟩⟩)
    rw [e, hexp]
    exact card_dvd_even hβm (k + 1)
  · have hexp : k + 1 - n % 2 = k := by omega
    have e : Nat.card {c : Fin (k + 1) → ZMod 2 //
          (n % 2 = 1 → c 0 = 0) ∧ β ∣ X ^ (k + 1) - polyOfFin c} =
        Nat.card {c : Fin (k + 1) → ZMod 2 //
          c ⟨0, Nat.succ_pos k⟩ = 0 ∧ β ∣ X ^ (k + 1) - polyOfFin c} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        ⟨fun h => ⟨h.1 h1, h.2⟩, fun h => ⟨fun _ => h.1, h.2⟩⟩)
    rw [e, hexp]
    have := card_dvd_odd hβm hβ hβX (k := k + 1) (Nat.succ_pos k)
    rwa [Nat.add_sub_cancel] at this

omit hβm hβ in
theorem card_par_ge (k : ℕ) :
    2 ^ (k + 1 - n % 2) ≤ Nat.card {c : Fin (k + 1) → ZMod 2 // (n % 2 = 1 → c 0 = 0)} := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · have hexp : k + 1 - n % 2 = k + 1 := by omega
    rw [hexp]
    have hinj : Function.Injective fun c : Fin (k + 1) → ZMod 2 =>
        (⟨c, fun h => absurd h (by omega)⟩ :
          {c : Fin (k + 1) → ZMod 2 // (n % 2 = 1 → c 0 = 0)}) :=
      fun c c' h => congrArg Subtype.val h
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin (k + 1)),
      Fintype.card_fin] at this
  · have hexp : k + 1 - n % 2 = k := by omega
    rw [hexp]
    have hinj : Function.Injective fun c : Fin k → ZMod 2 =>
        (⟨Fin.cons 0 c, fun _ => Fin.cons_zero _ _⟩ :
          {c : Fin (k + 1) → ZMod 2 // (n % 2 = 1 → c 0 = 0)}) := by
      intro c c' h
      have h' := congrArg
        (fun x : {c : Fin (k + 1) → ZMod 2 // (n % 2 = 1 → c 0 = 0)} => Fin.tail x.1) h
      simpa only [Fin.tail_cons] using h'
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin k),
      Fintype.card_fin] at this

theorem step3_fiber (hn : 1 ≤ n) (hβX : β ≠ X) {k : ℕ} (w : Fin (k + 1) → V) :
    Nat.card {M : Mat // ((IsAlt M ∧ ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2)))) ∧
        (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧ kseq (k + 1) M = w} *
        2 ^ (2 * β.natDegree - 1) ≤
      Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
        kseq (k + 1) M = w} := by
  have hd1 : 1 ≤ β.natDegree := hβ.natDegree_pos
  by_cases hw : LinearIndependent (ZMod 2) w
  swap
  · have : IsEmpty {M : Mat // ((IsAlt M ∧ ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2)))) ∧
        (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧ kseq (k + 1) M = w} := by
      refine ⟨fun M => hw ?_⟩
      rw [← M.2.2]
      exact ((natDegree_muVec_eq_iff M.1 (k + 1)).1 M.2.1.2).1
    rw [Nat.card_of_isEmpty, zero_mul]
    exact Nat.zero_le _
  by_cases hB : BadK (Submodule.span (ZMod 2) (Set.range w))
  · have : IsEmpty {M : Mat // ((IsAlt M ∧ ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2)))) ∧
        (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧ kseq (k + 1) M = w} := by
      refine ⟨fun M => M.2.1.1.2.2 ?_⟩
      rw [cyc_eq_span_kseq, M.2.1.2, M.2.2]
      exact hB
    rw [Nat.card_of_isEmpty, zero_mul]
    exact Nat.zero_le _
  rw [natCard_subtype_eq_sum (fun M : Mat => ((IsAlt M ∧ ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2)))) ∧
        (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧ kseq (k + 1) M = w)
      (fun M : Mat => coordsOf w (M ^ (k + 1) *ᵥ ones n (ZMod 2))),
    natCard_subtype_eq_sum (fun M : Mat => (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
        kseq (k + 1) M = w) (fun M : Mat => coordsOf w (M ^ (k + 1) *ᵥ ones n (ZMod 2)))]
  have eZ : ∀ c, Nat.card {M : Mat // (((IsAlt M ∧ ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2)))) ∧
        (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧ kseq (k + 1) M = w) ∧
        coordsOf w (M ^ (k + 1) *ᵥ ones n (ZMod 2)) = c} =
      Nat.card {M : Mat // (IsAlt M ∧ kseq (k + 1 + 1) M = Fin.snoc w (linComb w c)) ∧ ZEv M β} := by
    intro c
    refine Nat.card_congr (Equiv.subtypeEquivRight fun M => ?_)
    rw [kseq_succ_eq_iff]
    constructor
    · rintro ⟨⟨⟨⟨hM, hZ, -⟩, hk⟩, hMw⟩, hc⟩
      exact ⟨⟨hM, hMw, (k0_coords_iff hw hMw c).1 ⟨hk, hc⟩⟩, hZ⟩
    · rintro ⟨⟨hM, hMw, hz⟩, hZ⟩
      have h := (k0_coords_iff hw hMw c).2 hz
      refine ⟨⟨⟨⟨hM, hZ, ?_⟩, h.1⟩, hMw⟩, h.2⟩
      rw [cyc_eq_span_kseq, h.1, hMw]
      exact hB
  have eA : ∀ c, Nat.card {M : Mat // ((IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
        kseq (k + 1) M = w) ∧ coordsOf w (M ^ (k + 1) *ᵥ ones n (ZMod 2)) = c} =
      kcount (k + 1 + 1) (Fin.snoc w (linComb w c)) := by
    intro c
    unfold kcount
    refine Nat.card_congr (Equiv.subtypeEquivRight fun M => ?_)
    rw [kseq_succ_eq_iff]
    constructor
    · rintro ⟨⟨⟨hM, hk⟩, hMw⟩, hc⟩
      exact ⟨hM, hMw, (k0_coords_iff hw hMw c).1 ⟨hk, hc⟩⟩
    · rintro ⟨hM, hMw, hz⟩
      have h := (k0_coords_iff hw hMw c).2 hz
      exact ⟨⟨⟨hM, h.1⟩, hMw⟩, h.2⟩
  simp_rw [eZ, eA]
  have hAc : ∀ c : Fin (k + 1) → ZMod 2,
      kcount (k + 1 + 1) (Fin.snoc w (linComb w c)) * 2 ^ (n - (k + 1)) =
        if (n % 2 = 1 → c 0 = 0) then kcount (k + 1) w else 0 := by
    intro c
    rw [lem_krylov hw]
    by_cases hK : kcount (k + 1) w = 0
    · rw [hK]
      split_ifs <;> rfl
    · obtain ⟨⟨M₁, hM₁, hM₁w⟩⟩ : Nonempty {M : Mat // IsAlt M ∧ kseq (k + 1) M = w} := by
        by_contra h
        rw [not_nonempty_iff] at h
        exact hK Nat.card_of_isEmpty
      subst hM₁w
      by_cases hv : (n % 2 = 1 → c 0 = 0)
      · rw [ite_eq_left ((linComb_mem_orthC_iff hM₁ c).2 hv), ite_eq_left hv]
      · rw [ite_eq_right (fun h => hv ((linComb_mem_orthC_iff hM₁ c).1 h)), ite_eq_right hv]
  have h3 := card_dvd_par (n := n) hβm hβ hβX k
  have h4 := card_par_ge (n := n) k
  set d := β.natDegree with hd
  set Kw := kcount (k + 1) w with hKw
  classical
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.two_pow_pos (n - (k + 1)))
  calc (∑ c, Nat.card {M : Mat // (IsAlt M ∧ kseq (k + 1 + 1) M = Fin.snoc w (linComb w c)) ∧
          ZEv M β}) * 2 ^ (2 * d - 1) * 2 ^ (n - (k + 1))
      = ∑ c, Nat.card {M : Mat // (IsAlt M ∧ kseq (k + 1 + 1) M = Fin.snoc w (linComb w c)) ∧
          ZEv M β} * 2 ^ (d - 1) * (2 ^ d * 2 ^ (n - (k + 1))) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        have : 2 * d - 1 = (d - 1) + d := by omega
        rw [this, pow_add]
        ring
    _ ≤ ∑ c : Fin (k + 1) → ZMod 2,
          (if (n % 2 = 1 → c 0 = 0) ∧ β ∣ X ^ (k + 1) - polyOfFin c then Kw * 2 ^ d else 0) := by
        refine Finset.sum_le_sum fun c _ => ?_
        by_cases hdc : β ∣ X ^ (k + 1) - polyOfFin c
        · have h1 := Nat.mul_le_mul_right (2 ^ d * 2 ^ (n - (k + 1))) (step3_fiber_c hβm hβ hn hw hB c hdc)
          refine h1.trans (le_of_eq ?_)
          have h2 := hAc c
          calc kcount (k + 1 + 1) (Fin.snoc w (linComb w c)) * (2 ^ d * 2 ^ (n - (k + 1)))
              = kcount (k + 1 + 1) (Fin.snoc w (linComb w c)) * 2 ^ (n - (k + 1)) * 2 ^ d := by ring
            _ = _ := by
              rw [h2]
              by_cases hv : (n % 2 = 1 → c 0 = 0)
              · rw [ite_eq_left hv, ite_eq_left ⟨hv, hdc⟩]
              · rw [ite_eq_right hv, ite_eq_right (fun h => hv h.1), zero_mul]
        · rw [step3_fiber_c_zero hw c hdc, zero_mul, zero_mul]
          exact Nat.zero_le _
    _ = Nat.card {c : Fin (k + 1) → ZMod 2 //
          (n % 2 = 1 → c 0 = 0) ∧ β ∣ X ^ (k + 1) - polyOfFin c} * 2 ^ d * Kw := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
          Nat.card_eq_fintype_card, Fintype.card_subtype]
        ring
    _ ≤ 2 ^ (k + 1 - n % 2) * Kw := Nat.mul_le_mul_right _ h3
    _ ≤ Nat.card {c : Fin (k + 1) → ZMod 2 // (n % 2 = 1 → c 0 = 0)} * Kw :=
        Nat.mul_le_mul_right _ h4
    _ = ∑ c : Fin (k + 1) → ZMod 2, (if (n % 2 = 1 → c 0 = 0) then Kw else 0) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
          Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = ∑ c, kcount (k + 1 + 1) (Fin.snoc w (linComb w c)) * 2 ^ (n - (k + 1)) :=
        Finset.sum_congr rfl fun c _ => (hAc c).symm
    _ = (∑ c, kcount (k + 1 + 1) (Fin.snoc w (linComb w c))) * 2 ^ (n - (k + 1)) :=
        (Finset.sum_mul _ _ _).symm

theorem step3_count (hn : 1 ≤ n) (hβX : β ≠ X) :
    Nat.card {M : Mat // IsAlt M ∧ ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2)))} *
        2 ^ (2 * β.natDegree - 1) ≤ Nat.card {M : Mat // IsAlt M} := by
  rw [natCard_eq_sum_range (fun M : Mat => IsAlt M ∧ ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2))))
      (fun M : Mat => (muVec M (ones n (ZMod 2))).natDegree) n (fun M _ => natDegree_muVec_le M),
    natCard_eq_sum_range (fun M : Mat => IsAlt M) (fun M : Mat => (muVec M (ones n (ZMod 2))).natDegree)
      n (fun M _ => natDegree_muVec_le M), Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rcases k with - | k
  · have : IsEmpty {M : Mat // (IsAlt M ∧ ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2)))) ∧
        (muVec M (ones n (ZMod 2))).natDegree = 0} :=
      ⟨fun M => by have h1 := one_le_natDegree_muVec hn M.1; have h2 := M.2.2; omega⟩
    rw [Nat.card_of_isEmpty, zero_mul]
    exact Nat.zero_le _
  · rw [natCard_subtype_eq_sum (fun M : Mat => (IsAlt M ∧ ZEv M β ∧ ¬ BadK (cyc M (ones n (ZMod 2)))) ∧
        (muVec M (ones n (ZMod 2))).natDegree = k + 1) (kseq (k + 1)),
      natCard_subtype_eq_sum (fun M : Mat => IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1)
        (kseq (k + 1)), Finset.sum_mul]
    exact Finset.sum_le_sum fun w _ => step3_fiber hβm hβ hn hβX w

end Step3

end DGS
