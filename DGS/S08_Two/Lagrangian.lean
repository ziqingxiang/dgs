module

public import DGS.S08_Two.Flags

@[expose] public section

open Matrix Polynomial Module

namespace DGS

variable {n : ℕ}

local notation "V" => Fin n → ZMod 2

instance finite_submodule_fin : Finite (Submodule (ZMod 2) (Fin n → ZMod 2)) :=
  Finite.of_injective (fun L : Submodule (ZMod 2) (Fin n → ZMod 2) => (L : Set (Fin n → ZMod 2)))
    SetLike.coe_injective

section SeqValidIff

variable {X : Type*} [Finite X] (Ch : (i : ℕ) → (Fin i → X) → Set X)

omit [Finite X] in
theorem seqValid_iff {m : ℕ} (u : Fin m → X) :
    SeqValid Ch m u ↔ ∀ i : Fin m, u i ∈ Ch i (pre i i.2.le u) := by
  induction m with
  | zero => exact ⟨fun _ i => i.elim0, fun _ => trivial⟩
  | succ m ih =>
    show SeqValid Ch m (Fin.init u) ∧ u (Fin.last m) ∈ Ch m (Fin.init u) ↔ _
    rw [ih (Fin.init u), Fin.forall_fin_succ']
    exact Iff.rfl

end SeqValidIff

def kap (S : Finset (Fin n)) : ℕ := (S.card + 1) / 2

def IsMaxIso (S : Finset (Fin n)) (L : Submodule (ZMod 2) V) : Prop :=
  L ≤ coordSub S ∧ (∀ x ∈ L, ∀ y ∈ L, x ⬝ᵥ y = 0) ∧ finrank (ZMod 2) L = S.card / 2

def radL {m : ℕ} (u : Fin m → V) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (Set.range u) ⊓ orthC (Submodule.span (ZMod 2) (Set.range u))

theorem finrank_iso_le {S : Finset (Fin n)} {U : Submodule (ZMod 2) V} (hU : U ≤ coordSub S)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, x ⬝ᵥ y = 0) : finrank (ZMod 2) U ≤ S.card / 2 := by
  have h1 : U ≤ orthC U ⊓ coordSub S := fun x hx => ⟨fun w hw => hiso w hw x hx, hU hx⟩
  have h2 := Submodule.finrank_mono h1
  rw [finrank_orthC_inf_coordSub hU] at h2
  omega

theorem isMaxIso_radL {S : Finset (Fin n)} (hS : S.Nonempty) {m : ℕ} (hm : m = kap S)
    {u : Fin m → V} (hu : IsFlag S m u) : IsMaxIso S (radL u) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := hS.card_pos; unfold kap at hm; omega⟩
  obtain ⟨-, hmem, -, -⟩ := hu.prop hS
  refine ⟨inf_le_left.trans ?_, fun x hx y hy => (mem_orthC.1 hy.2) x hx.1, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  · rw [radL, finrank_radical_flag hS hu]
    unfold kap at hm
    omega

theorem indS_dot_eq_zero {S : Finset (Fin n)} {L : Submodule (ZMod 2) V} (hL : IsMaxIso S L) {x : V}
    (hx : x ∈ L) : indS S ⬝ᵥ x = 0 := by
  rw [← dot_self_eq_indS_dot (hL.1 hx)]
  exact hL.2.1 x hx x hx

theorem indS_mem_of_even {S : Finset (Fin n)} {L : Submodule (ZMod 2) V} (hL : IsMaxIso S L)
    (heven : S.card % 2 = 0) : indS S ∈ L := by
  have h1 : L ≤ orthC L ⊓ coordSub S := fun x hx => ⟨fun w hw => hL.2.1 w hw x hx, hL.1 hx⟩
  have h2 : finrank (ZMod 2) L = finrank (ZMod 2) (orthC L ⊓ coordSub S : Submodule (ZMod 2) V) := by
    rw [finrank_orthC_inf_coordSub hL.1, hL.2.2]
    omega
  have h3 := Submodule.eq_of_le_of_finrank_eq h1 h2
  rw [h3]
  refine ⟨fun w hw => ?_, indS_mem S⟩
  rw [dotProduct_comm]
  exact indS_dot_eq_zero hL hw

def ChL (S : Finset (Fin n)) (L : Submodule (ZMod 2) V) : (i : ℕ) → (Fin i → V) → Set V
  | 0, _ => {indS S}
  | _ + 1, p => {y | y ∈ L ∧ y ∉ Submodule.span (ZMod 2) (Set.range p)}

theorem ChL_valid_prop {S : Finset (Fin n)} {L : Submodule (ZMod 2) V} (hL : IsMaxIso S L) {m : ℕ}
    {u : Fin m → V} (hu : SeqValid (ChL S L) m u) :
    IsFlag S m u ∧ ∀ j : Fin m, (j : ℕ) ≠ 0 → u j ∈ L := by
  rw [seqValid_iff] at hu
  have hL' : ∀ j : Fin m, (j : ℕ) ≠ 0 → u j ∈ L := by
    rintro ⟨_ | j, hj⟩ h0
    · exact absurd rfl h0
    · exact (hu ⟨j + 1, hj⟩).1
  have h0 : ∀ j : Fin m, (j : ℕ) = 0 → u j = indS S := by
    rintro ⟨_ | j, hj⟩ h0
    · exact hu ⟨0, hj⟩
    · exact absurd h0 (Nat.succ_ne_zero j)
  refine ⟨(seqValid_iff _ u).2 ?_, hL'⟩
  rintro ⟨_ | i, hi⟩
  · exact hu ⟨0, hi⟩
  · obtain ⟨h1, h2⟩ := hu ⟨i + 1, hi⟩
    refine ⟨hL.1 h1, ?_, h2⟩
    rw [mem_orthC_span_iff]
    intro j
    simp only [pre]
    by_cases hj : (j : ℕ) = 0
    · rw [h0 _ hj, indS_dot_eq_zero hL h1]
    · exact hL.2.1 _ (hL' _ hj) _ h1

theorem ChL_valid_of_flag {S : Finset (Fin n)} {L : Submodule (ZMod 2) V} {m : ℕ} {u : Fin m → V}
    (hu : IsFlag S m u) (hL : ∀ j : Fin m, (j : ℕ) ≠ 0 → u j ∈ L) : SeqValid (ChL S L) m u := by
  have hu' : SeqValid (flagCh S) m u := hu
  rw [seqValid_iff] at hu' ⊢
  rintro ⟨_ | i, hi⟩
  · exact hu' ⟨0, hi⟩
  · exact ⟨hL ⟨i + 1, hi⟩ (Nat.succ_ne_zero i), (hu' ⟨i + 1, hi⟩).2.2⟩

theorem mem_radL_of_ne_zero {S : Finset (Fin n)} (hS : S.Nonempty) {m : ℕ} {u : Fin m → V}
    (hu : IsFlag S m u) (j : Fin m) (hj : (j : ℕ) ≠ 0) : u j ∈ radL u := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := j.2; omega⟩
  obtain ⟨-, -, -, horth⟩ := hu.prop hS
  refine Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨j, rfl⟩, ?_⟩
  rw [mem_orthC_span_iff]
  intro i
  exact horth i j (Or.inr hj)

theorem radL_eq_of_mem {S : Finset (Fin n)} (hS : S.Nonempty) {L : Submodule (ZMod 2) V}
    (hL : IsMaxIso S L) {m : ℕ} (hm : m = kap S) {u : Fin m → V} (hu : IsFlag S m u)
    (huL : ∀ j : Fin m, (j : ℕ) ≠ 0 → u j ∈ L) : radL u = L := by
  have hrad := isMaxIso_radL hS hm hu
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := hS.card_pos; unfold kap at hm; omega⟩
  obtain ⟨h0, -, hind, -⟩ := hu.prop hS
  have hle : L ≤ radL u := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rcases Nat.mod_two_eq_zero_or_one S.card with he | ho
      ·
        have hsub : Submodule.span (ZMod 2) (Set.range u) ≤ L := by
          rw [Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          by_cases hj : (j : ℕ) = 0
          · have : j = 0 := Fin.ext hj
            rw [this, h0]
            exact indS_mem_of_even hL he
          · exact huL j hj
        have heq := Submodule.eq_of_le_of_finrank_eq hsub (by
          rw [finrank_span_eq_card hind, Fintype.card_fin, hL.2.2]
          unfold kap at hm
          omega)
        rw [heq]
        exact hx
      ·
        have hind' : LinearIndependent (ZMod 2) (Fin.tail u) := hind.comp _ (Fin.succ_injective _)
        have hsub : Submodule.span (ZMod 2) (Set.range (Fin.tail u)) ≤ L := by
          rw [Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          exact huL j.succ (Nat.succ_ne_zero _)
        have heq := Submodule.eq_of_le_of_finrank_eq hsub (by
          rw [finrank_span_eq_card hind', Fintype.card_fin, hL.2.2]
          unfold kap at hm
          omega)
        rw [← heq] at hx
        exact Submodule.span_mono
          (Set.range_subset_iff.2 fun j => ⟨j.succ, rfl⟩ : Set.range (Fin.tail u) ⊆ Set.range u) hx
    · rw [mem_orthC_span_iff]
      intro j
      by_cases hj : (j : ℕ) = 0
      · have : j = 0 := Fin.ext hj
        rw [this, h0]
        exact indS_dot_eq_zero hL hx
      · exact hL.2.1 _ (huL j hj) _ hx
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hrad.2.2, hL.2.2])).symm

theorem flag_radL_iff {S : Finset (Fin n)} (hS : S.Nonempty) {L : Submodule (ZMod 2) V}
    (hL : IsMaxIso S L) {m : ℕ} (hm : m = kap S) (u : Fin m → V) :
    (IsFlag S m u ∧ radL u = L) ↔ SeqValid (ChL S L) m u := by
  constructor
  · rintro ⟨hu, hrad⟩
    refine ChL_valid_of_flag hu fun j hj => ?_
    rw [← hrad]
    exact mem_radL_of_ne_zero hS hu j hj
  · intro hu
    obtain ⟨hf, hL'⟩ := ChL_valid_prop hL hu
    exact ⟨hf, radL_eq_of_mem hS hL hm hf hL'⟩

theorem card_ChL {S : Finset (Fin n)} (hS : S.Nonempty) {L : Submodule (ZMod 2) V} (hL : IsMaxIso S L)
    {i : ℕ} {p : Fin (i + 1) → V} (hp : SeqValid (ChL S L) (i + 1) p) :
    Nat.card (ChL S L (i + 1) p) = 2 ^ (S.card / 2) - 2 ^ (i + 1 - S.card % 2) := by
  obtain ⟨hf, hpL⟩ := ChL_valid_prop hL hp
  obtain ⟨h0, -, hind, -⟩ := hf.prop hS
  set K := Submodule.span (ZMod 2) (Set.range p) with hK
  have hdim : finrank (ZMod 2) (L ⊓ K : Submodule (ZMod 2) V) = i + 1 - S.card % 2 := by
    have hup : L ⊓ K ≤ radL p := by
      intro x hx
      refine Submodule.mem_inf.2 ⟨hx.2, ?_⟩
      rw [mem_orthC_span_iff]
      intro j
      by_cases hj : (j : ℕ) = 0
      · have : j = 0 := Fin.ext hj
        rw [this, h0]
        exact indS_dot_eq_zero hL hx.1
      · exact hL.2.1 _ (hpL j hj) _ hx.1
    have h1 := Submodule.finrank_mono hup
    rw [radL, finrank_radical_flag hS hf] at h1
    have h2 : i + 1 - S.card % 2 ≤ finrank (ZMod 2) (L ⊓ K : Submodule (ZMod 2) V) := by
      rcases Nat.mod_two_eq_zero_or_one S.card with he | ho
      · have hsub : K ≤ L ⊓ K := by
          refine le_inf ?_ le_rfl
          rw [hK, Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          by_cases hj : (j : ℕ) = 0
          · have : j = 0 := Fin.ext hj
            rw [this, h0]
            exact indS_mem_of_even hL he
          · exact hpL j hj
        have := Submodule.finrank_mono hsub
        have hKd : finrank (ZMod 2) K = i + 1 := by
          rw [hK, finrank_span_eq_card hind, Fintype.card_fin]
        omega
      · have hind' : LinearIndependent (ZMod 2) (Fin.tail p) := hind.comp _ (Fin.succ_injective _)
        have hsub : Submodule.span (ZMod 2) (Set.range (Fin.tail p)) ≤ L ⊓ K := by
          rw [Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          exact ⟨hpL j.succ (Nat.succ_ne_zero _), Submodule.subset_span ⟨j.succ, rfl⟩⟩
        have := Submodule.finrank_mono hsub
        rw [finrank_span_eq_card hind', Fintype.card_fin] at this
        omega
    omega
  have hset : ChL S L (i + 1) p = (L : Set V) \ ((L ⊓ K : Submodule (ZMod 2) V) : Set V) := by
    ext y
    simp only [ChL, Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Submodule.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 h.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 ⟨h1, h⟩⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_sdiff]
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    change Nat.card L - Nat.card (L ⊓ K : Submodule (ZMod 2) V) = _
    have e1 : Nat.card L = 2 ^ (S.card / 2) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hL.2.2]
    have e2 : Nat.card (L ⊓ K : Submodule (ZMod 2) V) = 2 ^ (i + 1 - S.card % 2) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    rw [e1, e2]
  · intro y hy
    exact hy.1

def aF (S : Finset (Fin n)) (i : ℕ) : ℕ :=
  if i = 0 then 1 else 2 ^ (S.card - i) - 2 ^ (i - S.card % 2)

def bL (S : Finset (Fin n)) (i : ℕ) : ℕ :=
  if i = 0 then 1 else 2 ^ (S.card / 2) - 2 ^ (i - S.card % 2)

theorem card_flagCh_eq {S : Finset (Fin n)} (hS : S.Nonempty) (i : ℕ) (p : Fin i → V)
    (hp : IsFlag S i p) : Nat.card (flagCh S i p) = aF S i := by
  rcases i with - | i
  · show Nat.card ({indS S} : Set V) = aF S 0
    rw [Nat.card_unique]
    rfl
  · rw [card_flagCh hS hp, aF, ite_eq_right (Nat.succ_ne_zero i)]

theorem card_ChL_eq {S : Finset (Fin n)} (hS : S.Nonempty) {L : Submodule (ZMod 2) V}
    (hL : IsMaxIso S L) (i : ℕ) (p : Fin i → V) (hp : SeqValid (ChL S L) i p) :
    Nat.card (ChL S L i p) = bL S i := by
  rcases i with - | i
  · show Nat.card ({indS S} : Set V) = bL S 0
    rw [Nat.card_unique]
    rfl
  · rw [card_ChL hS hL hp, bL, ite_eq_right (Nat.succ_ne_zero i)]

theorem card_flags {S : Finset (Fin n)} (hS : S.Nonempty) (m : ℕ) :
    Nat.card {u : Fin m → V // IsFlag S m u} = ∏ i ∈ Finset.range m, aF S i :=
  card_valid (flagCh S) (aF S) (fun i p hp => card_flagCh_eq hS i p hp) m

theorem card_fiber_radL {S : Finset (Fin n)} (hS : S.Nonempty) {L : Submodule (ZMod 2) V}
    (hL : IsMaxIso S L) {m : ℕ} (hm : m = kap S) :
    Nat.card {u : Fin m → V // IsFlag S m u ∧ radL u = L} = ∏ i ∈ Finset.range m, bL S i := by
  rw [← card_valid (ChL S L) (bL S) (fun i p hp => card_ChL_eq hS hL i p hp) m]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun u => flag_radL_iff hS hL hm u)

theorem card_fiber_radL_pred {S : Finset (Fin n)} (hS : S.Nonempty) {m : ℕ} (hm : m = kap S)
    (P : Submodule (ZMod 2) V → Prop) :
    Nat.card {u : Fin m → V // IsFlag S m u ∧ P (radL u)} =
      Nat.card {L : Submodule (ZMod 2) V // IsMaxIso S L ∧ P L} * ∏ i ∈ Finset.range m, bL S i := by
  have e : {u : Fin m → V // IsFlag S m u ∧ P (radL u)} ≃
      Σ L : {L : Submodule (ZMod 2) V // IsMaxIso S L ∧ P L},
        {u : Fin m → V // IsFlag S m u ∧ radL u = L.1} :=
    { toFun := fun u => ⟨⟨radL u.1, isMaxIso_radL hS hm u.2.1, u.2.2⟩, ⟨u.1, u.2.1, rfl⟩⟩
      invFun := fun x => ⟨x.2.1, x.2.2.1, by rw [x.2.2.2]; exact x.1.2.2⟩
      left_inv := fun u => rfl
      right_inv := fun x => Sigma.subtype_ext (Subtype.ext x.2.2.2) rfl }
  rw [Nat.card_congr e]
  have := Fintype.ofFinite {L : Submodule (ZMod 2) V // IsMaxIso S L ∧ P L}
  rw [Nat.card_sigma]
  have : ∀ L : {L : Submodule (ZMod 2) V // IsMaxIso S L ∧ P L},
      Nat.card {u : Fin m → V // IsFlag S m u ∧ radL u = L.1} = ∏ i ∈ Finset.range m, bL S i :=
    fun L => card_fiber_radL hS L.2.1 hm
  simp_rw [this]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

def theta (t : ℕ) : ℕ := ∏ j ∈ Finset.range t, (2 ^ (j + 1) + 1)

theorem theta_succ (t : ℕ) : theta (t + 1) = theta t * (2 ^ (t + 1) + 1) :=
  Finset.prod_range_succ _ _

theorem aF_eq_bL_mul {S : Finset (Fin n)} {i : ℕ} (hi1 : 1 ≤ i) (hi : i < kap S) :
    aF S i = bL S i * (2 ^ (kap S - i) + 1) := by
  unfold aF bL kap at *
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  set N := S.card with hN
  have e1 : N - i = (i - N % 2) + ((N + 1) / 2 - i) + ((N + 1) / 2 - i) := by omega
  have e2 : N / 2 = (i - N % 2) + ((N + 1) / 2 - i) := by omega
  rw [e1, e2, pow_add, pow_add]
  set x := 2 ^ (i - N % 2) with hx
  set y := 2 ^ ((N + 1) / 2 - i) with hy
  have hy1 : 1 ≤ y := Nat.one_le_two_pow
  have h1 : x ≤ x * y := Nat.le_mul_of_pos_right x hy1
  have h2 : x ≤ x * y * y := h1.trans (Nat.le_mul_of_pos_right _ hy1)
  zify [h1, h2]
  ring

theorem bL_pos {S : Finset (Fin n)} {i : ℕ} (hi : i < kap S) : 0 < bL S i := by
  unfold bL kap at *
  split_ifs with h
  · exact one_pos
  · exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))

theorem card_maxIso {S : Finset (Fin n)} (hS : S.Nonempty) :
    Nat.card {L : Submodule (ZMod 2) V // IsMaxIso S L} = theta (kap S - 1) := by
  have h1 := card_fiber_radL_pred hS (m := kap S) rfl (fun _ => True)
  have e1 : Nat.card {u : Fin (kap S) → V // IsFlag S (kap S) u ∧ True} =
      Nat.card {u : Fin (kap S) → V // IsFlag S (kap S) u} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun u => (and_true _).to_iff)
  have e2 : Nat.card {L : Submodule (ZMod 2) V // IsMaxIso S L ∧ True} =
      Nat.card {L : Submodule (ZMod 2) V // IsMaxIso S L} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun L => (and_true _).to_iff)
  rw [e1, e2, card_flags hS] at h1
  obtain ⟨k, hk⟩ : ∃ k, kap S = k + 1 := ⟨kap S - 1, by unfold kap; have := hS.card_pos; omega⟩
  rw [hk, Finset.prod_range_succ', Finset.prod_range_succ' (bL S)] at h1
  rw [hk, Nat.add_sub_cancel]
  have h2 : ∏ i ∈ Finset.range k, aF S (i + 1) =
      (∏ i ∈ Finset.range k, bL S (i + 1)) * theta k := by
    rw [theta, ← Finset.prod_range_reflect (fun j => 2 ^ (j + 1) + 1) k, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [aF_eq_bL_mul (by omega) (by omega), hk]
    rw [show k + 1 - (i + 1) = k - 1 - i + 1 by omega]
  rw [h2] at h1
  have hpos : 0 < (∏ i ∈ Finset.range k, bL S (i + 1)) * bL S 0 :=
    Nat.mul_pos (Finset.prod_pos fun i hi => bL_pos (by rw [Finset.mem_range] at hi; omega))
      (bL_pos (by omega))
  have ha0 : aF S 0 = bL S 0 := rfl
  rw [ha0] at h1
  have h3 : theta k * ((∏ i ∈ Finset.range k, bL S (i + 1)) * bL S 0) =
      Nat.card {L : Submodule (ZMod 2) V // IsMaxIso S L} *
        ((∏ i ∈ Finset.range k, bL S (i + 1)) * bL S 0) := by
    rw [← h1]
    ring
  exact (Nat.eq_of_mul_eq_mul_right hpos h3).symm

end DGS
