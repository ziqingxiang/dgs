module

public import DGS.S08_Two.Lagrangian
public import DGS.S08_Two.Step3

@[expose] public section

open Matrix Polynomial Module

namespace DGS

variable {n : ℕ}

local notation "V" => Fin n → ZMod 2
local notation "Mat" => Matrix (Fin n) (Fin n) (ZMod 2)

def prodSpanL (L : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {x | ∃ u ∈ L, ∃ u' ∈ L, x = u * u'}

def BadL (L : Submodule (ZMod 2) V) : Prop :=
  ¬ orthC (Submodule.span (ZMod 2) {ones n (ZMod 2)}) ≤ prodSpanL L

theorem badL_of_badK {K L : Submodule (ZMod 2) V} (hLK : L ≤ orthC K) (hB : BadK K) : BadL L := by
  intro h
  apply hB
  refine h.trans (Submodule.span_mono ?_)
  rintro x ⟨u, hu, u', hu', rfl⟩
  exact ⟨u, hLK hu, u', hLK hu', rfl⟩

theorem aF_pos {S : Finset (Fin n)} {i : ℕ} (hi : i < kap S) : 0 < aF S i := by
  unfold aF kap at *
  split_ifs with h
  · exact one_pos
  · exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))

theorem IsFlag.le_kap {S : Finset (Fin n)} (hS : S.Nonempty) {m : ℕ} {u : Fin m → V}
    (hu : IsFlag S m u) : m ≤ kap S := by
  rcases m with - | m
  · exact Nat.zero_le _
  · have h1 := finrank_radical_flag hS hu
    have h2 : finrank (ZMod 2) (radL u) ≤ S.card / 2 := by
      obtain ⟨-, hmem, -, -⟩ := hu.prop hS
      refine finrank_iso_le (inf_le_left.trans ?_) fun x hx y hy => (mem_orthC.1 hy.2) x hx.1
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmem i
    rw [radL] at h2
    unfold kap
    omega

theorem pre_kseq {k m : ℕ} (h : k ≤ m) (M : Mat) : pre k h (kseq m M) = kseq k M := by
  funext j
  rfl

theorem isFlag_kseq {M : Mat} (hM : IsAlt M) {k : ℕ}
    (hk : k ≤ (muVec M (ones n (ZMod 2))).natDegree) : IsFlag Finset.univ k (kseq k M) := by
  have h : SeqValid (flagCh Finset.univ) k (kseq k M) := by
    rw [seqValid_iff]
    rintro ⟨_ | i, hi⟩
    · show kseq k M ⟨0, hi⟩ = indS Finset.univ
      rw [indS_univ]
      simp [kseq]
    · refine ⟨by rw [coordSub_univ]; exact Submodule.mem_top, ?_, ?_⟩
      · rw [pre_kseq, mem_orthC_span_iff]
        intro j
        exact dot_pow_ones_eq_zero hM.1 hM.2 (Or.inr (Nat.succ_ne_zero i))
      · rw [pre_kseq]
        have hind := (linearIndependent_kseq_iff M (i + 1 + 1)).2 (by omega)
        rw [kseq_succ_eq_snoc, linearIndependent_finSnoc] at hind
        exact hind.2
  exact h

theorem radL_le_orthC_cyc {M : Mat} {k m : ℕ} (hk : k ≤ m) {u : Fin m → V}
    (hk0 : (muVec M (ones n (ZMod 2))).natDegree = k) (hMu : pre k hk u = kseq k M) :
    radL u ≤ orthC (cyc M (ones n (ZMod 2))) := by
  rw [cyc_eq_span_kseq, hk0, ← hMu]
  refine inf_le_right.trans (orthC_anti (Submodule.span_mono ?_))
  rintro _ ⟨j, rfl⟩
  exact ⟨Fin.castLE hk j, rfl⟩

def sK (n k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (n - (i + 1))

theorem kcount_flag (hS : (Finset.univ : Finset (Fin n)).Nonempty) :
    ∀ {k : ℕ} {p : Fin (k + 1) → V}, IsFlag Finset.univ (k + 1) p →
      kcount (k + 1) p * 2 ^ sK n k = Nat.card {M : Mat // IsAlt M} := by
  intro k
  induction k with
  | zero =>
    intro p hp
    rw [isFlag_one_iff, indS_univ] at hp
    rw [sK, Finset.range_zero, Finset.sum_empty, pow_zero, mul_one, kcount]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun M => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩)
    funext j
    have : j = 0 := Fin.ext (by have := j.2; omega)
    subst this
    rw [hp]
    simp [kseq]
  | succ k ih =>
    intro p hp
    have hp' := hp
    rw [isFlag_succ_iff] at hp'
    obtain ⟨hinit, -, horth, -⟩ := hp'
    obtain ⟨-, -, hind, -⟩ := hinit.prop hS
    have h1 := lem_krylov hind (p (Fin.last (k + 1)))
    rw [Fin.snoc_init_self, ite_eq_left horth] at h1
    rw [sK, Finset.sum_range_succ, pow_add, ← sK, mul_comm (2 ^ sK n k), ← mul_assoc, h1]
    exact ih hinit

theorem card_k0_flag (hS : (Finset.univ : Finset (Fin n)).Nonempty) {k : ℕ} {p : Fin (k + 1) → V}
    (hp : IsFlag Finset.univ (k + 1) p) :
    Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
        kseq (k + 1) M = p} * 2 ^ (n - (k + 1)) = 2 ^ (k + 1 - n % 2) * kcount (k + 1) p := by
  classical
  obtain ⟨-, -, hw, -⟩ := hp.prop hS
  rw [natCard_subtype_eq_sum _ (fun M : Mat => M ^ (k + 1) *ᵥ ones n (ZMod 2)), Finset.sum_mul]
  have hz : ∀ z, Nat.card {M : Mat // ((IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
      kseq (k + 1) M = p) ∧ M ^ (k + 1) *ᵥ ones n (ZMod 2) = z} =
      if z ∈ Submodule.span (ZMod 2) (Set.range p) then kcount (k + 1 + 1) (Fin.snoc p z) else 0 := by
    intro z
    split_ifs with hzs
    · refine Nat.card_congr (Equiv.subtypeEquivRight fun M => ?_)
      rw [kseq_succ_eq_iff, natDegree_muVec_eq_iff]
      constructor
      · rintro ⟨⟨⟨hM, -⟩, hMw⟩, hMz⟩
        exact ⟨hM, hMw, hMz⟩
      · rintro ⟨hM, hMw, hMz⟩
        refine ⟨⟨⟨hM, ?_, ?_⟩, hMw⟩, hMz⟩
        · rw [hMw]; exact hw
        · rw [hMw, hMz]; exact hzs
    · have : IsEmpty {M : Mat // ((IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
          kseq (k + 1) M = p) ∧ M ^ (k + 1) *ᵥ ones n (ZMod 2) = z} := by
        refine ⟨fun M => hzs ?_⟩
        obtain ⟨⟨⟨-, hk⟩, hMw⟩, hMz⟩ := M.2
        have := ((natDegree_muVec_eq_iff M.1 (k + 1)).1 hk).2
        rwa [hMw, hMz] at this
      exact Nat.card_of_isEmpty
  simp_rw [hz]
  have h84 : ∀ z, (if z ∈ Submodule.span (ZMod 2) (Set.range p) then
      kcount (k + 1 + 1) (Fin.snoc p z) else 0) * 2 ^ (n - (k + 1)) =
      if z ∈ Submodule.span (ZMod 2) (Set.range p) ⊓ orthC (Submodule.span (ZMod 2) (Set.range p))
      then kcount (k + 1) p else 0 := by
    intro z
    split_ifs with h1 h2 h2
    · rw [lem_krylov hw z, ite_eq_left (Submodule.mem_inf.1 h2).2]
    · rw [lem_krylov hw z, ite_eq_right (fun h => h2 (Submodule.mem_inf.2 ⟨h1, h⟩))]
    · exact absurd h2.1 h1
    · rw [zero_mul]
  simp_rw [h84]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have h1 : (Finset.univ.filter fun z => z ∈ Submodule.span (ZMod 2) (Set.range p) ⊓
      orthC (Submodule.span (ZMod 2) (Set.range p))).card =
      Nat.card (Submodule.span (ZMod 2) (Set.range p) ⊓
        orthC (Submodule.span (ZMod 2) (Set.range p)) : Submodule (ZMod 2) V) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have h2 := finrank_radical_flag hS hp
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [h1, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, h2]

theorem card_k0_flag_eq (hS : (Finset.univ : Finset (Fin n)).Nonempty) {k : ℕ}
    {p p' : Fin (k + 1) → V} (hp : IsFlag Finset.univ (k + 1) p)
    (hp' : IsFlag Finset.univ (k + 1) p') :
    Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
        kseq (k + 1) M = p} =
      Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
        kseq (k + 1) M = p'} := by
  have h1 := card_k0_flag hS hp
  have h2 := card_k0_flag hS hp'
  have h3 := kcount_flag hS hp
  have h4 := kcount_flag hS hp'
  refine Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (Nat.two_pow_pos (n - (k + 1))) (Nat.two_pow_pos (sK n k))) ?_
  calc Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
          kseq (k + 1) M = p} * (2 ^ (n - (k + 1)) * 2 ^ sK n k)
      = 2 ^ (k + 1 - n % 2) * (kcount (k + 1) p * 2 ^ sK n k) := by rw [← mul_assoc, h1]; ring
    _ = 2 ^ (k + 1 - n % 2) * (kcount (k + 1) p' * 2 ^ sK n k) := by rw [h3, h4]
    _ = Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
          kseq (k + 1) M = p'} * (2 ^ (n - (k + 1)) * 2 ^ sK n k) := by
        rw [← mul_assoc (Nat.card _), h2]; ring

theorem sum_card_comm {A B : Type*} [Fintype A] [Fintype B] (R : A → B → Prop) :
    ∑ a, Nat.card {b // R a b} = ∑ b, Nat.card {a // R a b} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  exact Finset.sum_comm

theorem sum_ite_card {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P] (c : ℕ) :
    ∑ a, (if P a then c else 0) = Nat.card {a // P a} * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem natCard_eq_sum_k0 (hn : 1 ≤ n) (P : Mat → Prop) (hP : ∀ M, P M → IsAlt M) :
    Nat.card {M : Mat // P M} = ∑ k ∈ Finset.range (kap (Finset.univ : Finset (Fin n))),
      Nat.card {M : Mat // P M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1} := by
  have hS : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hle : ∀ M, P M → (muVec M (ones n (ZMod 2))).natDegree - 1 ≤
      kap (Finset.univ : Finset (Fin n)) - 1 := by
    intro M hM
    have := (isFlag_kseq (hP M hM) le_rfl).le_kap hS
    omega
  rw [natCard_eq_sum_range P (fun M => (muVec M (ones n (ZMod 2))).natDegree - 1) _ hle]
  have hκ : kap (Finset.univ : Finset (Fin n)) - 1 + 1 = kap (Finset.univ : Finset (Fin n)) := by
    have : 1 ≤ kap (Finset.univ : Finset (Fin n)) := by
      unfold kap
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    omega
  rw [hκ]
  refine Finset.sum_congr rfl fun k _ => Nat.card_congr (Equiv.subtypeEquivRight fun M => ?_)
  have := one_le_natDegree_muVec hn M
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by omega⟩

theorem coupling_k (hn : 1 ≤ n) {k : ℕ} (hk : k + 1 ≤ kap (Finset.univ : Finset (Fin n))) :
    Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
        BadK (cyc M (ones n (ZMod 2)))} *
        Nat.card {u : Fin (kap (Finset.univ : Finset (Fin n))) → V //
          IsFlag Finset.univ (kap Finset.univ) u} ≤
      Nat.card {u : Fin (kap (Finset.univ : Finset (Fin n))) → V //
          IsFlag Finset.univ (kap Finset.univ) u ∧ BadL (radL u)} *
        Nat.card {M : Mat // IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1} := by
  classical
  have hS : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set κ := kap (Finset.univ : Finset (Fin n)) with hκ
  set E := ∏ i ∈ Finset.Ico (k + 1) κ, aF (Finset.univ : Finset (Fin n)) i with hE
  have hEpos : 0 < E := Finset.prod_pos fun i hi => aF_pos (Finset.mem_Ico.1 hi).2
  have hext : ∀ M : Mat, IsAlt M → (muVec M (ones n (ZMod 2))).natDegree = k + 1 →
      Nat.card {u : Fin κ → V // IsFlag Finset.univ κ u ∧ pre (k + 1) hk u = kseq (k + 1) M} = E :=
    fun M hM hk0 => card_ext (flagCh Finset.univ) (aF Finset.univ)
      (fun i p hp => card_flagCh_eq hS i p hp) (kseq (k + 1) M) (isFlag_kseq hM hk0.ge) κ hk
  by_cases hF : Nat.card {u : Fin κ → V // IsFlag Finset.univ κ u} = 0
  · rw [hF, mul_zero]
    exact Nat.zero_le _
  obtain ⟨⟨u₀, hu₀⟩⟩ : Nonempty {u : Fin κ → V // IsFlag Finset.univ κ u} := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hF Nat.card_of_isEmpty
  set c := Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
    kseq (k + 1) M = pre (k + 1) hk u₀} with hc_def
  have hc : ∀ u : Fin κ → V, IsFlag Finset.univ κ u →
      Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
        kseq (k + 1) M = pre (k + 1) hk u} = c :=
    fun u hu => card_k0_flag_eq hS (SeqValid.pre_of _ hu (k + 1) hk)
      (SeqValid.pre_of _ hu₀ (k + 1) hk)
  have hA : Nat.card {M : Mat // IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1} * E =
      Nat.card {u : Fin κ → V // IsFlag Finset.univ κ u} * c := by
    have h := sum_card_comm (fun (M : Mat) (u : Fin κ → V) =>
      (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
        IsFlag Finset.univ κ u ∧ pre (k + 1) hk u = kseq (k + 1) M)
    have h1 : ∀ M : Mat, Nat.card {u : Fin κ → V //
        (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
          IsFlag Finset.univ κ u ∧ pre (k + 1) hk u = kseq (k + 1) M} =
        if IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1 then E else 0 := by
      intro M
      split_ifs with hM
      · rw [← hext M hM.1 hM.2]
        exact Nat.card_congr (Equiv.subtypeEquivRight fun u => ⟨fun h => h.2, fun h => ⟨hM, h⟩⟩)
      · have : IsEmpty {u : Fin κ → V //
            (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
              IsFlag Finset.univ κ u ∧ pre (k + 1) hk u = kseq (k + 1) M} := ⟨fun u => hM u.2.1⟩
        exact Nat.card_of_isEmpty
    have h2 : ∀ u : Fin κ → V, Nat.card {M : Mat //
        (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
          IsFlag Finset.univ κ u ∧ pre (k + 1) hk u = kseq (k + 1) M} =
        if IsFlag Finset.univ κ u then c else 0 := by
      intro u
      split_ifs with hu
      · rw [← hc u hu]
        exact Nat.card_congr (Equiv.subtypeEquivRight fun M =>
          ⟨fun h => ⟨h.1, h.2.2.symm⟩, fun h => ⟨h.1, hu, h.2.symm⟩⟩)
      · have : IsEmpty {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
            IsFlag Finset.univ κ u ∧ pre (k + 1) hk u = kseq (k + 1) M} := ⟨fun M => hu M.2.2.1⟩
        exact Nat.card_of_isEmpty
    simp_rw [h1, h2, sum_ite_card] at h
    exact h
  have hB : Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
      BadK (cyc M (ones n (ZMod 2)))} * E ≤
      Nat.card {u : Fin κ → V // IsFlag Finset.univ κ u ∧ BadL (radL u)} * c := by
    have h := sum_card_comm (fun (M : Mat) (u : Fin κ → V) =>
      ((IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
        BadK (cyc M (ones n (ZMod 2)))) ∧ IsFlag Finset.univ κ u ∧ pre (k + 1) hk u = kseq (k + 1) M)
    have h1 : ∀ M : Mat, Nat.card {u : Fin κ → V //
        ((IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
          BadK (cyc M (ones n (ZMod 2)))) ∧ IsFlag Finset.univ κ u ∧ pre (k + 1) hk u = kseq (k + 1) M} =
        if (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
          BadK (cyc M (ones n (ZMod 2))) then E else 0 := by
      intro M
      split_ifs with hM
      · rw [← hext M hM.1.1 hM.1.2]
        exact Nat.card_congr (Equiv.subtypeEquivRight fun u => ⟨fun h => h.2, fun h => ⟨hM, h⟩⟩)
      · have : IsEmpty {u : Fin κ → V //
            ((IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
              BadK (cyc M (ones n (ZMod 2)))) ∧
              IsFlag Finset.univ κ u ∧ pre (k + 1) hk u = kseq (k + 1) M} := ⟨fun u => hM u.2.1⟩
        exact Nat.card_of_isEmpty
    have h2 : ∀ u : Fin κ → V, Nat.card {M : Mat //
        ((IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
          BadK (cyc M (ones n (ZMod 2)))) ∧ IsFlag Finset.univ κ u ∧ pre (k + 1) hk u = kseq (k + 1) M} ≤
        if IsFlag Finset.univ κ u ∧ BadL (radL u) then c else 0 := by
      intro u
      split_ifs with hu
      · rw [← hc u hu.1]
        exact natCard_mono fun M h => ⟨h.1.1, h.2.2.symm⟩
      · have : IsEmpty {M : Mat // ((IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
            BadK (cyc M (ones n (ZMod 2)))) ∧
            IsFlag Finset.univ κ u ∧ pre (k + 1) hk u = kseq (k + 1) M} := by
          refine ⟨fun M => hu ⟨M.2.2.1, ?_⟩⟩
          exact badL_of_badK (radL_le_orthC_cyc hk M.2.1.1.2 M.2.2.2) M.2.1.2
        rw [Nat.card_of_isEmpty]
    simp_rw [h1, sum_ite_card] at h
    rw [h]
    calc ∑ u : Fin κ → V, Nat.card {M : Mat //
          ((IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
            BadK (cyc M (ones n (ZMod 2)))) ∧ IsFlag Finset.univ κ u ∧
            pre (k + 1) hk u = kseq (k + 1) M}
        ≤ ∑ u : Fin κ → V, (if IsFlag Finset.univ κ u ∧ BadL (radL u) then c else 0) :=
          Finset.sum_le_sum fun u _ => h2 u
      _ = Nat.card {u : Fin κ → V // IsFlag Finset.univ κ u ∧ BadL (radL u)} * c := sum_ite_card _ _
  refine Nat.le_of_mul_le_mul_right ?_ hEpos
  calc Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
          BadK (cyc M (ones n (ZMod 2)))} * Nat.card {u : Fin κ → V // IsFlag Finset.univ κ u} * E
      = Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
          BadK (cyc M (ones n (ZMod 2)))} * E * Nat.card {u : Fin κ → V // IsFlag Finset.univ κ u} := by
        ring
    _ ≤ Nat.card {u : Fin κ → V // IsFlag Finset.univ κ u ∧ BadL (radL u)} * c *
          Nat.card {u : Fin κ → V // IsFlag Finset.univ κ u} := Nat.mul_le_mul_right _ hB
    _ = Nat.card {u : Fin κ → V // IsFlag Finset.univ κ u ∧ BadL (radL u)} *
          (Nat.card {u : Fin κ → V // IsFlag Finset.univ κ u} * c) := by ring
    _ = Nat.card {u : Fin κ → V // IsFlag Finset.univ κ u ∧ BadL (radL u)} *
          (Nat.card {M : Mat // IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1} * E) := by
        rw [hA]
    _ = _ := by ring

theorem coupling (hn : 1 ≤ n) :
    Nat.card {M : Mat // IsAlt M ∧ BadK (cyc M (ones n (ZMod 2)))} *
        Nat.card {u : Fin (kap (Finset.univ : Finset (Fin n))) → V //
          IsFlag Finset.univ (kap Finset.univ) u} ≤
      Nat.card {u : Fin (kap (Finset.univ : Finset (Fin n))) → V //
          IsFlag Finset.univ (kap Finset.univ) u ∧ BadL (radL u)} *
        Nat.card {M : Mat // IsAlt M} := by
  rw [natCard_eq_sum_k0 hn (fun M => IsAlt M ∧ BadK (cyc M (ones n (ZMod 2)))) (fun M h => h.1),
    natCard_eq_sum_k0 hn (fun M => IsAlt M) (fun M h => h), Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k + 1 ≤ kap (Finset.univ : Finset (Fin n)) := by
    rw [Finset.mem_range] at hk
    omega
  have e1 : Nat.card {M : Mat // (IsAlt M ∧ BadK (cyc M (ones n (ZMod 2)))) ∧
        (muVec M (ones n (ZMod 2))).natDegree = k + 1} =
      Nat.card {M : Mat // (IsAlt M ∧ (muVec M (ones n (ZMod 2))).natDegree = k + 1) ∧
        BadK (cyc M (ones n (ZMod 2)))} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun M =>
      ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩)
  rw [e1]
  exact coupling_k hn hk'

theorem coupling_maxIso (hn : 1 ≤ n) :
    Nat.card {M : Mat // IsAlt M ∧ BadK (cyc M (ones n (ZMod 2)))} *
        Nat.card {L : Submodule (ZMod 2) V // IsMaxIso Finset.univ L} ≤
      Nat.card {L : Submodule (ZMod 2) V // IsMaxIso Finset.univ L ∧ BadL L} *
        Nat.card {M : Mat // IsAlt M} := by
  have hS : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have h := coupling hn
  have e1 := card_fiber_radL_pred hS (m := kap (Finset.univ : Finset (Fin n))) rfl (fun _ => True)
  have e2 := card_fiber_radL_pred hS (m := kap (Finset.univ : Finset (Fin n))) rfl BadL
  have f1 : Nat.card {u : Fin (kap (Finset.univ : Finset (Fin n))) → V //
      IsFlag Finset.univ (kap Finset.univ) u ∧ True} =
      Nat.card {u : Fin (kap (Finset.univ : Finset (Fin n))) → V //
        IsFlag Finset.univ (kap Finset.univ) u} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun u => (and_true _).to_iff)
  have f2 : Nat.card {L : Submodule (ZMod 2) V // IsMaxIso Finset.univ L ∧ True} =
      Nat.card {L : Submodule (ZMod 2) V // IsMaxIso Finset.univ L} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun L => (and_true _).to_iff)
  rw [f1, f2] at e1
  rw [e1, e2] at h
  have hpos : 0 < ∏ i ∈ Finset.range (kap (Finset.univ : Finset (Fin n))),
      bL (Finset.univ : Finset (Fin n)) i :=
    Finset.prod_pos fun i hi => bL_pos (Finset.mem_range.1 hi)
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card {M : Mat // IsAlt M ∧ BadK (cyc M (ones n (ZMod 2)))} *
        Nat.card {L : Submodule (ZMod 2) V // IsMaxIso Finset.univ L} *
        ∏ i ∈ Finset.range (kap (Finset.univ : Finset (Fin n))), bL (Finset.univ : Finset (Fin n)) i
      = Nat.card {M : Mat // IsAlt M ∧ BadK (cyc M (ones n (ZMod 2)))} *
        (Nat.card {L : Submodule (ZMod 2) V // IsMaxIso Finset.univ L} *
        ∏ i ∈ Finset.range (kap (Finset.univ : Finset (Fin n))), bL (Finset.univ : Finset (Fin n)) i) :=
        by ring
    _ ≤ Nat.card {L : Submodule (ZMod 2) V // IsMaxIso Finset.univ L ∧ BadL L} *
        (∏ i ∈ Finset.range (kap (Finset.univ : Finset (Fin n))), bL (Finset.univ : Finset (Fin n)) i) *
        Nat.card {M : Mat // IsAlt M} := h
    _ = _ := by ring

end DGS
