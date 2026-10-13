module

public import DGS.S08_Two.CondLaw

@[expose] public section

namespace DGS

section SeqCount

variable {X : Type*} [Finite X]

def SeqValid (Ch : (i : ℕ) → (Fin i → X) → Set X) : (m : ℕ) → (Fin m → X) → Prop
  | 0, _ => True
  | m + 1, u => SeqValid Ch m (Fin.init u) ∧ u (Fin.last m) ∈ Ch m (Fin.init u)

def pre {m : ℕ} (k : ℕ) (h : k ≤ m) (u : Fin m → X) : Fin k → X := fun j => u (Fin.castLE h j)

omit [Finite X] in
theorem pre_self {m : ℕ} (u : Fin m → X) : pre m le_rfl u = u := by
  funext j; simp [pre]

omit [Finite X] in
theorem pre_init {m k : ℕ} (h : k ≤ m) (u : Fin (m + 1) → X) :
    pre k h (Fin.init u) = pre k (h.trans (Nat.le_succ m)) u := by
  funext j
  simp only [pre, Fin.init]
  congr 1

omit [Finite X] in
theorem pre_snoc {m k : ℕ} (h : k ≤ m) (u : Fin m → X) (x : X) :
    pre k (h.trans (Nat.le_succ m)) (Fin.snoc u x : Fin (m + 1) → X) = pre k h u := by
  rw [← pre_init h, Fin.init_snoc]

omit [Finite X] in
theorem pre_pre {m k l : ℕ} (hkl : k ≤ l) (hlm : l ≤ m) (u : Fin m → X) :
    pre k hkl (pre l hlm u) = pre k (hkl.trans hlm) u := by
  funext j; simp only [pre]; congr 1

variable (Ch : (i : ℕ) → (Fin i → X) → Set X)

omit [Finite X] in
theorem seqValid_snoc {m : ℕ} (u : Fin m → X) (x : X) :
    SeqValid Ch (m + 1) (Fin.snoc u x : Fin (m + 1) → X) ↔ SeqValid Ch m u ∧ x ∈ Ch m u := by
  show SeqValid Ch m (Fin.init (Fin.snoc u x : Fin (m + 1) → X)) ∧
      (Fin.snoc u x : Fin (m + 1) → X) (Fin.last m) ∈ Ch m (Fin.init (Fin.snoc u x : Fin (m + 1) → X)) ↔ _
  rw [Fin.init_snoc, Fin.snoc_last]

omit [Finite X] in
theorem SeqValid.pre_of {m : ℕ} {u : Fin m → X} (hu : SeqValid Ch m u) :
    ∀ k (h : k ≤ m), SeqValid Ch k (pre k h u) := by
  induction m with
  | zero =>
    intro k h
    have : k = 0 := by omega
    subst this
    trivial
  | succ m ih =>
    intro k h
    rcases Nat.lt_or_ge k (m + 1) with hk | hk
    · have := ih hu.1 k (by omega)
      rwa [pre_init] at this
    · have : k = m + 1 := by omega
      subst this
      rwa [pre_self]

theorem card_ext (a : ℕ → ℕ) (ha : ∀ i (p : Fin i → X), SeqValid Ch i p → Nat.card (Ch i p) = a i)
    {k : ℕ} (p : Fin k → X) (hp : SeqValid Ch k p) :
    ∀ m (h : k ≤ m), Nat.card {u : Fin m → X // SeqValid Ch m u ∧ pre k h u = p} =
      ∏ i ∈ Finset.Ico k m, a i := by
  intro m h
  induction m, h using Nat.le_induction with
  | base =>
    rw [Finset.Ico_self, Finset.prod_empty]
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨p, hp, pre_self p⟩, fun u => Subtype.ext ?_⟩
    have := u.2.2
    rwa [pre_self] at this
  | succ m hkm ih =>
    rw [Finset.prod_Ico_succ_top hkm, ← ih]
    have e : {u : Fin (m + 1) → X // SeqValid Ch (m + 1) u ∧ pre k (hkm.trans (Nat.le_succ m)) u = p} ≃
        Σ u' : {u' : Fin m → X // SeqValid Ch m u' ∧ pre k hkm u' = p}, Ch m u'.1 :=
      { toFun := fun u => ⟨⟨Fin.init u.1, u.2.1.1, by rw [pre_init]; exact u.2.2⟩,
          ⟨u.1 (Fin.last m), u.2.1.2⟩⟩
        invFun := fun x => ⟨Fin.snoc x.1.1 x.2.1,
          ⟨(seqValid_snoc Ch x.1.1 x.2.1).2 ⟨x.1.2.1, x.2.2⟩,
          by rw [pre_snoc hkm]; exact x.1.2.2⟩⟩
        left_inv := fun u => Subtype.ext (Fin.snoc_init_self u.1)
        right_inv := fun x => Sigma.subtype_ext (Subtype.ext (by simp only [Fin.init_snoc]))
          (by simp only [Fin.snoc_last]) }
    rw [Nat.card_congr e]
    have hfin : Finite {u' : Fin m → X // SeqValid Ch m u' ∧ pre k hkm u' = p} := inferInstance
    have := Fintype.ofFinite {u' : Fin m → X // SeqValid Ch m u' ∧ pre k hkm u' = p}
    rw [Nat.card_sigma]
    have : ∀ u' : {u' : Fin m → X // SeqValid Ch m u' ∧ pre k hkm u' = p},
        Nat.card (Ch m u'.1) = a m := fun u' => ha m u'.1 u'.2.1
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem card_valid (a : ℕ → ℕ)
    (ha : ∀ i (p : Fin i → X), SeqValid Ch i p → Nat.card (Ch i p) = a i) (m : ℕ) :
    Nat.card {u : Fin m → X // SeqValid Ch m u} = ∏ i ∈ Finset.range m, a i := by
  have h := card_ext Ch a ha (Fin.elim0) trivial m (Nat.zero_le m)
  rw [Finset.range_eq_Ico, ← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
  constructor
  · intro hu; exact ⟨hu, funext fun j => j.elim0⟩
  · intro hu; exact hu.1

end SeqCount

end DGS
