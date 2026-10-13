module

public import DGS.S04_Reduction.Delete
public import DGS.S03_Prelim.Apriori
public import DGS.S03_Prelim.SuppD
public import DGS.S03_Prelim.Switching

@[expose] public section

open Matrix

namespace DGS

variable {n : ℕ}

theorem delMat_last_seidelOf (ω : Pairs (n + 1) → Bool) :
    delMat (seidelOf ω) (Fin.last n) = seidelOf (pairsSuccEquiv n ω).1 := by
  ext i j
  rw [delMat, submatrix_apply, Fin.succAbove_last, seidelOf, symOf_succ, border_castSucc_castSucc]
  rfl

theorem delCol_last_seidelOf (ω : Pairs (n + 1) → Bool) :
    delCol (seidelOf ω) (Fin.last n) = signVec (pairsSuccEquiv n ω).2 := by
  funext j
  rw [delCol, Fin.succAbove_last, seidelOf, symOf_succ, border_castSucc_last]
  rfl

def moveLast (i : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' (Fin.last n)).trans (finSuccEquiv' i).symm

@[simp] theorem moveLast_last (i : Fin (n + 1)) : moveLast i (Fin.last n) = i := by
  simp [moveLast, finSuccEquiv'_symm_none]

@[simp] theorem moveLast_castSucc (i : Fin (n + 1)) (j : Fin n) :
    moveLast i j.castSucc = i.succAbove j := by
  simp [moveLast, finSuccEquiv'_last_apply_castSucc, finSuccEquiv'_symm_some]

theorem delMat_submatrix_moveLast {R : Type*} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (i : Fin (n + 1)) : delMat (A.submatrix (moveLast i) (moveLast i)) (Fin.last n) = delMat A i := by
  ext j k
  simp [delMat]

theorem delCol_submatrix_moveLast {R : Type*} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (i : Fin (n + 1)) : delCol (A.submatrix (moveLast i) (moveLast i)) (Fin.last n) = delCol A i := by
  funext j
  simp [delCol]

theorem lem_exch_law (Φ : Matrix (Fin n) (Fin n) ℤ → (Fin n → ℤ) → Prop) :
    prob (fun ω : Pairs (n + 1) → Bool =>
        Φ (delMat (seidelOf ω) (Fin.last n)) (delCol (seidelOf ω) (Fin.last n))) =
      prob (fun x : (Pairs n → Bool) × (Fin n → Bool) => Φ (seidelOf x.1) (signVec x.2)) := by
  rw [← prob_equiv (pairsSuccEquiv n) (fun x => Φ (seidelOf x.1) (signVec x.2))]
  congr 1
  funext ω
  rw [delMat_last_seidelOf, delCol_last_seidelOf]

theorem lem_exch_eq (Φ : Matrix (Fin n) (Fin n) ℤ → (Fin n → ℤ) → Prop) (i : Fin (n + 1)) :
    prob (fun ω : Pairs (n + 1) → Bool => Φ (delMat (seidelOf ω) i) (delCol (seidelOf ω) i)) =
      prob (fun ω : Pairs (n + 1) → Bool =>
        Φ (delMat (seidelOf ω) (Fin.last n)) (delCol (seidelOf ω) (Fin.last n))) := by
  rw [← prob_comp_permPairs (moveLast i)
    (fun ω => Φ (delMat (seidelOf ω) (Fin.last n)) (delCol (seidelOf ω) (Fin.last n)))]
  congr 1
  funext ω
  rw [seidelOf, seidelOf, symOf_comp_permPairs, delMat_submatrix_moveLast,
    delCol_submatrix_moveLast]

open Classical in
theorem lem_exch (Φ : Matrix (Fin n) (Fin n) ℤ → (Fin n → ℤ) → Prop)
    (E : (Pairs (n + 1) → Bool) → Prop)
    (hE : ∀ ω, E ω → ((n + 1 : ℕ) : ℝ) / 20 <
      ((Finset.univ.filter fun i => Φ (delMat (seidelOf ω) i) (delCol (seidelOf ω) i)).card : ℝ)) :
    prob E ≤ 20 * prob (fun ω : Pairs (n + 1) → Bool =>
      Φ (delMat (seidelOf ω) (Fin.last n)) (delCol (seidelOf ω) (Fin.last n))) := by
  set Fl := prob (fun ω : Pairs (n + 1) → Bool =>
    Φ (delMat (seidelOf ω) (Fin.last n)) (delCol (seidelOf ω) (Fin.last n))) with hFl
  let N : (Pairs (n + 1) → Bool) → ℝ := fun ω =>
    ∑ i : Fin (n + 1), if Φ (delMat (seidelOf ω) i) (delCol (seidelOf ω) i) then (1 : ℝ) else 0
  have hN : expect N = (n + 1 : ℕ) * Fl := by
    rw [expect_sum]
    simp only [expect_indicator, lem_exch_eq Φ, ← hFl]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpt : ∀ ω, ((n + 1 : ℕ) : ℝ) / 20 * (if E ω then (1 : ℝ) else 0) ≤ N ω := by
    intro ω
    have hN0 : 0 ≤ N ω := Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
    split_ifs with h
    · rw [mul_one]
      refine (hE ω h).le.trans (le_of_eq ?_)
      simp only [N, Finset.sum_boole]
    · rw [mul_zero]
      exact hN0
  have h1 : ((n + 1 : ℕ) : ℝ) / 20 * prob E ≤ (n + 1 : ℕ) * Fl := by
    rw [← expect_indicator, ← expect_const_mul, ← hN]
    exact expect_mono hpt
  have hpos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  nlinarith

end DGS
