module

public import DGS.S07_Small.Frames
public import Mathlib.FieldTheory.Finite.GaloisField

@[expose] public section

open Polynomial

namespace DGS

theorem card_irrSet_mul_le (p : ℕ) [Fact p.Prime] {d : ℕ} (hd : d ≠ 0) :
    d * piCount p d ≤ p ^ d := by
  classical
  have : Fintype (GaloisField p d) := Fintype.ofFinite _
  have hroot : ∀ β ∈ irrSet p d, ∃ α : GaloisField p d, aeval α β = 0 := by
    intro β hβ
    obtain ⟨hm, hirr, hdeg⟩ := mem_irrSet_iff.1 hβ
    have : Fact (Irreducible β) := ⟨hirr⟩
    let pb := AdjoinRoot.powerBasis hirr.ne_zero
    have : Module.Finite (ZMod p) (AdjoinRoot β) := pb.finite
    have : Finite (AdjoinRoot β) := Module.finite_of_finite (ZMod p)
    have hcard : Nat.card (AdjoinRoot β) = p ^ d := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, pb.finrank,
        AdjoinRoot.powerBasis_dim, hdeg]
    let e := GaloisField.algEquivGaloisField p d hcard
    refine ⟨e (AdjoinRoot.root β), ?_⟩
    have h1 : aeval (e.toAlgHom (AdjoinRoot.root β)) β = e.toAlgHom (aeval (AdjoinRoot.root β) β) :=
      Polynomial.aeval_algHom_apply _ _ _
    have h2 : aeval (AdjoinRoot.root β) β = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    rw [h2, map_zero] at h1
    exact h1
  have hcardroot : ∀ β ∈ irrSet p d, (β.rootSet (GaloisField p d)).toFinset.card = d := by
    intro β hβ
    obtain ⟨hm, hirr, hdeg⟩ := mem_irrSet_iff.1 hβ
    obtain ⟨α, hα⟩ := hroot β hβ
    have hmin : β = minpoly (ZMod p) α := minpoly.eq_of_irreducible_of_monic hirr hα hm
    have hsplit : Splits (β.map (algebraMap (ZMod p) (GaloisField p d))) := by
      rw [hmin]
      exact Normal.splits inferInstance α
    have hsep : β.Separable := PerfectField.separable_of_irreducible hirr
    rw [Set.toFinset_card, card_rootSet_eq_natDegree hsep hsplit, hdeg]
  have hdisj : ∀ β ∈ irrSet p d, ∀ β' ∈ irrSet p d, β ≠ β' →
      Disjoint (β.rootSet (GaloisField p d)).toFinset (β'.rootSet (GaloisField p d)).toFinset := by
    intro β hβ β' hβ' hne
    rw [Finset.disjoint_left]
    intro α h1 h2
    rw [Set.mem_toFinset, mem_rootSet] at h1 h2
    obtain ⟨hm, hirr, -⟩ := mem_irrSet_iff.1 hβ
    obtain ⟨hm', hirr', -⟩ := mem_irrSet_iff.1 hβ'
    apply hne
    rw [minpoly.eq_of_irreducible_of_monic hirr h1.2 hm,
      minpoly.eq_of_irreducible_of_monic hirr' h2.2 hm']
  calc d * piCount p d = ∑ β ∈ irrSet p d, (β.rootSet (GaloisField p d)).toFinset.card := by
        rw [Finset.sum_congr rfl hcardroot, Finset.sum_const, smul_eq_mul, piCount, mul_comm]
    _ = ((irrSet p d).biUnion fun β => (β.rootSet (GaloisField p d)).toFinset).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ Fintype.card (GaloisField p d) := Finset.card_le_univ _
    _ = p ^ d := by rw [← Nat.card_eq_fintype_card, GaloisField.card p d hd]

theorem piCount_le_div (p : ℕ) [Fact p.Prime] {d : ℕ} (hd : d ≠ 0) :
    (piCount p d : ℝ) ≤ (p : ℝ) ^ d / d := by
  have h := card_irrSet_mul_le p hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  rw [le_div_iff₀ hd']
  have : ((d * piCount p d : ℕ) : ℝ) ≤ ((p ^ d : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this
  linarith

end DGS
