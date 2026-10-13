module

public import DGS.Ext.Cyclic.Bound
public import DGS.Ext.Cyclic.Krylov

@[expose] public section

open Matrix Polynomial Module Filter Topology

namespace DGS

variable {n : ℕ}

theorem notCyc_of_not_controllable {G : SimpleGraph (Fin n)} (hG : ¬ Controllable G) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (b : Fin n → Bool) : NotCyc p (switched G b) (signMat b *ᵥ ones n ℤ) := by
  classical
  have hW : (walkMatrix (adj G)).det = 0 := not_not.1 hG
  have hWp : (krylovMat (modP p (adj G)) (ones n (ZMod p))).det = 0 := by
    have h1 := RingHom.map_det (Int.castRingHom (ZMod p)) (walkMatrix (adj G))
    rw [RingHom.mapMatrix_apply, walkMatrix_map, hW, map_zero] at h1
    exact h1.symm
  have hAs : (modP p (adj G))ᵀ = modP p (adj G) := by
    rw [← modP_transpose]
    congr 1
    exact (SimpleGraph.isSymm_adjMatrix G).eq
  obtain ⟨U, hU, horth⟩ := exists_simple_perp_of_det_eq_zero hAs hWp
  have h2 := two_ne_zero_zmod hp
  have hrel : ∀ x, ones n (ZMod p) ⬝ᵥ x = 0 →
      modP p (seidelOfGraph G) *ᵥ x = -x - (2 : ZMod p) • (modP p (adj G) *ᵥ x) :=
    fun x hx => seidel_mulVec_of_perp p G hx
  have hUS : IsSimpleInvariant (modP p (seidelOfGraph G)) U :=
    (isSimpleInvariant_iff_of_perp h2 hrel horth).1 hU
  have hT : modP p (signMat b) * modP p (signMat b) = 1 := by
    rw [← modP_mul, signMat_mul_self, modP_one]
  have hTT : (modP p (signMat b))ᵀ * modP p (signMat b) = 1 := by
    rw [← modP_transpose, signMat_transpose, hT]
  have hS' : modP p (switched G b) =
      modP p (signMat b) * modP p (seidelOfGraph G) * modP p (signMat b) := by
    rw [switched, modP_mul, modP_mul]
  have hTS : modP p (signMat b) * modP p (seidelOfGraph G) =
      modP p (switched G b) * modP p (signMat b) := by
    rw [hS', Matrix.mul_assoc _ (modP p (signMat b)), hT, Matrix.mul_one]
  have hu : modP p (signMat b) *ᵥ ones n (ZMod p) = modPVec p (signMat b *ᵥ ones n ℤ) := by
    rw [signMat_mulVec_ones]
    funext i
    simp [modP, signMat, modPVec, mulVec, dotProduct, Matrix.diagonal_apply, ones]
  refine ⟨U.map (modP p (signMat b)).mulVecLin, isSimpleInvariant_map hT hTS hUS, ?_⟩
  rw [← hu]
  exact orth_map hTT horth

theorem ext_orourke_touri : ORourkeTouriStatement := by
  unfold ORourkeTouriStatement
  have h : Tendsto (fun n : ℕ => prob (fun G : SimpleGraph (Fin n) => ¬ Controllable G)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_prob_notCyc
      (fun _ => prob_nonneg _) fun N => ?_
    obtain ⟨hp, hp2, -⟩ := corePrime_spec N
    have : Fact (corePrime N).Prime := ⟨hp⟩
    calc prob (fun G : SimpleGraph (Fin N) => ¬ Controllable G)
        = prob (fun x : SimpleGraph (Fin N) × (Fin N → Bool) => ¬ Controllable x.1) :=
          (prob_fst (fun G : SimpleGraph (Fin N) => ¬ Controllable G)).symm
      _ ≤ prob (fun x : SimpleGraph (Fin N) × (Fin N → Bool) =>
            NotCyc (corePrime N) (switched x.1 x.2) (signMat x.2 *ᵥ ones N ℤ)) :=
          prob_mono fun x hx => notCyc_of_not_controllable hx hp2 x.2
      _ = prob (fun x : (Pairs N → Bool) × (Fin N → Bool) =>
            NotCyc (corePrime N) (seidelOf x.1) (signVec x.2)) :=
          lem_switch N (NotCyc (corePrime N))
  exact tendsto_prob_one_of_compl (Ω := fun n => SimpleGraph (Fin n)) (P := fun _ G => Controllable G) h

end DGS
