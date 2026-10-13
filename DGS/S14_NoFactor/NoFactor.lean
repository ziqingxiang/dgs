module

public import DGS.S14_NoFactor.Candidates
public import DGS.S11_Deg1.PtrueMain
public import DGS.S09_Smooth.Smooth
public import DGS.Core.Components
public import Mathlib.NumberTheory.Bertrand

@[expose] public section

open Finset Polynomial Filter

namespace DGS

theorem prob_dvd_le_geomMult {m p : ℕ} [Fact p.Prime] {g : ℤ[X]} {a : ℤ} (hpa : (p : ℤ) ∣ g.eval a) :
    probSeidel m (fun S => g ∣ S.charpoly) ≤
      prob (fun ω : Pairs m → Bool => 1 ≤ geomMult 1 (-1) (a : ZMod p) ω) := by
  unfold probSeidel
  refine prob_mono fun ω hω => ?_
  have h1 : g.eval a ∣ (seidelOf ω).charpoly.eval a := Polynomial.eval_dvd hω
  have h2 : (p : ℤ) ∣ (Matrix.scalar (Fin m) a - seidelOf ω).det := by
    rw [← Matrix.eval_charpoly]
    exact hpa.trans h1
  have h3 : (((Matrix.scalar (Fin m) a - seidelOf ω).det : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h2
  have hN : shiftedMat (F := ZMod p) 1 (-1) (a : ZMod p) ω =
      -((Matrix.scalar (Fin m) a - seidelOf ω).map (Int.castRingHom (ZMod p))) := by
    rw [shiftedMat_eq_modP]
    ext i j
    simp only [Matrix.scalar_apply]
    simp only [modP, Matrix.sub_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul, map_sub, eq_intCast]
    split_ifs <;> push_cast <;> ring
  have hdet : (shiftedMat (F := ZMod p) 1 (-1) (a : ZMod p) ω).det = 0 := by
    rw [hN, Matrix.det_neg, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast, h3, mul_zero]
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  unfold geomMult corank
  refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, ?_⟩, ?_⟩
  · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hv
  · intro h
    exact hv0 (congrArg Subtype.val h)

theorem eventually_prob_dvd_le :
    ∀ᶠ m : ℕ in atTop, ∀ p : ℕ, p.Prime → 23 ≤ p → (p : ℝ) ≤ Real.exp ((m : ℝ) ^ ((1 : ℝ) / 9)) →
      ∀ (g : ℤ[X]) (a : ℤ), (p : ℤ) ∣ g.eval a → probSeidel m (fun S => g ∣ S.charpoly) ≤ 3 / p := by
  filter_upwards [thm_rankp, eventually_rpow_ninth_le_mul cRK_pos] with m hm hcm
  intro p hp hp23 hpm g a hpa
  have : Fact p.Prime := ⟨hp⟩
  have h1 := (hm p hp23 hpm (a : ZMod p)).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp23' : (23 : ℝ) ≤ p := by exact_mod_cast hp23
  have hexp : Real.exp (-cRK * m) ≤ 1 / p := by
    have h2 : (p : ℝ) ≤ Real.exp (cRK * m) := hpm.trans (Real.exp_le_exp.2 hcm)
    calc Real.exp (-cRK * m) = (Real.exp (cRK * m))⁻¹ := by
          rw [← Real.exp_neg]
          congr 1
          ring
      _ ≤ (p : ℝ)⁻¹ := inv_anti₀ hp0 h2
      _ = 1 / p := (one_div _).symm
  have h12 : 1.2 / (p : ℝ) ^ 2 ≤ 1 / p := by
    rw [div_le_div_iff₀ (by positivity) hp0]
    nlinarith
  calc probSeidel m (fun S => g ∣ S.charpoly)
      ≤ prob (fun ω : Pairs m → Bool => 1 ≤ geomMult 1 (-1) (a : ZMod p) ω) := prob_dvd_le_geomMult hpa
    _ ≤ 1 / p + 1.2 / (p : ℝ) ^ 2 + Real.exp (-cRK * m) := h1
    _ ≤ 3 / p := by
        have : (3 : ℝ) / p = 1 / p + 1 / p + 1 / p := by ring
        linarith

theorem exists_prime_root {m : ℕ} {x : ℝ} {g : ℤ[X]} (hg : g.Monic) (hj1 : 1 ≤ g.natDegree)
    (hR : ∀ α ∈ (g.map (Int.castRingHom ℂ)).roots, ‖α‖ ≤ (m : ℝ))
    (hroot : g.natDegree = 1 ∨ ∀ a : ℤ, g.eval a ≠ 0)
    (hA : (m : ℝ) + 1000 ≤ Real.exp (x / (4 * g.natDegree))) (hjm : (g.natDegree : ℝ) ≤ m) :
    ∃ p : ℕ, p.Prime ∧ ∃ a : ℤ, (p : ℤ) ∣ g.eval a ∧
      Real.exp (x / (4 * g.natDegree)) ≤ p ∧ (p : ℝ) ≤ Real.exp x := by
  set A := Real.exp (x / (4 * g.natDegree)) with hAdef
  have hj0 : (0 : ℝ) < g.natDegree := by exact_mod_cast hj1
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA1000 : 1000 ≤ A := by linarith
  have hApow : A ^ (4 * g.natDegree) = Real.exp x := by
    rw [hAdef, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  by_cases h1 : g.natDegree = 1
  ·
    have hgX := hg.eq_X_add_C h1
    have hfl : ⌊A⌋₊ ≠ 0 := (Nat.floor_pos.2 (by linarith)).ne'
    obtain ⟨p, hp, hNp, hp2N⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊A⌋₊ hfl
    refine ⟨p, hp, -g.coeff 0, ?_, ?_, ?_⟩
    · rw [hgX]
      simp
    · have h2 := Nat.lt_floor_add_one A
      have h3 : ((⌊A⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hNp
      push_cast at h3
      linarith
    · have h2 : (p : ℝ) ≤ 2 * A := by
        have h3 : (p : ℝ) ≤ 2 * (⌊A⌋₊ : ℝ) := by exact_mod_cast hp2N
        have h4 := Nat.floor_le (by positivity : 0 ≤ A)
        linarith
      rw [← hApow, h1]
      have h4 : A ^ 2 ≤ A ^ (4 * 1) := pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith
  ·
    have hj2 : 2 ≤ g.natDegree := by omega
    obtain ⟨a, -, -, p, hp, hpa, hAp, hpA⟩ :=
      lem_schur hg hj2 (hroot.resolve_left h1) hm0 hR hA1000 (by linarith) (by linarith)
    exact ⟨p, hp, a, hpa, hAp, hpA.trans hApow.le⟩

open Classical in
noncomputable def cand (m j : ℕ) : Finset ℤ[X] :=
  (monicBox j (2 ^ j * m ^ j)).filter fun g => g.Monic ∧ g.natDegree = j ∧
    (∀ α ∈ (g.map (Int.castRingHom ℂ)).roots, ‖α‖ ≤ (m : ℝ)) ∧ (j = 1 ∨ ∀ a : ℤ, g.eval a ≠ 0)

open Classical in
theorem card_cand_le {m j : ℕ} (hm : 6 ≤ m) (hj : 1 ≤ j) : (cand m j).card ≤ m ^ (2 * j * j) :=
  (card_filter_le _ _).trans ((card_monicBox_le _ _).trans (box_count_le hm hj))

open Classical in
theorem nofactor_step1 {m K : ℕ} (hm : 1 ≤ m) {S : Matrix (Fin m) (Fin m) ℤ} (hS : IsSeidel S)
    {f : ℤ[X]} (hf : f.Monic) (hf1 : 1 ≤ f.natDegree) (hfK : f.natDegree ≤ K) (hfS : f ∣ S.charpoly) :
    ∃ j ∈ Icc 1 K, ∃ g ∈ cand m j, g ∣ S.charpoly := by
  obtain ⟨g, hg, hg1, hgf, hgS, hroot⟩ := exists_good_divisor hf hf1 hfS
  have hR := norm_root_le_of_dvd hS hgS
  refine ⟨g.natDegree, mem_Icc.2 ⟨hg1, hgf.trans hfK⟩, g, ?_, hgS⟩
  unfold cand
  rw [mem_filter]
  exact ⟨mem_monicBox_of_roots hg hm hR, hg, rfl, hR, hroot⟩

theorem nofactor_eventually {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 27) :
    ∀ᶠ m : ℕ in atTop, 6 ≤ m ∧ 16 * Real.log m ≤ (m : ℝ) ^ (1 / 9 - 3 * η) ∧
      144 * Real.log m ≤ (m : ℝ) ^ (1 / 9 - η) := by
  have h1 := eventually_mul_log_pow_le_rpow 16 1 (by linarith : (0 : ℝ) < 1 / 9 - 3 * η)
  have h2 := eventually_mul_log_pow_le_rpow 144 1 (by linarith : (0 : ℝ) < 1 / 9 - η)
  filter_upwards [eventually_ge_atTop 6, h1, h2] with m hm h1 h2
  simp only [pow_one] at h1 h2
  exact ⟨hm, h1, h2⟩

open Classical in
theorem thm_nofactor : Thm25 := by
  intro η hη0 hη
  filter_upwards [nofactor_eventually hη0 hη, eventually_prob_dvd_le] with m hm hP
  obtain ⟨hm6, h16, h144⟩ := hm
  set y := (m : ℝ) ^ (1 / 9 - η) with hy
  set x := (m : ℝ) ^ ((1 : ℝ) / 9) with hx
  set K := ⌊(m : ℝ) ^ η⌋₊ with hK
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hlog0 : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hu0 : 0 ≤ (m : ℝ) ^ η := by positivity
  have hmη : (m : ℝ) ^ η ≤ m := by
    calc (m : ℝ) ^ η ≤ (m : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
      _ = m := Real.rpow_one _
  have hKη : (K : ℝ) ≤ (m : ℝ) ^ η := Nat.floor_le hu0
  have hxy : x = (m : ℝ) ^ η * y := by
    rw [hx, hy, ← Real.rpow_add hm0]
    congr 1
    ring
  have hu2 : (m : ℝ) ^ η * (m : ℝ) ^ η * (m : ℝ) ^ (1 / 9 - 3 * η) = y := by
    rw [← Real.rpow_add hm0, ← Real.rpow_add hm0, hy]
    congr 1
    ring
  have hexp_y4 : (m : ℝ) + 1000 ≤ Real.exp (y / 4) := by
    have h1 : (m : ℝ) ^ 36 = Real.exp (((36 : ℕ) : ℝ) * Real.log m) := by
      rw [Real.exp_nat_mul, Real.exp_log hm0]
    have h2 : m + 1000 ≤ m ^ 36 := by
      have h3 : 6 ^ 4 ≤ m ^ 4 := Nat.pow_le_pow_left hm6 4
      have h4 : m ^ 5 ≤ m ^ 36 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have h5 : m ^ 5 = m ^ 4 * m := by ring
      nlinarith
    have h2' : ((m + 1000 : ℕ) : ℝ) ≤ ((m ^ 36 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h2'
    rw [h1] at h2'
    refine h2'.trans (Real.exp_le_exp.2 ?_)
    push_cast
    linarith
  have hcand : ∀ j ∈ Icc 1 K, ∀ g ∈ cand m j,
      probSeidel m (fun S => g ∣ S.charpoly) ≤ 3 * Real.exp (-(y / 4)) := by
    intro j hj g hg
    obtain ⟨hj1, hjK⟩ := mem_Icc.1 hj
    unfold cand at hg
    rw [mem_filter] at hg
    obtain ⟨-, hgm, hgj, hgR, hgroot⟩ := hg
    have hjR : (j : ℝ) ≤ (m : ℝ) ^ η := (Nat.cast_le.2 hjK).trans hKη
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hxj : y / 4 ≤ x / (4 * j) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity), hxy]
      have hy0 : 0 ≤ y := by positivity
      nlinarith
    have hA : (m : ℝ) + 1000 ≤ Real.exp (x / (4 * g.natDegree)) := by
      rw [hgj]
      exact hexp_y4.trans (Real.exp_le_exp.2 hxj)
    obtain ⟨p, hp, a, hpa, hAp, hpx⟩ := exists_prime_root hgm (by omega) hgR (by rw [hgj]; exact hgroot)
      hA (by rw [hgj]; exact hjR.trans hmη)
    have hp23 : 23 ≤ p := by
      have : (23 : ℝ) ≤ p := by linarith
      exact_mod_cast this
    calc probSeidel m (fun S => g ∣ S.charpoly) ≤ 3 / p := hP p hp hp23 hpx g a hpa
      _ ≤ 3 / Real.exp (x / (4 * g.natDegree)) :=
          div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) hAp
      _ = 3 * Real.exp (-(x / (4 * g.natDegree))) := by
          rw [Real.exp_neg]
          ring
      _ ≤ 3 * Real.exp (-(y / 4)) := by
          rw [hgj]
          have := Real.exp_le_exp.2 (neg_le_neg hxj)
          linarith
  have hsum_j : ∀ j ∈ Icc 1 K, ∑ g ∈ cand m j, probSeidel m (fun S => g ∣ S.charpoly) ≤
      Real.exp (y / 8) * (3 * Real.exp (-(y / 4))) := by
    intro j hj
    obtain ⟨hj1, hjK⟩ := mem_Icc.1 hj
    have hjR : (j : ℝ) ≤ (m : ℝ) ^ η := (Nat.cast_le.2 hjK).trans hKη
    have hcard : ((cand m j).card : ℝ) ≤ Real.exp (y / 8) := by
      have h1 : ((cand m j).card : ℝ) ≤ (m : ℝ) ^ (2 * j * j) := by exact_mod_cast card_cand_le hm6 hj1
      have h2 : (m : ℝ) ^ (2 * j * j) = Real.exp (((2 * j * j : ℕ) : ℝ) * Real.log m) := by
        rw [Real.exp_nat_mul, Real.exp_log hm0]
      rw [h2] at h1
      refine h1.trans (Real.exp_le_exp.2 ?_)
      have hjj : (j : ℝ) * j ≤ (m : ℝ) ^ η * (m : ℝ) ^ η :=
        mul_le_mul hjR hjR (Nat.cast_nonneg j) hu0
      have h3 := mul_le_mul_of_nonneg_right hjj hlog0
      have h4 : 16 * Real.log m * ((m : ℝ) ^ η * (m : ℝ) ^ η) ≤
          (m : ℝ) ^ (1 / 9 - 3 * η) * ((m : ℝ) ^ η * (m : ℝ) ^ η) :=
        mul_le_mul_of_nonneg_right h16 (by positivity)
      push_cast
      nlinarith
    calc ∑ g ∈ cand m j, probSeidel m (fun S => g ∣ S.charpoly)
        ≤ ∑ g ∈ cand m j, 3 * Real.exp (-(y / 4)) := sum_le_sum (hcand j hj)
      _ = (cand m j).card * (3 * Real.exp (-(y / 4))) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ Real.exp (y / 8) * (3 * Real.exp (-(y / 4))) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  have h3mη : 3 * (m : ℝ) ^ η ≤ Real.exp (y / 72) := by
    rw [Real.rpow_def_of_pos hm0]
    have hl3 : Real.log 3 ≤ Real.log m :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 3 ≤ m))
    have h1 : 3 * Real.exp (Real.log m * η) = Real.exp (Real.log 3 + Real.log m * η) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
    rw [h1]
    apply Real.exp_le_exp.2
    have h2 : Real.log m * η ≤ Real.log m * 1 := mul_le_mul_of_nonneg_left (by linarith) hlog0
    linarith
  calc probSeidel m (fun S => ∃ f : ℤ[X], f.Monic ∧ 1 ≤ f.natDegree ∧
        (f.natDegree : ℝ) ≤ (m : ℝ) ^ η ∧ f ∣ S.charpoly)
      ≤ prob (fun ω : Pairs m → Bool => ∃ j ∈ Icc 1 K, ∃ g ∈ cand m j, g ∣ (seidelOf ω).charpoly) := by
        unfold probSeidel
        refine prob_mono fun ω hω => ?_
        obtain ⟨f, hf, hf1, hfη, hfS⟩ := hω
        exact nofactor_step1 (by omega) (isSeidel_seidelOf ω) hf hf1 (Nat.le_floor hfη) hfS
    _ ≤ ∑ j ∈ Icc 1 K, prob (fun ω : Pairs m → Bool => ∃ g ∈ cand m j, g ∣ (seidelOf ω).charpoly) :=
        prob_exists_le_sum _ _
    _ ≤ ∑ j ∈ Icc 1 K, ∑ g ∈ cand m j, probSeidel m (fun S => g ∣ S.charpoly) :=
        sum_le_sum fun j _ => prob_exists_le_sum _ _
    _ ≤ ∑ j ∈ Icc 1 K, Real.exp (y / 8) * (3 * Real.exp (-(y / 4))) := sum_le_sum hsum_j
    _ = K * (Real.exp (y / 8) * (3 * Real.exp (-(y / 4)))) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    _ ≤ Real.exp (-y / 9) := by
        have hK3 : (K : ℝ) * 3 ≤ Real.exp (y / 72) := by linarith
        have he : Real.exp (y / 8) * Real.exp (-(y / 4)) = Real.exp (-(y / 8)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have he2 : Real.exp (y / 72) * Real.exp (-(y / 8)) = Real.exp (-y / 9) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc (K : ℝ) * (Real.exp (y / 8) * (3 * Real.exp (-(y / 4))))
            = ((K : ℝ) * 3) * (Real.exp (y / 8) * Real.exp (-(y / 4))) := by ring
          _ = ((K : ℝ) * 3) * Real.exp (-(y / 8)) := by rw [he]
          _ ≤ Real.exp (y / 72) * Real.exp (-(y / 8)) :=
              mul_le_mul_of_nonneg_right hK3 (Real.exp_pos _).le
          _ = Real.exp (-y / 9) := he2

end DGS
