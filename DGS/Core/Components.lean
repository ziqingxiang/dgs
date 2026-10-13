module

public import DGS.Core.Seidel
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Filter Topology Real

namespace DGS

def Thm22 : Prop :=
  Tendsto (fun n : ℕ => probG n (fun G => ∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧
    3 * logb 2 n ≤ (d : ℝ) ∧ E p d G)) atTop (𝓝 0)

def Thm23 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    Tendsto (fun n : ℕ => probG n (fun G => ∃ Q ∈ QG G, ¬ IsPermMatrix Q ∧
      ∀ p : ℕ, p.Prime → p ∣ level Q → (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε))) atTop (𝓝 0)

def Thm24 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 10 →
    Tendsto (fun n : ℕ => probG n (fun G => ∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧
      (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ) ∧ (p : ℝ) ≤ exp ((n : ℝ) ^ (1 / 10 : ℝ)) ∧
      1 ≤ d ∧ (d : ℝ) < 3 * logb 2 n ∧ E p d G)) atTop (𝓝 0)

def Thm25 : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 / 27 →
    ∀ᶠ m : ℕ in atTop, probSeidel m (fun S => ∃ f : Polynomial ℤ, f.Monic ∧ 1 ≤ f.natDegree ∧
      (f.natDegree : ℝ) ≤ (m : ℝ) ^ η ∧ f ∣ S.charpoly) ≤ exp (-(m : ℝ) ^ (1 / 9 - η) / 9)

def Thm26 : Prop :=
  Tendsto (fun n : ℕ => probG n (fun G => ∃ p d : ℕ, p.Prime ∧ p ≠ 2 ∧
    exp ((log n) ^ 6) < (p : ℝ) ∧ 1 ≤ d ∧ E p d G)) atTop (𝓝 0)

end DGS
