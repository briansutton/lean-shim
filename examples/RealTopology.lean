import Mathlib.Basic.Real.Basic

def Neighborhood (x₀ : ℝ) (r : ℝ) (S : Set ℝ) : Set ℝ :=
  { x : ℝ | x ∈ S ∧ |x - x₀| < r }

def IsInteriorTo (x₀ : ℝ) (E : Set ℝ) (S : Set ℝ) : Prop :=
  ∃ r : ℝ, r > 0 ∧ (Neighborhood x₀ r S) ⊆ E

def Interior (E : Set ℝ) (S : Set ℝ) : Set ℝ :=
  { x : ℝ | IsInteriorTo x E S }
