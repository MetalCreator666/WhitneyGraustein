import Mathlib




noncomputable section

-- Notations used throughout the project
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
notation "𝕊¹" => Metric.sphere (0 : ℝ²) 1


/-
  This file is a collection of important definitions and theorems
  necessary to prove the Whitney-Graustein theorem. In particular
  it contains the setup for the `winding number` of maps 𝕊¹ → 𝕊¹,
  thus containing information on lifts etc.

  ...
-/

-- The natural projection `ℝ → 𝕊¹`
def nat_proj : ℝ → 𝕊¹ :=
  fun x ↦ ⟨![Real.cos (2 * Real.pi * x), Real.sin (2 * Real.pi * x)],
    by simp [EuclideanSpace.norm_eq]⟩

lemma nat_proj_surj : Function.Surjective nat_proj := by
  intro a
  sorry

-- All points that can be used as startpoints for a lift
def startpoints (f : 𝕊¹ → 𝕊¹) : Set ℝ := {x | nat_proj x = f ⟨![1, 0], by simp [EuclideanSpace.norm_eq]⟩}

lemma existence_startpoint (f : 𝕊¹ → 𝕊¹) : ∃a : ℝ, nat_proj a = f ⟨![1, 0], by simp [EuclideanSpace.norm_eq]⟩ := by
  sorry

-- The general definition of a lift of a map between circles `ℝ → ℝ` at a point a
-- It takes a the point `a` as the startpoint of the lift
-- Always assuming that moving counter clockwise is lowering and vice versa
structure Lift (f : 𝕊¹ → 𝕊¹) (a : ℝ)
  (ha : a ∈ startpoints f)
    (F : ℝ → ℝ) : Prop where
        start : F 0 = a
        comp_nat_proj : ∀ t : ℝ, nat_proj (F t) = f (nat_proj t)

-- Axiom that gives existence of lifts
axiom existence_lift (f : 𝕊¹ → 𝕊¹) :
  ∀a : startpoints f,
    ∃!F : ℝ → ℝ, Lift f a (by exact Subtype.coe_prop a) F

def winding_number (f : 𝕊¹ → 𝕊¹) : ℤ := sorry
