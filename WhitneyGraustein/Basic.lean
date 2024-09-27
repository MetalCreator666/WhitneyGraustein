import SphereEversion.Global.Immersion

open Metric FiniteDimensional Set Function LinearMap Filter ContinuousLinearMap
open scoped Manifold Topology

/-
  The goal is to prove the Whitney Graustein theorem.
-/

#check immersionRel_satisfiesHPrincipleWith

/-
  First; we need to define the statement of the Whitney Graustein theorem

  The Whitney Graustein Theorem is the following:
    "two immersions are regularly homotopic if and only if
     they have the same turning number"

    "Assume f₀, f₁ : 𝕊¹ → ℝ² immersions, then there exists a smooth homotopy
     F : 𝕊¹ × [0,1] → ℝ² of immersions between f₀ and f₁ if and only if
     their turning number is equal, i.e. w(f₀') = w(f₁')"

  Note:
    Winding number of γ is number of loops around 0
    Turning number of γ is winding number of γ'
-/

#check Immersion
#check sphere (0 : ℝ^2) 1

-- Euclidean space
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

#check sphere (0 : E) 1

local notation "𝕊¹" => sphere (0 : E) 1

#check 𝕊¹

-- Can only use this because of "open Manifold" at the start, since this command is scoped
#check 𝓡 2
-- its slash M C I for 𝓘
#check 𝓘(ℝ, E)
#check Immersion (𝓡 1) 𝓘(ℝ, E) (fun x : 𝕊¹ ↦ (x : E)) ⊤

-- TODO the other half of the iff statement. namely that the turning number of f₀ and f₁ is equal
-- To do this one needs to properly define turning number and I don't think this has been done so far.
theorem whitney_graustein {f₀ f₁ : 𝕊¹ → E} (h₀ : Immersion (𝓡 1) 𝓘(ℝ, E) f₀ ⊤)
  (h₁ : Immersion (𝓡 1) 𝓘(ℝ, E) f₁ ⊤) :
    ∃ F : ℝ → 𝕊¹ → E,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ⊤ ↿F ∧
        (F 0 = f₀) ∧ (F 1 = f₁) ∧
        ∀ t, Immersion (𝓡 1) 𝓘(ℝ, E) (F t) ⊤ := by sorry
