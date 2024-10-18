import Mathlib
import SphereEversion.Global.Immersion

open scoped Manifold

notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
notation "𝕊¹" => Metric.sphere (0 : ℝ²) 1

-- Smooth loop around zero
structure MLoop (γ : 𝕊¹ → ℝ²) : Prop where
  smooth : Smooth (𝓡 1) 𝓘(ℝ, ℝ²) γ
  around_zero : ∀x : 𝕊¹, γ x ≠ 0

-- Immersion loop
structure ILoop (γ : 𝕊¹ → ℝ²) : Prop where
  smooth : Smooth (𝓡 1) 𝓘(ℝ, ℝ²) γ
  -- Injectivity of derivative in this case (dim(𝕊¹) = 1)
  imm :  ∀ t : 𝕊¹, mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ t ≠ 0

-- Now, one can take the function `t ↦ Dγ(t)(e)`
-- where `e is the standard unit vector` to get a `MLoop 𝕊¹ → ℝ²`

lemma deriv_iloop_eq_mloop {γ : 𝕊¹ → ℝ²} (γ_iloop : ILoop γ) :
  MLoop (fun t : 𝕊¹ ↦ (mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ t ...)) := by sorry
