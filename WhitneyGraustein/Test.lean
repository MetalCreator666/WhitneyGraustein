import Mathlib

open scoped Manifold

notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
notation "𝕊¹" => Metric.sphere (0 : ℝ²) 1

variable {x y : Fin 1}

lemma vector_eq_val_mult_unit (s : 𝕊¹) (v : TangentSpace 𝓘(ℝ, ℝ¹) s):
  ∃v' : ℝ, v = v' • (fun x ↦ 1 : TangentSpace 𝓘(ℝ, ℝ¹) s) := by
    use v 0
    rw [@Pi.smul_def]
    simp
    have h2 : ∀x y : Fin 1, v x = (fun _ ↦ v 0) y := by
      intro x _
      let x := Fin.fin_one_eq_zero x
      exact congrArg v x
    apply (Function.funext_iff_of_subsingleton x y).mp (h2 x y)




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

--lemma deriv_iloop_eq_mloop {γ : 𝕊¹ → ℝ²} (γ_iloop : ILoop γ) :
  --MLoop (fun t : 𝕊¹ ↦ (mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ t ...)) := by sorry
