import SphereEversion.Global.Immersion

open Metric FiniteDimensional Set Function LinearMap Filter ContinuousLinearMap Complex NormedSpace
open scoped Manifold Topology

/-
  The goal is to prove the Whitney Graustein theorem.
-/

#check immersionRel_satisfiesHPrincipleWith

lemma fin_rank_c : finrank ℝ ℂ = 2 := by exact finrank_real_complex
lemma fin_rank_r : finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1 := by simp
lemma rank_r_le_rank_c : finrank ℝ (EuclideanSpace ℝ (Fin 1)) < finrank ℝ ℂ := by simp
def ε : (ℝ^1) → ℝ := fun _ ↦ 1

#check (immersionRel_satisfiesHPrincipleWith (𝓡 1) (ℝ^1) 𝓘(ℝ, ℂ) ℂ 𝓘(ℝ, ℝ) ℝ rank_r_le_rank_c
  ((Finite.isClosed (by simp : ({0, 1} : Set ℝ).Finite)).prod isClosed_univ)
   (fun _ ↦ zero_lt_one) (continuous_const)).bs

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
#check immersionRel (𝓡 1) (ℝ^1) 𝓘(ℝ, E) E

/-

-- TODO the other half of the iff statement. namely that the turning number of f₀ and f₁ is equal
-- To do this one needs to properly define turning number and I don't think this has been done so far.
theorem whitney_graustein {f₀ f₁ : 𝕊¹ → E} (h₀ : Immersion (𝓡 1) 𝓘(ℝ, E) f₀ ⊤)
  (h₁ : Immersion (𝓡 1) 𝓘(ℝ, E) f₁ ⊤) :
    ∃ F : ℝ → 𝕊¹ → E,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ⊤ ↿F ∧
        (F 0 = f₀) ∧ (F 1 = f₁) ∧
        ∀ t, Immersion (𝓡 1) 𝓘(ℝ, E) (F t) ⊤ := by sorry

-/





section loops

-- Structure for a loop in ℂ that is also an immersion.
structure LoopImmersion (γ : ℝ → ℂ) : Prop where
  cdiff : ContDiff ℝ ⊤ γ        -- Smooth function
  per : Periodic γ 1            -- Period of 1
  imm : ∀ t : ℝ, deriv γ t ≠ 0  -- Immersion condition (≠ 0, since Dim(𝕊¹) = 1)

-- Structure for homotopy between loops
structure LoopHomotopy (Γ : ℝ → ℝ → ℂ) : Prop where
  cdiff : ContDiff ℝ ⊤ (uncurry Γ)
  imm : ∀ t : ℝ, LoopImmersion (Γ t)

end loops





section turning

/-

IMPORTANT

To do the Whitney Graustein theorem fully, one needs the proper definition for
turning number of a loop. This invokes the definition of a winding number and
thus needs covering space theory. In particular, we want to be able to count
the windings of a loop around a point, for which we would need the homotopy lifting
property.

To solve this, we assume for now that this exists and build on top of the assumptions.
In particular we will assume the following regarding turning number:
  -> For all Loopimmersions there exists a smooth lift ℝ → ℝ
  -> γ'(t) = |γ'(t)|e^(2πi*lift(t))
  -> The turning number is a number in ℤ
  -> lift(t + k) = lift(t) + k * turningNumber (i.e. going up in values of ℤ)

END

-/

variable {γ : ℝ → ℂ} (γ_imm : LoopImmersion γ)

axiom LoopImmersion.lift {γ : ℝ → ℂ} (γ_imm : LoopImmersion γ) : ℝ → ℝ
axiom LoopImmersion.cdiff_lift : ContDiff ℝ ⊤ γ_imm.lift
axiom LoopImmersion.turningNumber {γ : ℝ → ℂ} (γ_imm : LoopImmersion γ) : ℤ
axiom LoopImmersion.deriv_in_complex (t : ℝ) : deriv γ t = ‖deriv γ t‖ * exp (2 * Real.pi * I * γ_imm.lift t)
axiom LoopImmersion.lift_add (t : ℝ) (k : ℤ) : γ_imm.lift (t + k) = γ_imm.lift t + k * γ_imm.turningNumber

-- Axiom that tells us that taking the turning number as a function from a homotopy is continuous
-- To be proven once turning number is fully defined
axiom LoopHomotopy.cont_turningNumber {Γ : ℝ → ℝ → ℂ} (Γ_hom : LoopHomotopy Γ) : Continuous (fun t ↦ (Γ_hom.imm t).turningNumber)

-- Unused for now
-- Lemma to show that one can get turning number from lift
lemma turning_from_lift {γ : ℝ → ℂ} (γ_imm : LoopImmersion γ) :
  γ_imm.turningNumber =  γ_imm.lift 1 - γ_imm.lift 0 := by
    rw[← zero_add 1, eq_sub_iff_add_eq, add_comm]
    apply symm
    simpa using γ_imm.lift_add 0 1


end turning





section whitneygraustein


-- first implication whitney graustein
-- Assuming turning number is equal => ∃ homotopy
theorem whitney_graustein_left {f₀ f₁ : ℝ → ℂ} (f₀_imm : LoopImmersion f₀) (f₁_imm : LoopImmersion f₁)
  (eq_turn : f₀_imm.turningNumber = f₁_imm.turningNumber) :
    ∃F : ℝ → ℝ → ℂ, LoopHomotopy F ∧ (F 0 = f₀) ∧ (F 1 = f₁) := by
      sorry

-- second implication whitney graustein
-- Assuming ∃ homotopy => turning number eq
theorem whitney_graustein_right {f₀ f₁ : ℝ → ℂ} (f₀_imm : LoopImmersion f₀) (f₁_imm : LoopImmersion f₁)
  (hom : ∃ F : ℝ → ℝ → ℂ, LoopHomotopy F ∧ (F 0 = f₀) ∧ (F 1 = f₁)) :
    f₀_imm.turningNumber = f₁_imm.turningNumber := by

      -- choose a working F and extract its properties
      let F := Classical.choose hom
      have loop_hom : LoopHomotopy F := by
        exact (Classical.choose_spec hom).left
      have F₀ : F 0 = f₀ := by
        exact (Classical.choose_spec hom).right.left
      have F₁ : F 1 = f₁ := by
        exact (Classical.choose_spec hom).right.right

      -- Construct the function ℝ → ℤ that determines turning number per time frame
      let G := fun t ↦ (loop_hom.imm t).turningNumber
      have G₀ : G 0 = f₀_imm.turningNumber := by
        simp_rw[G, F₀]
      have G₁ : G 1 = f₁_imm.turningNumber := by
        simp_rw[G, F₁]

      -- Prove continuity of G (taking turning number)
      -- Uses axiom cont_turningNumber!!
      have G_cont : Continuous G := by
        exact LoopHomotopy.cont_turningNumber loop_hom

      -- Prove continuous G => G constant
      have G_const : ∀ t s, G t = G s := by
        have hyp : IsLocallyConstant G :=
         (IsLocallyConstant.iff_continuous G).mpr G_cont
        apply IsLocallyConstant.iff_is_const.mp hyp

      -- Prove that therefore turning numbers are equal
      rw[← G₀, ← G₁]
      exact G_const 0 1


-- for completeness the theorem in its entirety
theorem whitney_graustein {f₀ f₁ : ℝ → ℂ} (f₀_imm : LoopImmersion f₀) (f₁_imm : LoopImmersion f₁) :
  (∃F : ℝ → ℝ → ℂ, LoopHomotopy F ∧ (F 0 = f₀) ∧ (F 1 = f₁)) ↔ (f₀_imm.turningNumber = f₁_imm.turningNumber) :=
    Iff.intro (whitney_graustein_right f₀_imm f₁_imm) (whitney_graustein_left f₀_imm f₁_imm)

end whitneygraustein
