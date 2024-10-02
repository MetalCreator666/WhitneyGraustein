import SphereEversion.Global.Immersion

open Metric FiniteDimensional Set Function LinearMap Filter ContinuousLinearMap Complex NormedSpace
open scoped Manifold Topology

-- set_option diagnostics true

/-
  The goal is to prove the Whitney Graustein theorem.
-/

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



-- Euclidean space
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] [Fact (finrank ℝ E = 2)]
local notation "𝕊¹" => sphere (0 : E) 1
local notation "𝓡_imm" => immersionRel (𝓡 1) 𝕊¹ 𝓘(ℝ, ℂ) ℂ

#check 𝕊¹

-- Can only use this because of "open Manifold" at the start, since this command is scoped
#check 𝓡 2
-- its slash M C I for 𝓘
#check 𝓘(ℝ, E)




section loops

/- OLD
-- Structure for a loop in ℂ that is also an immersion.
structure LoopImmersion (γ : 𝕊¹ → ℂ) : Prop where
  cdiff : ContDiff ℝ ⊤ γ    -- Smooth function
  per : Periodic γ 1         -- Period of 1
  imm : ∀ t : ℝ , deriv γ t ≠ 0   -- Immersion condition (≠ 0, since Dim(𝕊¹) = 1)
-/

-- Structure for a loop in ℂ that is also an immersion.
structure LoopImmersion (γ : 𝕊¹ → ℂ) : Prop where
  cdiff : Smooth (𝓡 1) 𝓘(ℝ, ℂ) γ                -- Smooth function
  imm : ∀ t : 𝕊¹, mfderiv (𝓡 1) 𝓘(ℝ, ℂ) γ t ≠ 0 -- Immersion condition (≠ 0, since Dim(𝕊¹) = 1)


/- OLD
-- Structure for homotopy between loops
structure LoopHomotopy (Γ : ℝ → ℝ → ℂ) : Prop where
  cdiff : ContDiff ℝ ⊤ (uncurry Γ)
  imm : ∀ t : ℝ, LoopImmersion (Γ t)
-/

-- Structure for homotopy between loops
structure LoopHomotopy (Γ : ℝ → 𝕊¹ → ℂ) : Prop where
  cdiff : Smooth (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ↿Γ
  imm : ∀ t : ℝ, LoopImmersion E (Γ t)


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


axiom LoopImmersion.lift {γ : 𝕊¹ → ℂ} (γ_imm : LoopImmersion E γ) : ℝ → ℝ
axiom LoopImmersion.cdiff_lift {γ : 𝕊¹ → ℂ} (γ_imm : LoopImmersion E γ) : Smooth 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ_imm.lift --ContDiff ℝ ⊤ γ_imm.lift
axiom LoopImmersion.turningNumber {γ : 𝕊¹ → ℂ} (γ_imm : LoopImmersion E γ) : ℤ
--axiom LoopImmersion.deriv_in_complex {γ : 𝕊¹ → ℂ} (γ_imm : LoopImmersion E γ) (t : 𝕊¹) (t' : ℝ) :
--  mfderiv (𝓡 1) 𝓘(ℝ, ℂ) γ t = ‖mfderiv (𝓡 1) 𝓘(ℝ, ℂ) γ t‖ * exp (2 * Real.pi * I * γ_imm.lift E t')
axiom LoopImmersion.lift_add {γ : 𝕊¹ → ℂ} (γ_imm : LoopImmersion E γ) (t : ℝ) (k : ℤ) : γ_imm.lift E (t + k) = γ_imm.lift E t + k * γ_imm.turningNumber

-- Axiom that tells us that taking the turning number as a function from a homotopy is continuous
-- To be proven once turning number is fully defined
axiom LoopHomotopy.cont_turningNumber {Γ : ℝ → 𝕊¹ → ℂ} (Γ_hom : LoopHomotopy E Γ) : Continuous (fun t ↦ (Γ_hom.imm t).turningNumber)

-- Unused for now
-- Lemma to show that one can get turning number from lift
lemma turning_from_lift {γ : 𝕊¹ → ℂ} (γ_imm : LoopImmersion E γ) :
  γ_imm.turningNumber =  γ_imm.lift E 1 - γ_imm.lift E 0 := by
    rw[← zero_add 1, eq_sub_iff_add_eq, add_comm]
    apply symm
    simpa using γ_imm.lift_add E 0 1

end turning






section whitneygraustein

-- Give a family of formal solutions
def family_of_formal_sol : HtpyFormalSol 𝓡_imm := sorry

-- Prove that the family of formal solutions is holonomic near C := {0,1} x 𝕊¹
theorem family_of_formal_sol_hol_near_zero_one :
    ∀ᶠ s : ℝ × 𝕊¹ near {0, 1} ×ˢ univ, (family_of_formal_sol E s.1).toOneJetSec.IsHolonomicAt s.2 := by
      sorry

-- first implication whitney graustein
-- Assuming turning number is equal => ∃ homotopy
theorem whitney_graustein_left {f₀ f₁ : 𝕊¹ → ℂ} (f₀_imm : LoopImmersion E f₀) (f₁_imm : LoopImmersion E f₁)
  (eq_turn : f₀_imm.turningNumber = f₁_imm.turningNumber) :
    ∃F : ℝ → 𝕊¹ → ℂ, LoopHomotopy E F ∧ (F 0 = f₀) ∧ (F 1 = f₁) := by
      -- First step is to get H-principle result
      have ineq_rank : finrank ℝ (ℝ^1) < finrank ℝ ℂ := by simp
      let ε : 𝕊¹ → ℝ := fun _ ↦ 1
      have hε_pos : ∀ x, 0 < ε x := fun _ ↦ zero_lt_one
      have hε_cont : Continuous ε := continuous_const
      let C := ({0, 1} : Set ℝ).prod (univ : Set 𝕊¹)
      have C_closed : IsClosed C :=
        (Finite.isClosed (by simp : ({0, 1} : Set ℝ).Finite)).prod isClosed_univ
      haveI : Nontrivial E := nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = 2)
      haveI : Nonempty 𝕊¹ := (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
      haveI : IsCompact 𝕊¹ := isCompact_sphere (0 : E) 1
      haveI : SigmaCompactSpace 𝕊¹ := sigmaCompactSpace_of_locally_compact_second_countable
      rcases (immersionRel_satisfiesHPrincipleWith (𝓡 1) 𝕊¹ 𝓘(ℝ, ℂ) ℂ 𝓘(ℝ, ℝ) ℝ
        ineq_rank C_closed hε_pos hε_cont).bs (family_of_formal_sol E) (family_of_formal_sol_hol_near_zero_one E)
         with ⟨F, h₁, h₂, h₃, h₄⟩

      -- Remains to show that F is a Loophomotopy f₀ ~ f₁
      sorry



-- second implication whitney graustein
-- Assuming ∃ homotopy => turning number eq
theorem whitney_graustein_right {f₀ f₁ : 𝕊¹ → ℂ} (f₀_imm : LoopImmersion E f₀) (f₁_imm : LoopImmersion E f₁)
  (hom : ∃ F : ℝ → 𝕊¹ → ℂ, LoopHomotopy E F ∧ (F 0 = f₀) ∧ (F 1 = f₁)) :
    f₀_imm.turningNumber = f₁_imm.turningNumber := by

      -- choose a working F and extract its properties
      let F := Classical.choose hom
      have loop_hom : LoopHomotopy E F := by
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
        exact LoopHomotopy.cont_turningNumber E loop_hom

      -- Prove continuous G => G constant
      have G_const : ∀ t s, G t = G s := by
        have hyp : IsLocallyConstant G :=
         (IsLocallyConstant.iff_continuous G).mpr G_cont
        apply IsLocallyConstant.iff_is_const.mp hyp

      -- Prove that therefore turning numbers are equal
      rw[← G₀, ← G₁]
      exact G_const 0 1


-- for completeness the theorem in its entirety
theorem whitney_graustein {f₀ f₁ : 𝕊¹ → ℂ} (f₀_imm : LoopImmersion E f₀) (f₁_imm : LoopImmersion E f₁) :
  (∃F : ℝ → 𝕊¹ → ℂ, LoopHomotopy E F ∧ (F 0 = f₀) ∧ (F 1 = f₁)) ↔ (f₀_imm.turningNumber = f₁_imm.turningNumber) :=
    Iff.intro (whitney_graustein_right E f₀_imm f₁_imm) (whitney_graustein_left E f₀_imm f₁_imm)

end whitneygraustein
