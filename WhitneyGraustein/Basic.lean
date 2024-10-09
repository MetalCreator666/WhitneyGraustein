import SphereEversion.Global.Immersion

noncomputable section

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
local notation "𝓡_imm" => immersionRel (𝓡 1) 𝕊¹ 𝓘(ℝ, E) E


section loops

-- Structure for a loop in E that is also an immersion.
structure LoopImmersion (γ : 𝕊¹ → E) : Prop where
  -- Smooth function
  cdiff : Smooth (𝓡 1) 𝓘(ℝ, E) γ
  -- Immersion condition (≠ 0, since Dim(𝕊¹) = 1)
  -- imm : ∀ t : 𝕊¹, mfderiv (𝓡 1) 𝓘(ℝ, E) γ t ≠ 0
  imm :  ∀ t : 𝕊¹, Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ t)

-- Structure for homotopy between loops
structure LoopHomotopy (Γ : ℝ → 𝕊¹ → E) : Prop where
  -- Smooth as function ℝ × 𝕊¹ → ℂ
  cdiff : Smooth (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ↿Γ
  -- LoopImmersion at every point
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
-/

axiom LoopImmersion.lift {γ : 𝕊¹ → E} (γ_imm : LoopImmersion E γ) : ℝ → ℝ
axiom LoopImmersion.cdiff_lift {γ : 𝕊¹ → E} (γ_imm : LoopImmersion E γ) : Smooth 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ_imm.lift --ContDiff ℝ ⊤ γ_imm.lift
axiom LoopImmersion.turningNumber {γ : 𝕊¹ → E} (γ_imm : LoopImmersion E γ) : ℤ
axiom LoopImmersion.lift_add {γ : 𝕊¹ → E} (γ_imm : LoopImmersion E γ) (t : ℝ) (k : ℤ) : γ_imm.lift E (t + k) = γ_imm.lift E t + k * γ_imm.turningNumber

-- Axiom that tells us that taking the turning number as a function from a homotopy is continuous
-- To be proven once turning number is fully defined
axiom LoopHomotopy.cont_turningNumber {Γ : ℝ → 𝕊¹ → E} (Γ_hom : LoopHomotopy E Γ) : Continuous (fun t ↦ (Γ_hom.imm t).turningNumber)

--lemma aux (x : E) : E = TangentSpace 𝓘(ℝ, E) x := by exact rfl
--lemma aux2 (x : ℝ^1) : ℝ^1 = TangentSpace (𝓡 1) x := by exact rfl
axiom eq_turn_hom {γ₀ γ₁ : 𝕊¹ → E} (γ₀_imm : LoopImmersion E γ₀) (γ₁_imm : LoopImmersion E γ₁)
  (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber) :
  ∃G : ℝ × 𝕊¹ → E →L[ℝ] E,
    (∀ (x₀ : ℝ × 𝕊¹), SmoothAt (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E →L[ℝ] E) G x₀) ∧
      -- Idea here is that it becomes a homotopy of endomorphisms
      -- Thus moving the space around the loops to homotope the loops
      -- It becomes a homotopy of the space E instead of a homotopy of the loops
      (∀ s : 𝕊¹, G (0,s) = ContinuousLinearMap.id ℝ E) ∧
        -- TODO : This needs to change, instead of the id, we want this to be some endomorphism
        -- that changes γ₀ into γ₁ in general. For sphere eversion, one would choose this because
        -- rotation map is easy to choose as endomorphisms, because here it would simply become w ↦ -w.
        -- In our case another way needs to be done
        (∀ s : 𝕊¹, G (1,s) = ContinuousLinearMap.id ℝ E) ∧
          (∀ x₀ : ℝ × 𝕊¹, Injective (G x₀))

-- Unused for now
-- Lemma to show that one can get turning number from lift
lemma turning_from_lift {γ : 𝕊¹ → E} (γ_imm : LoopImmersion E γ) :
  γ_imm.turningNumber =  γ_imm.lift E 1 - γ_imm.lift E 0 := by
    rw[← zero_add 1, eq_sub_iff_add_eq, add_comm]
    apply symm
    simpa using γ_imm.lift_add E 0 1


end turning



section whitneygraustein

theorem smooth_bs_wg {γ₀ γ₁ : 𝕊¹ → E} (γ₀_imm : LoopImmersion E γ₀) (γ₁_imm : LoopImmersion E γ₁) :
  Smooth (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E)
      fun p : ℝ × 𝕊¹ ↦ (1 - p.1) • (γ₀ p.2 : E) + p.1 • (γ₁ p.2 : E) := by
        refine (ContMDiff.smul ?_ ?_).add (contMDiff_fst.smul ?_)
        exact (contDiff_const.sub contDiff_id).contMDiff.comp contMDiff_fst
        exact γ₀_imm.cdiff.contMDiff.comp contMDiff_snd
        exact γ₁_imm.cdiff.contMDiff.comp contMDiff_snd


def formal_solution_aux2 {γ₀ γ₁ : 𝕊¹ → E} (γ₀_imm : LoopImmersion E γ₀) (γ₁_imm : LoopImmersion E γ₁) (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber):
  FamilyOneJetSec (𝓡 1) 𝕊¹ 𝓘(ℝ, E) E 𝓘(ℝ, ℝ) ℝ :=
    familyJoin (smooth_bs_wg E γ₀_imm γ₁_imm) <|
      familyTwist (drop (oneJetExtSec ⟨((↑) : 𝕊¹ → E), contMDiff_coe_sphere⟩))
        (fun p : ℝ × 𝕊¹ ↦ (eq_turn_hom E γ₀_imm γ₁_imm turn_eq).choose p)
        ((eq_turn_hom E γ₀_imm γ₁_imm turn_eq).choose_spec.left)

def formal_solution_aux {γ₀ γ₁ : 𝕊¹ → E} (γ₀_imm : LoopImmersion E γ₀) (γ₁_imm : LoopImmersion E γ₁) (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber):
  HtpyFormalSol 𝓡_imm :=
    {
      formal_solution_aux2 E γ₀_imm γ₁_imm turn_eq with
      is_sol' := fun t x ↦ ((eq_turn_hom E γ₀_imm γ₁_imm turn_eq).choose_spec.right.right.right (t,x)).comp (mfderiv_coe_sphere_injective x)
    }

def family_of_formal_sol {γ₀ γ₁ : 𝕊¹ → E} (γ₀_imm : LoopImmersion E γ₀) (γ₁_imm : LoopImmersion E γ₁) (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber):
  HtpyFormalSol 𝓡_imm := (formal_solution_aux E γ₀_imm γ₁_imm turn_eq).reindex ⟨smoothStep, contMDiff_iff_contDiff.mpr smoothStep.smooth⟩

@[simp]
theorem formal_sol_bs {γ₀ γ₁ : 𝕊¹ → E} (γ₀_imm : LoopImmersion E γ₀) (γ₁_imm : LoopImmersion E γ₁) (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber) (t : ℝ):
    (family_of_formal_sol E γ₀_imm γ₁_imm turn_eq t).bs = fun x : 𝕊¹ ↦
      (1 - smoothStep t : ℝ) • (γ₀ x : E) + (smoothStep t : ℝ) • (γ₁ x : E) :=
  rfl

theorem formal_sol_zero {γ₀ γ₁ : 𝕊¹ → E} (γ₀_imm : LoopImmersion E γ₀) (γ₁_imm : LoopImmersion E γ₁) (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber) (x : 𝕊¹):
  (family_of_formal_sol E γ₀_imm γ₁_imm turn_eq 0).bs x = γ₀ x := by simp

theorem formal_sol_one {γ₀ γ₁ : 𝕊¹ → E} (γ₀_imm : LoopImmersion E γ₀) (γ₁_imm : LoopImmersion E γ₁) (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber) (x : 𝕊¹):
  (family_of_formal_sol E γ₀_imm γ₁_imm turn_eq 1).bs x = γ₁ x := by simp

-- TODO find the right properties for G above to complete
theorem formal_sol_hol_at_zero {γ₀ γ₁ : 𝕊¹ → E} (γ₀_imm : LoopImmersion E γ₀) (γ₁_imm : LoopImmersion E γ₁) (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber) {t : ℝ} (ht : t < 1 / 4) :
    (family_of_formal_sol E γ₀_imm γ₁_imm turn_eq t).toOneJetSec.IsHolonomic := by
  intro x
  change
    mfderiv (𝓡 1) 𝓘(ℝ, E) (fun y : 𝕊¹ ↦ ((1 : ℝ) - smoothStep t) • (γ₀ y : E) +
      smoothStep t • (γ₁ y : E)) x =
      ((eq_turn_hom E γ₀_imm γ₁_imm turn_eq).choose (smoothStep t, x)).comp (mfderiv (𝓡 1) 𝓘(ℝ, E) (fun y : 𝕊¹ ↦ (y : E)) x)
  simp_rw [smoothStep.of_lt ht, (eq_turn_hom E γ₀_imm γ₁_imm turn_eq).choose_spec.right.left, ContinuousLinearMap.id_comp]
  congr
  ext y
  simp [smoothStep.of_lt ht]
  sorry

-- TODO find the right properties for G above to complete
theorem formal_sol_hol_at_one {γ₀ γ₁ : 𝕊¹ → E} (γ₀_imm : LoopImmersion E γ₀) (γ₁_imm : LoopImmersion E γ₁) (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber) {t : ℝ} (ht : 3 / 4 < t) :
    (family_of_formal_sol E γ₀_imm γ₁_imm turn_eq t).toOneJetSec.IsHolonomic := by
  intro x
  change
    mfderiv (𝓡 1) 𝓘(ℝ, E) (fun y : 𝕊¹ ↦ ((1 : ℝ) - smoothStep t) • (γ₀ y : E) +
      smoothStep t • (γ₁ y : E)) x =
      ((eq_turn_hom E γ₀_imm γ₁_imm turn_eq).choose (smoothStep t, x)).comp (mfderiv (𝓡 1) 𝓘(ℝ, E) (fun y : 𝕊¹ ↦ (y : E)) x)
  trans mfderiv (𝓡 1) 𝓘(ℝ, E) (fun y : 𝕊¹ ↦ (γ₁ y : E)) x
  · congr 2
    ext y
    simp [smoothStep.of_gt ht]
  ext v
  erw [ContinuousLinearMap.coe_comp', Function.comp_apply, smoothStep.of_gt ht]
  rw [(eq_turn_hom E γ₀_imm γ₁_imm turn_eq).choose_spec.right.right.left];
  sorry


-- Prove that the family of formal solutions is holonomic near C := {0,1} x 𝕊¹
theorem family_of_formal_sol_hol_near_zero_one {γ₀ γ₁ : 𝕊¹ → E} (γ₀_imm : LoopImmersion E γ₀) (γ₁_imm : LoopImmersion E γ₁) (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber):
    ∀ᶠ s : ℝ × 𝕊¹ near {0, 1} ×ˢ univ, (family_of_formal_sol E γ₀_imm γ₁_imm turn_eq s.1).toOneJetSec.IsHolonomicAt s.2 := by
      have : (Iio (1 / 4 : ℝ) ∪ Ioi (3 / 4)) ×ˢ (univ : Set 𝕊¹) ∈ 𝓝ˢ (({0, 1} : Set ℝ) ×ˢ univ) := by
        refine ((isOpen_Iio.union isOpen_Ioi).prod isOpen_univ).mem_nhdsSet.mpr ?_
        rintro ⟨s, x⟩ ⟨hs, hx⟩
        refine ⟨?_, mem_univ _⟩
        simp_rw [mem_insert_iff, mem_singleton_iff] at hs
        rcases hs with (rfl | rfl)
        · exact Or.inl (show (0 : ℝ) < 1 / 4 by norm_num)
        · exact Or.inr (show (3 / 4 : ℝ) < 1 by norm_num)
      filter_upwards [this]
      rintro ⟨t, x⟩ ⟨ht | ht, _hx⟩
      · exact formal_sol_hol_at_zero E γ₀_imm γ₁_imm turn_eq ht x
      · exact formal_sol_hol_at_one E γ₀_imm γ₁_imm turn_eq ht x

-- first implication whitney graustein
-- Assuming turning number is equal => ∃ homotopy
theorem whitney_graustein_left {f₀ f₁ : 𝕊¹ → E} (f₀_imm : LoopImmersion E f₀) (f₁_imm : LoopImmersion E f₁)
  (eq_turn : f₀_imm.turningNumber = f₁_imm.turningNumber) :
    ∃F : ℝ → 𝕊¹ → E, LoopHomotopy E F ∧ (F 0 = f₀) ∧ (F 1 = f₁) := by
      -- First step is to get H-principle result
      have rankE : finrank ℝ E = 2 := Fact.out
      have ineq_rank : finrank ℝ (ℝ^1) < finrank ℝ E := by simp [rankE]
      let ε : 𝕊¹ → ℝ := fun _ ↦ 1
      have hε_pos : ∀ x, 0 < ε x := fun _ ↦ zero_lt_one
      have hε_cont : Continuous ε := continuous_const
      haveI : Nontrivial E := nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = 2)
      haveI : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_eq_succ rankE
      haveI : Nonempty 𝕊¹ := (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
      haveI : IsCompact 𝕊¹ := isCompact_sphere (0 : E) 1
      haveI : SigmaCompactSpace 𝕊¹ := sigmaCompactSpace_of_locally_compact_second_countable
      rcases (immersionRel_satisfiesHPrincipleWith (𝓡 1) 𝕊¹ 𝓘(ℝ, E) E 𝓘(ℝ, ℝ) ℝ
        ineq_rank ((Finite.isClosed (by simp : ({0, 1} : Set ℝ).Finite)).prod isClosed_univ) hε_pos hε_cont).bs
          (family_of_formal_sol E f₀_imm f₁_imm eq_turn)
            (family_of_formal_sol_hol_near_zero_one E f₀_imm f₁_imm eq_turn)
              with ⟨F, h₁, h₂, _, h₄⟩
      have := h₂.forall_mem principal_le_nhdsSet

      -- Remains to show that F is a Loophomotopy f₀ ~ f₁
      use F
      constructor
      refine { cdiff := h₁, imm := ?h.left.imm }
      intro t
      refine { cdiff := ?h.left.imm.cdiff, imm := ?h.left.imm.imm }
      exact Smooth.uncurry_left 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ^1) 𝓘(ℝ, E) h₁ t
      exact fun t_1 ↦ h₄ t t_1
      constructor
      ext x
      rw [this (0, x) (by simp)]
      apply formal_sol_zero E f₀_imm f₁_imm eq_turn
      ext x
      rw [this (1, x) (by simp)]
      apply formal_sol_one E f₀_imm f₁_imm eq_turn

-- second implication whitney graustein
-- Assuming ∃ homotopy => turning number eq
theorem whitney_graustein_right {f₀ f₁ : 𝕊¹ → E} (f₀_imm : LoopImmersion E f₀) (f₁_imm : LoopImmersion E f₁)
  (hom : ∃ F : ℝ → 𝕊¹ → E, LoopHomotopy E F ∧ (F 0 = f₀) ∧ (F 1 = f₁)) :
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
theorem whitney_graustein {f₀ f₁ : 𝕊¹ → E} (f₀_imm : LoopImmersion E f₀) (f₁_imm : LoopImmersion E f₁) :
  (∃F : ℝ → 𝕊¹ → E, LoopHomotopy E F ∧ (F 0 = f₀) ∧ (F 1 = f₁)) ↔ (f₀_imm.turningNumber = f₁_imm.turningNumber) :=
    Iff.intro (whitney_graustein_right E f₀_imm f₁_imm) (whitney_graustein_left E f₀_imm f₁_imm)

end whitneygraustein
