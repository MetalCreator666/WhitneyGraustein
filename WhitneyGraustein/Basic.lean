import SphereEversion.Global.Immersion
import WhitneyGraustein.WindingNumber

noncomputable section

open InnerProductSpace Metric FiniteDimensional Set Function LinearMap Filter ContinuousLinearMap Complex NormedSpace
open scoped Manifold Topology

-- set_option diagnostics true

/-
  The goal is to prove the Whitney Graustein theorem.
-/

/-
  The Whitney Graustein Theorem is the following:
    "two immersions are regularly homotopic if and only if
     they have the same turning number"

    "Assume f₀, f₁ : 𝕊¹ → ℝ² immersions, then there exists a smooth homotopy
     F : 𝕊¹ × [0,1] → ℝ² of immersions between f₀ and f₁ if and only if
     their turning number is equal, i.e. w(f₀') = w(f₁')"
-/

-- Notation used
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] [Fact (finrank ℝ E = 2)]
local notation "𝓡_imm" => immersionRel (𝓡 1) 𝕊¹ 𝓘(ℝ, ℝ²)  ℝ²

section loops

-- Structure for a loop in E that is also an immersion.
structure LoopImmersion (γ : 𝕊¹ → ℝ²) : Prop where
  -- Smooth function
  cdiff : Smooth (𝓡 1) 𝓘(ℝ, ℝ²) γ
  -- Immersion condition
  imm :  ∀ t : 𝕊¹, Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ t)

-- Structure for homotopy between LoopImmersions
structure RegularHomotopy (Γ : ℝ → 𝕊¹ → ℝ²) : Prop where
  -- Smooth as function ℝ × 𝕊¹ → E
  cdiff : Smooth (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ²) ↿Γ
  -- LoopImmersion at every point
  imm : ∀ t : ℝ, LoopImmersion (Γ t)

end loops


section lemmas

axiom inj_def {γ : 𝕊¹ → ℝ²} (loop_imm : LoopImmersion γ) :
  (∀ t : 𝕊¹, Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ t)) ↔ (∀ t : 𝕊¹, mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ t ≠ 0)

def to_circle (x : ℝ²) (hx : x ≠ 0) : 𝕊¹ := ⟨‖x‖⁻¹ • x, by
  simp only [mem_sphere_iff_norm, sub_zero]; rw [@norm_smul]; rw [@norm_inv]; rw [@norm_norm]; simp [hx]⟩

-- TODO lemma stating that a Loopimmersion has a smoothcircleloop as derivative REWRITING?
-- TODO lemma stating that thus a Loopimmersion has lifts of its derivative with a winding number
-- TODO definition stating that winding number of Loopimmersion deriv is called turning number
-- TODO lemma stating that eq turning number iff homotopy between deriv
-- TODO lemma stating that this homotopy can be written as a homotopy between ℝ² and ℝ²



end lemmas







section turning

/-
TODO: Structure the axioms in a way that reflects the mathematics as we know it.
Making sure that single axioms don't blackbox several theorems/definitions at once.

IMPORTANT

To do the Whitney Graustein theorem fully, one needs the proper definition for
turning number of a loop. This invokes the definition of a winding number and
thus needs covering space theory. In particular, we want to be able to count
the windings of a loop around a point, for which we would need the homotopy lifting
property.

To solve this, we assume for now that this exists and build on top of the assumptions.
In particular we will assume the following regarding turning number:
-/



axiom LoopImmersion.lift {γ : 𝕊¹ → ℝ²} (γ_imm : LoopImmersion γ) : ℝ → ℝ
axiom LoopImmersion.cdiff_lift {γ : 𝕊¹ → ℝ²} (γ_imm : LoopImmersion γ) : Smooth 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ_imm.lift
axiom LoopImmersion.turningNumber {γ : 𝕊¹ → ℝ²} (γ_imm : LoopImmersion γ) : ℤ
axiom LoopImmersion.lift_add {γ : 𝕊¹ → ℝ²} (γ_imm : LoopImmersion γ) (t : ℝ) (k : ℤ) :
  γ_imm.lift (t + k) = γ_imm.lift t + k * γ_imm.turningNumber

-- Axiom that tells us that taking the turning number as a function from a homotopy is continuous
-- To be proven once turning number is fully defined
axiom LoopHomotopy.cont_turningNumber {Γ : ℝ → 𝕊¹ → ℝ²} (Γ_hom : RegularHomotopy Γ) :
  Continuous (fun t ↦ (Γ_hom.imm t).turningNumber)

--lemma aux (x : E) : E = TangentSpace 𝓘(ℝ, E) x := by exact rfl
--lemma aux2 (x : ℝ^1) : ℝ^1 = TangentSpace (𝓡 1) x := by exact rfl
axiom eq_turn_hom {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber) :
  ∃G : ℝ × 𝕊¹ → ℝ² →L[ℝ] ℝ²,
    (∀ (x₀ : ℝ × 𝕊¹), SmoothAt (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ² →L[ℝ] ℝ²) G x₀) ∧
      -- Idea here is that it becomes a homotopy of endomorphisms
      -- Thus moving the space around the loops to homotope the loops
      -- It becomes a homotopy of the space E instead of a homotopy of the loops
      (∀ s : 𝕊¹, G (0,s) = ContinuousLinearMap.id ℝ ℝ²) ∧
        -- TODO : This needs to change, instead of the id, we want this to be some endomorphism
        -- that changes γ₀ into γ₁ in general. For sphere eversion, one would choose this because
        -- rotation map is easy to choose as endomorphisms, because here it would simply become w ↦ -w.
        -- In our case another way needs to be done
        (∀ s : 𝕊¹, (G (1,s)).comp (mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ₀ s) = mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ₁ s) ∧
          (∀ x₀ : ℝ × 𝕊¹, Injective (G x₀))

-- Unused for now
-- Lemma to show that one can get turning number from lift.
lemma turning_from_lift {γ : 𝕊¹ → ℝ²} (γ_imm : LoopImmersion γ) :
  γ_imm.turningNumber =  γ_imm.lift 1 - γ_imm.lift 0 := by
    rw[← zero_add 1, eq_sub_iff_add_eq, add_comm]
    apply symm
    simpa using γ_imm.lift_add 0 1

end turning




section whitneygraustein

-- Straight line homotopy between loops is smooth.
theorem smooth_bs_wg {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁) :
  Smooth (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ²)
      fun p : ℝ × 𝕊¹ ↦ (1 - p.1) • (γ₀ p.2 : ℝ²) + p.1 • (γ₁ p.2 : ℝ²) := by
        refine (ContMDiff.smul ?_ ?_).add (contMDiff_fst.smul ?_)
        exact (contDiff_const.sub contDiff_id).contMDiff.comp contMDiff_fst
        exact γ₀_imm.cdiff.contMDiff.comp contMDiff_snd
        exact γ₁_imm.cdiff.contMDiff.comp contMDiff_snd

-- Construction of family of one jet sections.
-- Does so by taking the one jet extension of γ₀ and 'replacing' the linear map with the homotopy from equal turning number.
def formal_solution_aux2 {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber):
    FamilyOneJetSec (𝓡 1) 𝕊¹ 𝓘(ℝ, ℝ²)  ℝ² 𝓘(ℝ, ℝ) ℝ :=
      familyJoin (smooth_bs_wg γ₀_imm γ₁_imm) <|
        familyTwist (drop (oneJetExtSec ⟨γ₀, γ₀_imm.cdiff⟩))
          (fun p : ℝ × 𝕊¹ ↦ (eq_turn_hom γ₀_imm γ₁_imm turn_eq).choose p)
          ((eq_turn_hom γ₀_imm γ₁_imm turn_eq).choose_spec.left)

-- Proving that the construction made in `def:formal_solution_aux2` is a solution to the immersion relation.
def formal_solution_aux {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber):
    HtpyFormalSol 𝓡_imm :=
      {
        formal_solution_aux2 γ₀_imm γ₁_imm turn_eq with
        is_sol' := fun t x ↦ ((eq_turn_hom γ₀_imm γ₁_imm turn_eq).choose_spec.right.right.right (t,x)).comp (γ₀_imm.imm x)
      }

-- Reindexing the homotopy of formal solutions from `def:formal_solution_aux` by a smooth stepfunction.
def family_of_formal_sol {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber):
    HtpyFormalSol 𝓡_imm := (formal_solution_aux γ₀_imm γ₁_imm turn_eq).reindex
      ⟨smoothStep, contMDiff_iff_contDiff.mpr smoothStep.smooth⟩

-- simplification lemma that refactors the reindexed homotopy between loops in the formal solution to concrete function.
@[simp]
theorem formal_sol_bs {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber) (t : ℝ):
    (family_of_formal_sol γ₀_imm γ₁_imm turn_eq t).bs = fun x : 𝕊¹ ↦
      (1 - smoothStep t : ℝ) • (γ₀ x : ℝ²) + (smoothStep t : ℝ) • (γ₁ x : ℝ²) :=
    rfl

-- proof that the straight line homotopy is indeed a homotopy from `γ₀`
theorem formal_sol_zero {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber) (x : 𝕊¹):
    (family_of_formal_sol γ₀_imm γ₁_imm turn_eq).bs (0,x).1 (0,x).2 = γ₀ x := by simp

-- proof that the straight line homotopy is indeed a homotopy to `γ₁`
theorem formal_sol_one {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber) (x : 𝕊¹):
    (family_of_formal_sol γ₀_imm γ₁_imm turn_eq).bs (1,x).1 (1,x).2 = γ₁ x := by simp

-- proof that the formal solution is holonomic at zero, i.e. derivative of straight line homotopy at zero
-- is equivalent to composition of derivative of γ₀ and the homotopy at zero gotten from equal turning numbers.
theorem formal_sol_hol_at_zero {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber) {t : ℝ} (ht : t < 1 / 4) :
    (family_of_formal_sol γ₀_imm γ₁_imm turn_eq t).toOneJetSec.IsHolonomic := by
      intro x
      change
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) (fun y : 𝕊¹ ↦ ((1 : ℝ) - smoothStep t) • (γ₀ y : ℝ²) +
          smoothStep t • (γ₁ y : ℝ²)) x =
          ((eq_turn_hom γ₀_imm γ₁_imm turn_eq).choose (smoothStep t, x)).comp
            (mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) (fun y : 𝕊¹ ↦ (γ₀ y : ℝ²)) x)
      simp_rw [smoothStep.of_lt ht, (eq_turn_hom γ₀_imm γ₁_imm turn_eq).choose_spec.right.left,
               ContinuousLinearMap.id_comp]
      congr
      ext y
      simp [smoothStep.of_lt ht]

-- proof that the formal solution is holonomic at one, i.e. derivative of straight line homotopy at one
-- is equivalent to composition of derivative of γ₀ and the homotopy at one gotten from equal turning numbers.
theorem formal_sol_hol_at_one {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber) {t : ℝ} (ht : 3 / 4 < t) :
    (family_of_formal_sol γ₀_imm γ₁_imm turn_eq t).toOneJetSec.IsHolonomic := by
      intro x
      change
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) (fun y : 𝕊¹ ↦ ((1 : ℝ) - smoothStep t) • (γ₀ y : ℝ²) +
          smoothStep t • (γ₁ y : ℝ²)) x =
          ((eq_turn_hom γ₀_imm γ₁_imm turn_eq).choose (smoothStep t, x)).comp
            (mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) (fun y : 𝕊¹ ↦ (γ₀ y : ℝ²)) x)
      trans mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) (fun y : 𝕊¹ ↦ (γ₁ y : ℝ²)) x
      · congr 2
        ext y
        simp [smoothStep.of_gt ht]
      ext v
      erw [ContinuousLinearMap.coe_comp', Function.comp_apply, smoothStep.of_gt ht]
      rw [← (eq_turn_hom γ₀_imm γ₁_imm turn_eq).choose_spec.right.right.left x];
      rfl

-- Proof that the family of formal solutions is holonomic near C := {0,1} x 𝕊¹
-- Finds nbhds of C, because we used the smooth step function
-- Then finishes using `theorem:formal_sol_hol_at_zero` and `theorem:formal_sol_hol_at_one`
theorem family_of_formal_sol_hol_near_zero_one {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : γ₀_imm.turningNumber = γ₁_imm.turningNumber):
    ∀ᶠ s : ℝ × 𝕊¹ near {0, 1} ×ˢ univ, (family_of_formal_sol γ₀_imm γ₁_imm turn_eq s.1).toOneJetSec.IsHolonomicAt s.2 := by
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
      · exact formal_sol_hol_at_zero γ₀_imm γ₁_imm turn_eq ht x
      · exact formal_sol_hol_at_one γ₀_imm γ₁_imm turn_eq ht x


-- first implication whitney graustein
-- Assuming turning number is equal => ∃ homotopy
theorem whitney_graustein_left {f₀ f₁ : 𝕊¹ → ℝ²} (f₀_imm : LoopImmersion f₀) (f₁_imm : LoopImmersion f₁)
  (eq_turn : f₀_imm.turningNumber = f₁_imm.turningNumber) :
    ∃F : ℝ → 𝕊¹ → ℝ², RegularHomotopy F ∧ (F 0 = f₀) ∧ (F 1 = f₁) := by
      -- First step is to get H-principle result
      have ineq_rank : finrank ℝ (ℝ^1) < finrank ℝ  ℝ² := by simp
      let ε : 𝕊¹ → ℝ := fun _ ↦ 1
      have hε_pos : ∀ x, 0 < ε x := fun _ ↦ zero_lt_one
      have hε_cont : Continuous ε := continuous_const
      haveI : Nontrivial  ℝ² := by exact WithLp.instNontrivial 2 ((i : Fin 2) → (fun _ ↦ ℝ) i)
      haveI : FiniteDimensional ℝ  ℝ² := by exact WithLp.instModuleFinite 2 ℝ ((i : Fin 2) → (fun _ ↦ ℝ) i)
      haveI : Nonempty 𝕊¹ := (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
      haveI : IsCompact 𝕊¹ := isCompact_sphere (0 : ℝ²) 1
      haveI : SigmaCompactSpace 𝕊¹ := sigmaCompactSpace_of_locally_compact_second_countable
      rcases (immersionRel_satisfiesHPrincipleWith (𝓡 1) 𝕊¹ 𝓘(ℝ, ℝ²)  ℝ² 𝓘(ℝ, ℝ) ℝ
        ineq_rank ((Finite.isClosed (by simp : ({0, 1} : Set ℝ).Finite)).prod isClosed_univ) hε_pos hε_cont).bs
          (family_of_formal_sol f₀_imm f₁_imm eq_turn)
            (family_of_formal_sol_hol_near_zero_one f₀_imm f₁_imm eq_turn)
              with ⟨F, h₁, h₂, _, h₄⟩
      have := h₂.forall_mem principal_le_nhdsSet

      -- Remains to show that F is a Loophomotopy f₀ ~ f₁
      use F
      constructor
      refine { cdiff := h₁, imm := ?h.left.imm }
      intro t
      refine { cdiff := ?h.left.imm.cdiff, imm := ?h.left.imm.imm }
      exact Smooth.uncurry_left 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ^1) 𝓘(ℝ, ℝ²) h₁ t
      exact fun t_1 ↦ h₄ t t_1
      constructor
      ext x
      rw [this (0, x) (by simp)]
      simp_rw[formal_sol_zero f₀_imm f₁_imm eq_turn x]
      ext x
      rw [this (1, x) (by simp)]
      simp_rw[formal_sol_one f₀_imm f₁_imm eq_turn x]

-- second implication whitney graustein
-- Assuming ∃ homotopy => turning number eq
theorem whitney_graustein_right {f₀ f₁ : 𝕊¹ → ℝ²} (f₀_imm : LoopImmersion f₀) (f₁_imm : LoopImmersion f₁)
  (hom : ∃ F : ℝ → 𝕊¹ → ℝ², RegularHomotopy F ∧ (F 0 = f₀) ∧ (F 1 = f₁)) :
    f₀_imm.turningNumber = f₁_imm.turningNumber := by

      -- choose a working F and extract its properties
      let F := Classical.choose hom
      have loop_hom : RegularHomotopy F := by
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
theorem whitney_graustein {f₀ f₁ : 𝕊¹ → ℝ²} (f₀_imm : LoopImmersion f₀) (f₁_imm : LoopImmersion f₁) :
  (∃F : ℝ → 𝕊¹ → ℝ², RegularHomotopy F ∧ (F 0 = f₀) ∧ (F 1 = f₁)) ↔ (f₀_imm.turningNumber = f₁_imm.turningNumber) :=
    Iff.intro (whitney_graustein_right f₀_imm f₁_imm) (whitney_graustein_left f₀_imm f₁_imm)

end whitneygraustein
