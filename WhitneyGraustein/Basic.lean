import SphereEversion.Global.Immersion

noncomputable section

open InnerProductSpace Metric FiniteDimensional Set Function LinearMap Filter ContinuousLinearMap Complex NormedSpace
open scoped Manifold Topology

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
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
notation "𝕊¹" => Metric.sphere (0 : ℝ²) 1
local notation "𝓡_imm" => immersionRel (𝓡 1) 𝕊¹ 𝓘(ℝ, ℝ²)  ℝ²


section Tloops

structure TLoop (γ : 𝕊¹ → ℝ²) : Prop where
  cont : Continuous γ
  around_zero : ∀x : 𝕊¹, γ x ≠ 0

structure THomotopy (Γ : ℝ → 𝕊¹ → ℝ²) : Prop where
  cont : Continuous ↿Γ
  loop : ∀ t : ℝ, TLoop (Γ t)

end Tloops


section axioms

/- Winding number axioms -/
axiom TLoop.windingNumber {γ : 𝕊¹ → ℝ²} (γ_tloop : TLoop γ) : ℤ

axiom THomotopy.cont_windingNumber {Γ : ℝ → 𝕊¹ → ℝ²} (Γ_thom : THomotopy Γ) :
  Continuous (fun t ↦ (Γ_thom.loop t).windingNumber)

axiom eq_wind_conthom {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_tloop : TLoop γ₀) (γ₁_tloop : TLoop γ₁)
  (wind_eq : γ₀_tloop.windingNumber = γ₁_tloop.windingNumber) :
  ∃G : ℝ × 𝕊¹ → ℝ² →L[ℝ] ℝ²,
    (∀ (x₀ : ℝ × 𝕊¹), ContinuousAt G x₀) ∧
      (∀ s : 𝕊¹, G (0,s) = ContinuousLinearMap.id ℝ ℝ²) ∧
        -- TODO
        -- Not what it needs to be right now
        -- not derivatives, but instead just γ₀ and γ₁
        (∀ s : 𝕊¹, (G (1,s)).comp (mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ₀ s) = mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ₁ s) ∧
          (∀ x₀ : ℝ × 𝕊¹, Injective (G x₀))

/- Smoothing Principle -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M][ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N]

axiom smoothing_principle {f : M → N} (cont : Continuous f) {A : Set M} (A_clos : IsClosed A)
  (A_smooth : ∀ x : A, SmoothAt I J f x):
    ∃g : ℝ → M → N, (g 0 = f) ∧ (Smooth I J (g 1)) ∧
      (∀t : ℝ, ∀x : A, g t x = f x)


end axioms


section Mloops

structure MLoop (γ : 𝕊¹ → ℝ²) : Prop where
  smooth : Smooth (𝓡 1) 𝓘(ℝ, ℝ²) γ
  around_zero : ∀x : 𝕊¹, γ x ≠ 0

structure MHomotopy (Γ : ℝ → 𝕊¹ → ℝ²) : Prop where
  smooth : Smooth (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ²) ↿Γ
  loop : ∀ t : ℝ, MLoop (Γ t)

lemma mloop_to_tloop {γ : 𝕊¹ → ℝ²} (γ_mloop : MLoop γ) : TLoop γ := by refine
  { cont := γ_mloop.smooth.continuous, around_zero := γ_mloop.around_zero }

lemma mhom_to_thom {Γ : ℝ → 𝕊¹ → ℝ²} (Γ_mhom : MHomotopy Γ) : THomotopy Γ := by refine
  { cont := Γ_mhom.smooth.continuous, loop := fun t ↦ mloop_to_tloop (Γ_mhom.loop t) }

end Mloops


section smooth

/- smoothed version of winding number axioms -/
def MLoop.windingNumber {γ : 𝕊¹ → ℝ²} (γ_mloop : MLoop γ) : ℤ :=
  (mloop_to_tloop γ_mloop).windingNumber

lemma MHomotopy.cont_windingNumber {Γ : ℝ → 𝕊¹ → ℝ²} (Γ_mhom : MHomotopy Γ) :
  Continuous (fun t ↦ (Γ_mhom.loop t).windingNumber) :=
    (mhom_to_thom Γ_mhom).cont_windingNumber



lemma eq_wind_smoothhom {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_mloop : MLoop γ₀) (γ₁_mloop : MLoop γ₁)
  (wind_eq : γ₀_mloop.windingNumber = γ₁_mloop.windingNumber) :
  ∃G : ℝ × 𝕊¹ → ℝ² →L[ℝ] ℝ²,
    (∀ (x₀ : ℝ × 𝕊¹), SmoothAt (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ² →L[ℝ] ℝ²) G x₀) ∧
      (∀ s : 𝕊¹, G (0,s) = ContinuousLinearMap.id ℝ ℝ²) ∧
        (∀ s : 𝕊¹, (G (1,s)).comp (mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ₀ s) = mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ₁ s) ∧
          (∀ x₀ : ℝ × 𝕊¹, Injective (G x₀)) := by
            let h := eq_wind_conthom (mloop_to_tloop γ₀_mloop) (mloop_to_tloop γ₁_mloop) wind_eq
            let G := Classical.choose h
            let G_prop := Classical.choose_spec h
            let A : Set (ℝ × 𝕊¹) := ({0, 1} : Set ℝ) ×ˢ (univ : Set 𝕊¹)
            have A_closed : IsClosed A := (Finite.isClosed (by simp : ({0, 1} : Set ℝ).Finite)).prod isClosed_univ
            have G_smoothat_A : ∀ x : A, SmoothAt (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ² →L[ℝ] ℝ²) G x := by sorry
            -- let h1 := smoothing_principle /- ℝ × 𝕊¹ is manifold and ℝ² →L[ℝ] ℝ² too ... -/
            --   (continuous_iff_continuousAt.mpr G_prop.left) A_closed G_smoothat_A
            sorry


end smooth


section loopimmersion

structure LoopImmersion (γ : 𝕊¹ → ℝ²) : Prop where
  smooth : Smooth (𝓡 1) 𝓘(ℝ, ℝ²) γ
  imm :  ∀ t : 𝕊¹, Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ t)

structure RegularHomotopy (Γ : ℝ → 𝕊¹ → ℝ²) : Prop where
  smooth : Smooth (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ²) ↿Γ
  imm : ∀ t : ℝ, LoopImmersion (Γ t)

end loopimmersion


section lemmas

axiom inj_def {γ : 𝕊¹ → ℝ²} (loop_imm : LoopImmersion γ) :
  (∀ t : 𝕊¹, Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ t)) ↔ (∀ t : 𝕊¹, mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ t ≠ 0)

def to_circle (x : ℝ²) (hx : x ≠ 0) : 𝕊¹ := ⟨‖x‖⁻¹ • x, by
  simp only [mem_sphere_iff_norm, sub_zero]; rw [@norm_smul]; rw [@norm_inv]; rw [@norm_norm]; simp [hx]⟩

/- The unit section of the tangent bundle of the circle -/
def unitSection : 𝕊¹ → TangentBundle (𝓡 1) (𝕊¹) := (⟨·, fun _ ↦ 1⟩)

axiom smooth_unit : Smooth (𝓡 1) ((𝓡 1).prod (𝓡 1)) unitSection

lemma deriv_to_mloop {γ : 𝕊¹ → ℝ²} (loop_imm : LoopImmersion γ):
  MLoop (fun x : 𝕊¹ ↦ mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) γ x (unitSection x).snd) := by
    refine
    {
      smooth := sorry,
      around_zero := sorry
    }

end lemmas








-- Goal is to make these lemmas to only have to resort to topology before the proof
-- as would normally be done when using h-principle
section turning

/-
To do the Whitney Graustein theorem fully, one needs the proper definition for
turning number of a loop. This invokes the definition of a winding number and
thus needs covering space theory. In particular, we want to be able to count
the windings of a loop around a point, for which we would need the homotopy lifting
property.

To solve this, we assume for now that this exists and build on top of the assumptions.
In particular we will assume the following regarding turning number:
-/

/- Definition of the turning number -/
def turningNumber {γ : 𝕊¹ → ℝ²} (loop_imm : LoopImmersion γ) := (deriv_to_mloop loop_imm).windingNumber

lemma LoopHomotopy.cont_turningNumber {Γ : ℝ → 𝕊¹ → ℝ²} (Γ_hom : RegularHomotopy Γ) :
  Continuous (fun t ↦ turningNumber (Γ_hom.imm t)) := by
    refine THomotopy.cont_windingNumber ?Γ_thom
    refine
    {
      cont := sorry,
      loop := fun t : ℝ ↦ mloop_to_tloop <| deriv_to_mloop (Γ_hom.imm t)
    }

lemma eq_turn_hom {f₀ f₁ : 𝕊¹ → ℝ²} (f₀_imm : LoopImmersion f₀) (f₁_imm : LoopImmersion f₁)
  (turn_eq : turningNumber f₀_imm = turningNumber f₁_imm) :
  ∃G : ℝ × 𝕊¹ → ℝ² →L[ℝ] ℝ²,
    (∀ (x₀ : ℝ × 𝕊¹), SmoothAt (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ² →L[ℝ] ℝ²) G x₀) ∧
      (∀ s : 𝕊¹, G (0,s) = ContinuousLinearMap.id ℝ ℝ²) ∧
        (∀ s : 𝕊¹, (G (1,s)).comp (mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) f₀ s) = mfderiv (𝓡 1) 𝓘(ℝ, ℝ²) f₁ s) ∧
          (∀ x₀ : ℝ × 𝕊¹, Injective (G x₀)) :=
            sorry --eq_wind_smoothhom (deriv_to_mloop f₀_imm) (deriv_to_mloop f₁_imm) turn_eq

end turning




section whitneygraustein

-- Straight line homotopy between loops is smooth.
theorem smooth_bs_wg {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁) :
  Smooth (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ²)
      fun p : ℝ × 𝕊¹ ↦ (1 - p.1) • (γ₀ p.2 : ℝ²) + p.1 • (γ₁ p.2 : ℝ²) := by
        refine (ContMDiff.smul ?_ ?_).add (contMDiff_fst.smul ?_)
        exact (contDiff_const.sub contDiff_id).contMDiff.comp contMDiff_fst
        exact γ₀_imm.smooth.contMDiff.comp contMDiff_snd
        exact γ₁_imm.smooth.contMDiff.comp contMDiff_snd

-- Construction of family of one jet sections.
-- Does so by taking the one jet extension of γ₀ and 'replacing' the linear map with the homotopy from equal turning number.
def formal_solution_aux2 {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : turningNumber γ₀_imm = turningNumber γ₁_imm):
    FamilyOneJetSec (𝓡 1) 𝕊¹ 𝓘(ℝ, ℝ²)  ℝ² 𝓘(ℝ, ℝ) ℝ :=
      familyJoin (smooth_bs_wg γ₀_imm γ₁_imm) <|
        familyTwist (drop (oneJetExtSec ⟨γ₀, γ₀_imm.smooth⟩))
          (fun p : ℝ × 𝕊¹ ↦ (eq_turn_hom γ₀_imm γ₁_imm turn_eq).choose p)
          ((eq_turn_hom γ₀_imm γ₁_imm turn_eq).choose_spec.left)

-- Proving that the construction made in `def:formal_solution_aux2` is a solution to the immersion relation.
def formal_solution_aux {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : turningNumber γ₀_imm = turningNumber γ₁_imm):
    HtpyFormalSol 𝓡_imm :=
      {
        formal_solution_aux2 γ₀_imm γ₁_imm turn_eq with
        is_sol' := fun t x ↦ ((eq_turn_hom γ₀_imm γ₁_imm turn_eq).choose_spec.right.right.right (t,x)).comp (γ₀_imm.imm x)
      }

-- Reindexing the homotopy of formal solutions from `def:formal_solution_aux` by a smooth stepfunction.
def family_of_formal_sol {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : turningNumber γ₀_imm = turningNumber γ₁_imm):
    HtpyFormalSol 𝓡_imm := (formal_solution_aux γ₀_imm γ₁_imm turn_eq).reindex
      ⟨smoothStep, contMDiff_iff_contDiff.mpr smoothStep.smooth⟩

-- simplification lemma that refactors the reindexed homotopy between loops in the formal solution to concrete function.
@[simp]
theorem formal_sol_bs {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : turningNumber γ₀_imm = turningNumber γ₁_imm) (t : ℝ):
    (family_of_formal_sol γ₀_imm γ₁_imm turn_eq t).bs = fun x : 𝕊¹ ↦
      (1 - smoothStep t : ℝ) • (γ₀ x : ℝ²) + (smoothStep t : ℝ) • (γ₁ x : ℝ²) :=
    rfl

-- proof that the straight line homotopy is indeed a homotopy from `γ₀`
theorem formal_sol_zero {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : turningNumber γ₀_imm = turningNumber γ₁_imm) (x : 𝕊¹):
    (family_of_formal_sol γ₀_imm γ₁_imm turn_eq).bs (0,x).1 (0,x).2 = γ₀ x := by simp

-- proof that the straight line homotopy is indeed a homotopy to `γ₁`
theorem formal_sol_one {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : turningNumber γ₀_imm = turningNumber γ₁_imm) (x : 𝕊¹):
    (family_of_formal_sol γ₀_imm γ₁_imm turn_eq).bs (1,x).1 (1,x).2 = γ₁ x := by simp

-- proof that the formal solution is holonomic at zero, i.e. derivative of straight line homotopy at zero
-- is equivalent to composition of derivative of γ₀ and the homotopy at zero gotten from equal turning numbers.
theorem formal_sol_hol_at_zero {γ₀ γ₁ : 𝕊¹ → ℝ²} (γ₀_imm : LoopImmersion γ₀) (γ₁_imm : LoopImmersion γ₁)
  (turn_eq : turningNumber γ₀_imm = turningNumber γ₁_imm) {t : ℝ} (ht : t < 1 / 4) :
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
  (turn_eq : turningNumber γ₀_imm = turningNumber γ₁_imm) {t : ℝ} (ht : 3 / 4 < t) :
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
  (turn_eq : turningNumber γ₀_imm = turningNumber γ₁_imm):
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
  (eq_turn : turningNumber f₀_imm = turningNumber f₁_imm) :
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
      refine { smooth := h₁, imm := ?h.left.imm }
      intro t
      refine { smooth := ?h.left.imm.cdiff, imm := ?h.left.imm.imm }
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
    turningNumber f₀_imm = turningNumber f₁_imm := by

      -- choose a working F and extract its properties
      let F := Classical.choose hom
      have loop_hom : RegularHomotopy F := by
        exact (Classical.choose_spec hom).left
      have F₀ : F 0 = f₀ := by
        exact (Classical.choose_spec hom).right.left
      have F₁ : F 1 = f₁ := by
        exact (Classical.choose_spec hom).right.right

      -- Construct the function ℝ → ℤ that determines turning number per time frame
      let G := fun t ↦ turningNumber (loop_hom.imm t)
      have G₀ : G 0 = turningNumber f₀_imm := by
        simp_rw[G, F₀]
      have G₁ : G 1 = turningNumber f₁_imm := by
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
  (∃F : ℝ → 𝕊¹ → ℝ², RegularHomotopy F ∧ (F 0 = f₀) ∧ (F 1 = f₁)) ↔ (turningNumber f₀_imm = turningNumber f₁_imm) :=
    Iff.intro (whitney_graustein_right f₀_imm f₁_imm) (whitney_graustein_left f₀_imm f₁_imm)

end whitneygraustein
