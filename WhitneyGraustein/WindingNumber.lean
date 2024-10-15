-- import Mathlib
import SphereEversion.Global.Immersion

noncomputable section

open InnerProductSpace Metric FiniteDimensional Set Function LinearMap Filter ContinuousLinearMap Complex NormedSpace
open scoped Manifold Topology

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


section naturalprojection

-- The natural projection `ℝ → 𝕊¹`
def nat_proj : ℝ → 𝕊¹ :=
  fun x ↦ ⟨![Real.cos (2 * Real.pi * x), Real.sin (2 * Real.pi * x)],
    by simp [EuclideanSpace.norm_eq]⟩

axiom nat_proj_surj : Function.Surjective nat_proj
axiom nat_proj_eq (x y : ℝ) (nat_proj_eq : nat_proj x = nat_proj y) : ∃!n : ℤ, x - y = n

end naturalprojection


section path

structure CirclePath (f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹) : Prop where
  cont : Continuous f

structure CirclePathHomotopy {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (path_f : CirclePath f)
  {g : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (path_g : CirclePath g) (eq_start : f 0 = g 0) (eq_end : f 1 = g 1)
    (F : (Set.Icc (0 : ℝ) (1 : ℝ)) × (Set.Icc (0 : ℝ) (1 : ℝ)) → 𝕊¹) : Prop where
      cont : Continuous F
      startpoint : ∀ s : Set.Icc (0 : ℝ) (1 : ℝ), F (0, s) = f 0
      endpoint : ∀ s : Set.Icc (0 : ℝ) (1 : ℝ), F (1, s) = f 1

end path



section pathlift

-- Structure of a lift of a path in 𝕊¹
structure CirclePathLift {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (_ : CirclePath f)
  (F : Set.Icc (0 : ℝ) (1 : ℝ) → ℝ) : Prop where
    cont : Continuous F
    lift : ∀ t : Set.Icc (0 : ℝ) (1 : ℝ), nat_proj (F t) = f t

-- Structure of a lift of a circle path homotopy
structure CirclePathHomotopyLift {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (path_f : CirclePath f)
  {g : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (path_g : CirclePath g) (eq_start : f 0 = g 0) (eq_end : f 1 = g 1)
    {H : (Set.Icc (0 : ℝ) (1 : ℝ)) × (Set.Icc (0 : ℝ) (1 : ℝ)) → 𝕊¹} (H_hom : CirclePathHomotopy path_f path_g eq_start eq_end H)
      (F : (Set.Icc (0 : ℝ) (1 : ℝ)) × (Set.Icc (0 : ℝ) (1 : ℝ)) → ℝ) : Prop where
        cont : Continuous F
        startpoint : ∀ s : Set.Icc (0 : ℝ) (1 : ℝ), nat_proj (F (0, s)) = f 0
        endpoint : ∀ s : Set.Icc (0 : ℝ) (1 : ℝ), nat_proj (F (1, s)) = f 1
        lift : ∀ x : (Set.Icc (0 : ℝ) (1 : ℝ)) × (Set.Icc (0 : ℝ) (1 : ℝ)), nat_proj (F x) = H x

-- Set of startpoints
def path_startpoints {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (_ : CirclePath f) :=  {x | nat_proj x = f 0}

-- Existence lift of map
axiom existence_lift_of_path {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (path_f : CirclePath f) :
  ∀a ∈ path_startpoints path_f,
    ∃!F : Set.Icc (0 : ℝ) (1 : ℝ) → ℝ, CirclePathLift path_f F

-- Existence of startpoint for lift of path
lemma existence_startpoint_pathlift {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (path_f : CirclePath f) :
  ∃a : ℝ, a ∈ path_startpoints path_f := by
    apply nat_proj_surj

-- Given a homotopy between circlepaths, it can be lifted
axiom circlepath_homotopy_lifting_property {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (path_f : CirclePath f)
  {g : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (path_g : CirclePath g) (eq_start : f 0 = g 0) (eq_end : f 1 = g 1)
    {H : (Set.Icc (0 : ℝ) (1 : ℝ)) × (Set.Icc (0 : ℝ) (1 : ℝ)) → 𝕊¹} (H_hom : CirclePathHomotopy path_f path_g eq_start eq_end H)
      {F : Set.Icc (0 : ℝ) (1 : ℝ) → ℝ} (F_lift : CirclePathLift path_f F) :
        ∃ F' : (Set.Icc (0 : ℝ) (1 : ℝ)) × (Set.Icc (0 : ℝ) (1 : ℝ)) → ℝ, CirclePathHomotopyLift path_f path_g eq_start eq_end H_hom F'

end pathlift



section loop

structure CircleLoop (f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹) : Prop where
  circlepath : CirclePath f
  per : f 0 = f 1

structure CircleLoopHomotopy {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (path_f : CircleLoop f)
  {g : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (path_g : CircleLoop g) (eq_start_end : f 0 = g 0)
    (F : (Set.Icc (0 : ℝ) (1 : ℝ)) × (Set.Icc (0 : ℝ) (1 : ℝ)) → 𝕊¹) : Prop where
      circlepathhomotopy : CirclePathHomotopy path_f.circlepath path_g.circlepath eq_start_end
        (by rw[path_f.per,path_g.per] at eq_start_end
            exact eq_start_end) F

end loop



section looplift

structure CircleLoopLift {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (loop_f : CircleLoop f)
  (F : Set.Icc (0 : ℝ) (1 : ℝ) → ℝ) : Prop where
    pathlift : CirclePathLift loop_f.circlepath F

structure CircleLoopHomotopyLift {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (loop_f : CircleLoop f)
  {g : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (loop_g : CircleLoop g) (eq_start_end : f 0 = g 0)
    {H : (Set.Icc (0 : ℝ) (1 : ℝ)) × (Set.Icc (0 : ℝ) (1 : ℝ)) → 𝕊¹} (H_hom : CircleLoopHomotopy loop_f loop_g eq_start_end H)
      (F : (Set.Icc (0 : ℝ) (1 : ℝ)) × (Set.Icc (0 : ℝ) (1 : ℝ)) → ℝ) : Prop where
        pathhomlift : CirclePathHomotopyLift loop_f.circlepath loop_g.circlepath eq_start_end
          (by rw[loop_f.per,loop_g.per] at eq_start_end
              exact eq_start_end) H_hom.circlepathhomotopy F

-- Set of startpoints
def loop_startpoints {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (_ : CircleLoop f) :=  {x | nat_proj x = f 0}

-- Existence lift of map
axiom existence_lift_of_loop {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (loop_f : CircleLoop f) :
  ∀a ∈ loop_startpoints loop_f,
    ∃!F : Set.Icc (0 : ℝ) (1 : ℝ) → ℝ, CircleLoopLift loop_f F

-- Existence of startpoint for lift of loop
lemma existence_startpoint_looplift {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (loop_f : CircleLoop f) :
  ∃a : ℝ, a ∈ loop_startpoints loop_f := by
    apply nat_proj_surj

-- Given a homotopy between circleloops, it can be lifted
axiom circleloop_homotopy_lifting_property {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (loop_f : CircleLoop f)
  {g : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (loop_g : CircleLoop g) (eq_start_end : f 0 = g 0)
    {H : (Set.Icc (0 : ℝ) (1 : ℝ)) × (Set.Icc (0 : ℝ) (1 : ℝ)) → 𝕊¹} (H_hom : CircleLoopHomotopy loop_f loop_g eq_start_end H)
      {F : Set.Icc (0 : ℝ) (1 : ℝ) → ℝ} (F_lift : CircleLoopLift loop_f F) :
        ∃ F' : (Set.Icc (0 : ℝ) (1 : ℝ)) × (Set.Icc (0 : ℝ) (1 : ℝ)) → ℝ, CircleLoopHomotopyLift loop_f loop_g eq_start_end H_hom F'

end looplift



section winding

-- Definition of the winding number
def winding_number {f : Set.Icc (0 : ℝ) (1 : ℝ) → 𝕊¹} (loop_f : CircleLoop f) : ℤ :=
  let a  := (existence_startpoint_looplift loop_f).choose
  let ha := (existence_startpoint_looplift loop_f).choose_spec.out
  let F := (existence_lift_of_loop loop_f a ha).choose
  let hF := (existence_lift_of_loop loop_f a ha).choose_spec.left
  let eq_start_end := loop_f.per
  let h₀ := hF.pathlift.lift 0
  let h₁ := hF.pathlift.lift 1
  have nat_proj_eq_F₀_F₁ : nat_proj (F 0) = nat_proj (F 1) := by
    rw[h₀, h₁]
    exact eq_start_end
  (nat_proj_eq (F 0) (F 1) nat_proj_eq_F₀_F₁).choose

end winding



section smoothing

structure SmoothCirclePath (f : ℝ → 𝕊¹) : Prop where
  smooth : Smooth 𝓘(ℝ, ℝ) (𝓡 1) f

structure SmoothCirclePathHomotopy {f : ℝ → 𝕊¹} (path_f : SmoothCirclePath f)
  {g : ℝ → 𝕊¹} (path_g : SmoothCirclePath g) (eq_start : f 0 = g 0) (eq_end : f 1 = g 1)
    (F : ℝ × ℝ → 𝕊¹) : Prop where
      smooth : Smooth (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) (𝓡 1) F
      startpoint : ∀ s : ℝ, F (0, s) = f 0
      endpoint : ∀ s : ℝ, F (1, s) = f 1

-- Structure of a lift of a path in 𝕊¹
structure SmoothCirclePathLift {f : ℝ → 𝕊¹} (_ : SmoothCirclePath f)
  (F : ℝ → ℝ) : Prop where
    smooth : Smooth 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) F
    lift : ∀ t : ℝ, nat_proj (F t) = f t

-- Structure of a lift of a circle path homotopy
structure SmoothCirclePathHomotopyLift {f : ℝ → 𝕊¹} (path_f : SmoothCirclePath f)
  {g : ℝ → 𝕊¹} (path_g : SmoothCirclePath g) (eq_start : f 0 = g 0) (eq_end : f 1 = g 1)
    {H : ℝ × ℝ → 𝕊¹} (H_hom : SmoothCirclePathHomotopy path_f path_g eq_start eq_end H)
      (F : ℝ × ℝ → ℝ) : Prop where
        smooth : Smooth (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) F
        startpoint : ∀ s : ℝ, nat_proj (F (0, s)) = f 0
        endpoint : ∀ s : ℝ, nat_proj (F (1, s)) = f 1
        lift : ∀ x : ℝ × ℝ, nat_proj (F x) = H x

-- Set of startpoints
def smoothpath_startpoints {f : ℝ → 𝕊¹} (_ : SmoothCirclePath f) :=  {x | nat_proj x = f 0}

-- Existence lift of map
axiom existence_lift_of_smooth_path {f : ℝ → 𝕊¹} (path_f : SmoothCirclePath f) :
  ∀a ∈ smoothpath_startpoints path_f,
    ∃!F : ℝ → ℝ, SmoothCirclePathLift path_f F

-- Existence of startpoint for lift of path
lemma existence_startpoint_smoothpathlift {f : ℝ → 𝕊¹} (path_f : SmoothCirclePath f) :
  ∃a : ℝ, a ∈ smoothpath_startpoints path_f := by
    apply nat_proj_surj

-- Given a homotopy between circlepaths, it can be lifted
axiom smoothcirclepath_homotopy_lifting_property {f : ℝ → 𝕊¹} (path_f : SmoothCirclePath f)
  {g : ℝ → 𝕊¹} (path_g : SmoothCirclePath g) (eq_start : f 0 = g 0) (eq_end : f 1 = g 1)
    {H : ℝ × ℝ → 𝕊¹} (H_hom : SmoothCirclePathHomotopy path_f path_g eq_start eq_end H)
      {F : ℝ → ℝ} (F_lift : SmoothCirclePathLift path_f F) :
        ∃ F' : ℝ × ℝ → ℝ, SmoothCirclePathHomotopyLift path_f path_g eq_start eq_end H_hom F'

structure SmoothCircleLoop (f : ℝ → 𝕊¹) : Prop where
  smoothcirclepath : SmoothCirclePath f
  per : f 0 = f 1

structure SmoothCircleLoopHomotopy {f : ℝ → 𝕊¹} (path_f : SmoothCircleLoop f)
  {g : ℝ → 𝕊¹} (path_g : SmoothCircleLoop g) (eq_start_end : f 0 = g 0)
    (F : ℝ × ℝ → 𝕊¹) : Prop where
      smoothcirclepathhomotopy : SmoothCirclePathHomotopy path_f.smoothcirclepath path_g.smoothcirclepath eq_start_end
        (by rw[path_f.per,path_g.per] at eq_start_end
            exact eq_start_end) F

structure SmoothCircleLoopLift {f : ℝ → 𝕊¹} (loop_f : SmoothCircleLoop f)
  (F : ℝ → ℝ) : Prop where
    smoothpathlift : SmoothCirclePathLift loop_f.smoothcirclepath F

structure SmoothCircleLoopHomotopyLift {f : ℝ → 𝕊¹} (loop_f : SmoothCircleLoop f)
  {g : ℝ → 𝕊¹} (loop_g : SmoothCircleLoop g) (eq_start_end : f 0 = g 0)
    {H : ℝ × ℝ → 𝕊¹} (H_hom : SmoothCircleLoopHomotopy loop_f loop_g eq_start_end H)
      (F : ℝ × ℝ → ℝ) : Prop where
        smoothpathhomlift : SmoothCirclePathHomotopyLift loop_f.smoothcirclepath loop_g.smoothcirclepath eq_start_end
          (by rw[loop_f.per,loop_g.per] at eq_start_end
              exact eq_start_end) H_hom.smoothcirclepathhomotopy F

-- Set of startpoints
def smoothloop_startpoints {f : ℝ → 𝕊¹} (_ : SmoothCircleLoop f) :=  {x | nat_proj x = f 0}

-- Existence lift of map
axiom existence_lift_of_smoothloop {f : ℝ → 𝕊¹} (loop_f : SmoothCircleLoop f) :
  ∀a ∈ smoothloop_startpoints loop_f,
    ∃!F : ℝ → ℝ, SmoothCircleLoopLift loop_f F

-- Existence of startpoint for lift of loop
lemma existence_startpoint_smoothlooplift {f : ℝ → 𝕊¹} (loop_f : SmoothCircleLoop f) :
  ∃a : ℝ, a ∈ smoothloop_startpoints loop_f := by
    apply nat_proj_surj

-- Given a homotopy between circleloops, it can be lifted
axiom smoothcircleloop_homotopy_lifting_property {f : ℝ → 𝕊¹} (loop_f : SmoothCircleLoop f)
  {g : ℝ → 𝕊¹} (loop_g : SmoothCircleLoop g) (eq_start_end : f 0 = g 0)
    {H : ℝ × ℝ → 𝕊¹} (H_hom : SmoothCircleLoopHomotopy loop_f loop_g eq_start_end H)
      {F : ℝ → ℝ} (F_lift : SmoothCircleLoopLift loop_f F) :
        ∃ F' : ℝ × ℝ → ℝ, SmoothCircleLoopHomotopyLift loop_f loop_g eq_start_end H_hom F'

-- Definition of the winding number
def smooth_winding_number {f : ℝ → 𝕊¹} (loop_f : SmoothCircleLoop f) : ℤ :=
  let a  := (existence_startpoint_smoothlooplift loop_f).choose
  let ha := (existence_startpoint_smoothlooplift loop_f).choose_spec.out
  let F := (existence_lift_of_smoothloop loop_f a ha).choose
  let hF := (existence_lift_of_smoothloop loop_f a ha).choose_spec.left
  let eq_start_end := loop_f.per
  let h₀ := hF.smoothpathlift.lift 0
  let h₁ := hF.smoothpathlift.lift 1
  have nat_proj_eq_F₀_F₁ : nat_proj (F 0) = nat_proj (F 1) := by
    rw[h₀, h₁]
    exact eq_start_end
  (nat_proj_eq (F 0) (F 1) nat_proj_eq_F₀_F₁).choose

end smoothing
