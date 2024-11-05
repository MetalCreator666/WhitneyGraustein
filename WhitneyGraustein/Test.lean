import Mathlib

open scoped Manifold Topology

noncomputable section

notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)
notation "𝕊¹" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

/- The unit section of the tangent bundle of the circle -/
def unitSection : 𝕊¹ → TangentBundle (𝓡 1) (𝕊¹) := (⟨·, fun _ ↦ 1⟩)

abbrev core := tangentBundleCore (𝓡 1) (𝕊¹)


lemma smooth_coordtransform (x : 𝕊¹) :
  SmoothAt 𝓘(ℝ, ℝ¹) 𝓘(ℝ, ℝ¹ →L[ℝ] ℝ¹)
    (fun (s : 𝕊¹) ↦ core.coordChange (core.indexAt s) (core.indexAt x) s) x := by

      #check ContMDiffAt.congr_of_eventuallyEq
      #check tangentBundleCore_indexAt
      #check ContMDiffAt.contMDiffWithinAt
      #check contMDiffAt_iff_source_of_mem_source

      -- Given two trivializations, the change of coordinates function is smooth
      -- It needs constant trivializations, so since our function above has changing trivializations
      -- for changing values of s, we need to pick a nbhd of x on which we can simply
      let tangent_smooth := (core.smoothVectorBundle (𝓡 1)).smoothOn_coordChangeL


      sorry










/- unitSection is Smooth section -/
lemma smooth_unit : Smooth (𝓡 1) ((𝓡 1).prod (𝓡 1)) unitSection := by
  -- Take arbitrary point `x` and trivialization at `x`
  intro x
  let e' := (trivializationAt (ℝ¹) (TangentSpace (𝓡 1)) x)
  -- Show `unitSection x` is in the source of the trivialization
  have h1 : unitSection x ∈ e'.source := by
    refine (Trivialization.mem_source (trivializationAt (ℝ¹) (TangentSpace (𝓡 1)) x)).mpr ?_
    exact FiberBundle.mem_baseSet_trivializationAt' (unitSection x).proj
  haveI : MemTrivializationAtlas e' := by
    exact instMemTrivializationAtlasTrivializationAt x
  -- join of two smooth maps `id` and `const`
  have h : SmoothAt (𝓡 1) (𝓡 1) (fun s ↦ (e' (unitSection s)).1) x ∧
    SmoothAt (𝓡 1) (𝓡 1) ((fun s ↦ (e' (unitSection s)).2)) x := by
      constructor
      · -- `id` is smooth
        exact smooth_id x
      · -- `fun s ↦ (e' (unitSection s)).2` is smooth
        refine ContMDiffAt.clm_apply ?right.hg ?right.hf
        · -- `coordtransform` is smooth
          exact smooth_coordtransform x
        · -- `const` is smooth
          exact smooth_const x
  -- Finish proof using `h1` and `h`
  refine (Trivialization.contMDiffAt_iff (𝓡 1) h1).mpr ?_
  constructor
  · exact h.left
  · exact h.right























theorem unitSection_triv (e : Trivialization ℝ¹ Bundle.TotalSpace.proj) [e.IsLinear ℝ] {x : 𝕊¹}
    (hx : x ∈ e.baseSet) : e (unitSection x) = (x, (fun _ ↦ 1)) := by
  simp_rw [unitSection]
  refine Prod.ext ?_ ?_
  · exact Trivialization.coe_coe_fst e hx
  · rw[e.apply_eq_prod_continuousLinearEquivAt ℝ x hx (fun _ ↦ 1)]
    have hyp : (Trivialization.continuousLinearEquivAt ℝ e x hx) (fun _ ↦ 1) = fun _ ↦ 1 := by
      sorry
    exact hyp





/- Smooth coordchange -/
lemma coordchange_smooth2 (x : 𝕊¹) :
  SmoothAt 𝓘(ℝ, ℝ¹) 𝓘(ℝ, ℝ¹ →L[ℝ] ℝ¹)
    (fun (s : 𝕊¹) ↦
      (tangentBundleCore (𝓡 1) (𝕊¹)).coordChange
        ((tangentBundleCore (𝓡 1) (𝕊¹)).indexAt s)
        ((tangentBundleCore (𝓡 1) (𝕊¹)).indexAt x) s)
    x := by
      let core := tangentBundleCore (𝓡 1) (𝕊¹)
      let function := fun s ↦ core.coordChange (core.indexAt s) (core.indexAt x) s
      let tangent_smooth := (core.smoothVectorBundle (𝓡 1)).smoothOn_coordChangeL

      #check tangentBundleCore_indexAt
      -- #check refine (Z.smoothOn_coordChange IB i i').congr fun b hb ↦ ?_
      -- look at instance smoothvectorbundle

      let chart_x := achart ℝ¹ x
      have h : ∀s : chart_x.1.source, core.coordChange
        (core.indexAt s) (core.indexAt x) s =
          ↑(Trivialization.coordChangeL ℝ
            (core.localTriv (core.indexAt s)) (core.localTriv (core.indexAt x)) s) := by
        intro s
        sorry
      haveI : MemTrivializationAtlas (core.localTriv chart_x) := by
        sorry
      -- stuck again.... Later moment....



      -- let core := tangentBundleCore (𝓡 1) (𝕊¹)
      -- let function := fun s ↦ core.coordChange (core.indexAt s) (core.indexAt x) s
      -- refine smoothWithinAt_univ.mp ?_
      -- -- let c := TangentBundle.chartAt (𝓡 1) (𝕊¹) (unitSection x)
      -- let c := achart (ℝ¹) x
      -- let c_base := c.1.source
      -- have x_mem_c_base : x ∈ c_base := by exact ChartedSpace.mem_chart_source x
      -- have h : ∀s : c_base, ((tangentBundleCore (𝓡 1) (𝕊¹)).indexAt s) = c := by
      --   intro s
      --   sorry
      -- haveI : MemTrivializationAtlas (core.localTriv c) := by
      --   sorry
      -- let smoothness := (core.smoothVectorBundle (𝓡 1)).smoothOn_coordChangeL
      --   (core.localTriv c) (core.localTriv c)
      -- have c_base_nbhd_x : c_base ∈ 𝓝[Set.univ] x := by
      --   refine mem_nhdsWithin_of_mem_nhds ?h
      --   refine IsOpen.mem_nhds ?h.hs x_mem_c_base
      --   exact (c.1).open_source
      -- refine (contMDiffWithinAt_inter' c_base_nbhd_x).mp ?right.hg.a
      -- rw[Set.univ_inter]
      -- rw[Set.inter_self] at smoothness
      -- have smoothness_2 : SmoothOn 𝓘(ℝ, ℝ¹) 𝓘(ℝ, ℝ¹ →L[ℝ] ℝ¹) (fun b ↦ core.coordChange c c b) c_base := by
      --   sorry



      sorry





/- unitSection is Smooth section -/
lemma smooth_unit2 : Smooth (𝓡 1) ((𝓡 1).prod (𝓡 1)) unitSection := by
  -- Take arbitrary point `x` and trivialization at `x`
  intro x
  let e' := (trivializationAt (ℝ¹) (TangentSpace (𝓡 1)) x)
  -- Show `unitSection x` is in the source of the trivialization
  have h1 : unitSection x ∈ e'.source := by
    refine (Trivialization.mem_source (trivializationAt (ℝ¹) (TangentSpace (𝓡 1)) x)).mpr ?_
    exact FiberBundle.mem_baseSet_trivializationAt' (unitSection x).proj
  haveI : MemTrivializationAtlas e' := by
    exact instMemTrivializationAtlasTrivializationAt x
  -- join of two smooth maps `id` and `const`
  have h : SmoothAt (𝓡 1) (𝓡 1) (fun s ↦ (e' (unitSection s)).1) x ∧
    SmoothAt (𝓡 1) (𝓡 1) ((fun s ↦ (e' (unitSection s)).2)) x := by
      constructor
      · -- `id` is smooth
        exact smooth_id x
      · refine ContMDiffAt.clm_apply ?right.hg ?right.hf
        · -- `coordchange` is smooth
          apply coordchange_smooth2
        · -- `const` is smooth
          exact smoothAt_const
  -- Finish proof using `h1` and `h`
  refine (Trivialization.contMDiffAt_iff (𝓡 1) h1).mpr ?_
  constructor
  · exact h.left
  · exact h.right


















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
