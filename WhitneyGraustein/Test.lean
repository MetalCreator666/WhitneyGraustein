import Mathlib

noncomputable section

notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
notation "𝕊¹" => Metric.sphere (0 : ℝ²) 1

def to_circle (x : ℝ²) (hx : x ≠ 0) : 𝕊¹ := ⟨‖x‖⁻¹ • x, by
  simp only [mem_sphere_iff_norm, sub_zero]; rw [@norm_smul]; rw [@norm_inv]; rw [@norm_norm]; simp [hx]⟩
