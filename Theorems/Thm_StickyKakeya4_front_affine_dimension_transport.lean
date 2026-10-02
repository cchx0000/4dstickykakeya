import Theorems.Thm_StickyKakeya4_residual_affine_rescaling

/-!
The actual fixed affine normalization preserves Hausdorff dimension. Thus a
dimension deficit on the original front persists on every individually
normalized front. No assertion about a weak limit of moving normalizations
is made.
-/

open Set

namespace StickyKakeya4.ResidualAffineRescaling

theorem affine_E4_lipschitz (e : E4 ≃ᵃ[ℝ] E4) :
    ∃ K : NNReal, LipschitzWith K (e : E4 → E4) := by
  let f : E4 →ᴬ[ℝ] E4 := ⟨e.toAffineMap, e.continuous_of_finiteDimensional⟩
  refine ⟨‖f.contLinear‖₊, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖f x - f y‖ ≤ ‖f.contLinear‖ * ‖x - y‖
  have heq : f.contLinear (x - y) = f x - f y :=
    f.contLinear_map_vsub x y
  rw [← heq]
  exact f.contLinear.le_opNorm (x - y)

theorem affine_E4_dimH_image (e : E4 ≃ᵃ[ℝ] E4) (S : Set E4) :
    dimH (e '' S) = dimH S := by
  obtain ⟨K, hK⟩ := affine_E4_lipschitz e
  obtain ⟨K', hK'⟩ := affine_E4_lipschitz e.symm
  apply le_antisymm (hK.dimH_image_le S)
  have hinv : e.symm '' (e '' S) = S := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, hzx⟩
      rw [e.symm_apply_apply] at hzx
      exact hzx ▸ hz
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  simpa only [hinv] using hK'.dimH_image_le (e '' S)

theorem normalized_front_dimH_eq (ambient : Set MarkedLine) (a₀ b₀ : E3)
    (τ : ℝ) (hτ : τ ≠ 0) :
    dimH (frontAffineEquiv4 a₀ b₀ τ hτ '' unitFront ambient) =
      dimH (unitFront ambient) :=
  affine_E4_dimH_image _ _

theorem normalized_front_dimH_lt_four (ambient : Set MarkedLine) (a₀ b₀ : E3)
    (τ : ℝ) (hτ : τ ≠ 0) (hdim : dimH (unitFront ambient) < 4) :
    dimH (frontAffineEquiv4 a₀ b₀ τ hτ '' unitFront ambient) < 4 := by
  rwa [normalized_front_dimH_eq]

end StickyKakeya4.ResidualAffineRescaling
