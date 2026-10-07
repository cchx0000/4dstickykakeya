import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Finset.Image

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
noncomputable section
namespace NativeMergedPointOffsets
open Classical Finset

/-- One offset on each actual configured point, chosen from the fixed
pre-third source. No later retained subset participates in this definition. -/
def pointOffset {Omega Point V : Type*} [Zero V]
    (U : Finset Omega) (point : Omega → Point) (xi : Omega → V) (p : Point) : V :=
  if hp : p ∈ U.image point then xi ((mem_image.mp hp).choose) else 0

/-- Every occupied point uses an actual old-source offset at that same point. -/
theorem pointOffset_witness {Omega Point V : Type*} [Zero V]
    (U : Finset Omega) (point : Omega → Point) (xi : Omega → V)
    (p : Point) (hp : p ∈ U.image point) :
    ∃w ∈ U, point w = p ∧ pointOffset U point xi p = xi w := by
  refine ⟨(mem_image.mp hp).choose, (mem_image.mp hp).choose_spec.1,
    (mem_image.mp hp).choose_spec.2, ?_⟩
  exact dif_pos hp

/-- The fixed offset retains the original bounded-anchor estimate. -/
theorem pointOffset_norm_le {Omega Point V : Type*} [SeminormedAddCommGroup V]
    (U : Finset Omega) (point : Omega → Point) (xi : Omega → V)
    (C : ℝ) (hC : 0 ≤ C) (hxi : ∀w ∈ U, ‖xi w‖ ≤ C) (p : Point) :
    ‖pointOffset U point xi p‖ ≤ C := by
  by_cases hp : p ∈ U.image point
  · obtain ⟨w, hw, _, he⟩ := pointOffset_witness U point xi p hp
    rw [he]
    exact hxi w hw
  · simp only [pointOffset, dif_neg hp, norm_zero]
    exact hC

/-- Literal old-cell coherence supplies point coherence; merged points do
not need unique old preimages or any positive old fiber normalization. -/
theorem old_cell_coherence_to_pointOffset
    {Omega Point Cell V : Type*} [SeminormedAddCommGroup V]
    (U : Finset Omega) (point : Omega → Point) (oldCell : Omega → Cell)
    (xi : Omega → V) (osc : ℝ)
    (hread : ∀w ∈ U, ∀v ∈ U, point w = point v → oldCell w = oldCell v)
    (hcoh : ∀w ∈ U, ∀v ∈ U, oldCell w = oldCell v → ‖xi w - xi v‖ ≤ osc)
    (w : Omega) (hw : w ∈ U) :
    ‖xi w - pointOffset U point xi (point w)‖ ≤ osc := by
  obtain ⟨v, hv, he, hoff⟩ :=
    pointOffset_witness U point xi (point w) (mem_image_of_mem point hw)
  rw [hoff]
  exact hcoh w hw v hv (hread w hw v hv he.symm)

/-- Every later incidence restriction uses the same point offset. The
original residual, actual coarse-tube drift, and source-cell oscillation are
all charged, and none is divided by a retained fiber mass. -/
theorem residual_on_retained_source
    {Omega Point Cell V : Type*} [SeminormedAddCommGroup V]
    (U T : Finset Omega) (hTU : T ⊆ U)
    (point : Omega → Point) (oldCell : Omega → Cell)
    (xi oldValue coarseValue : Omega → V) (error drift osc : ℝ)
    (hread : ∀w ∈ U, ∀v ∈ U, point w = point v → oldCell w = oldCell v)
    (hcoh : ∀w ∈ U, ∀v ∈ U, oldCell w = oldCell v → ‖xi w - xi v‖ ≤ osc)
    (hres : ∀w ∈ U, ‖oldValue w - xi w‖ ≤ error)
    (hmove : ∀w ∈ T, ‖coarseValue w - oldValue w‖ ≤ drift)
    (w : Omega) (hw : w ∈ T) :
    ‖coarseValue w - pointOffset U point xi (point w)‖ ≤ error + drift + osc := by
  have hoff := old_cell_coherence_to_pointOffset U point oldCell xi osc hread hcoh w (hTU hw)
  have he : coarseValue w - pointOffset U point xi (point w) =
      (coarseValue w - oldValue w) + (oldValue w - xi w) +
        (xi w - pointOffset U point xi (point w)) := by abel
  rw [he]
  have hn := (norm_add_le ((coarseValue w - oldValue w) + (oldValue w - xi w))
    (xi w - pointOffset U point xi (point w))).trans
      (add_le_add (norm_add_le (coarseValue w - oldValue w) (oldValue w - xi w)) le_rfl)
  exact hn.trans (by linarith only [hmove w hw, hres w (hTU hw), hoff])

/-- At the real base deltaCfg=64 Delta, the merged-point loss is a fixed
267 analytic tube widths. Spatial contraction has not been applied to slopes. -/
theorem configured_direction_budget {Delta error drift osc : ℝ}
    (hDelta : 0 ≤ Delta) (he : error ≤ 64 * Delta)
    (hd : drift ≤ (3/32 : ℝ) * Delta) (ho : osc ≤ 2064 * Delta) :
    error + drift + osc ≤ 267 * (8 * Delta) := by
  linarith only [he, hd, ho, hDelta]

end NativeMergedPointOffsets
