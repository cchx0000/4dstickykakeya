import Theorems.Thm_StickyKakeya4_original_macro_direction_source
import Theorems.Thm_StickyKakeya4_original_terminal_scalar_collision_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace OriginalMacroPrintedW
open Classical Finset OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open OriginalMacroDirectionCells OriginalTerminalScalarCollisionGeometry
variable {P T H : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq H]
/-- The new collision labels give the literal original W conditions,
 including the FULL Euclidean terminal-direction restriction. All path
 incidences and shared original point/height labels are read back unchanged. -/
theorem original_full_witness_conditions (I : Finset (P × T)) (height : P → H)
    (u : T → ℝ) (v : T → ℝ × ℝ) {q : ℝ} (hq : 0 < q)
    {w : TwoTubePathCollisionCount.Path P T × TwoTubePathCollisionCount.Path P T}
    (hw : w ∈ witnesses I height (directionCell (q/8) u v)) :
    w.1 ∈ TwoTubePathCollisionCount.paths I ∧ w.2 ∈ TwoTubePathCollisionCount.paths I ∧
      w.2.point₀=w.1.point₀ ∧ height w.2.point₁=height w.1.point₁ ∧
      height w.2.point₂=height w.1.point₂ ∧
      dist (EuclideanAlignmentPatches.euclidean (directionVector u v w.2.tube₂))
        (EuclideanAlignmentPatches.euclidean (directionVector u v w.1.tube₂)) ≤ q := by
  obtain ⟨ha,hb,hp,hz1,hz2,hcell⟩ := witness_conditions I height (directionCell (q/8) u v) hw
  exact ⟨ha,hb,hp,hz1,hz2,full_direction_collision u v hq _ _ hcell⟩
/-- The actual full-direction fiber is contained in its original scalar
 fiber, so the already derived scalar angular population cap is retained. -/
theorem original_full_terminal_fiber_cap (I : Finset (P × T)) (u : T → ℝ) (v : T → ℝ × ℝ)
    {q radius U : ℝ} (hq : 0 < q) (hqr : q/8 ≤ radius)
    (hball : ∀ p a, (((tubesAt I p).filter (fun t => |u t-a| ≤ radius)).card:ℝ) ≤ U) :
    ∀ p k, (((tubesAt I p).filter (fun t => directionCell (q/8) u v t=k)).card:ℝ) ≤ U := by
  intro p k
  have hsub : (tubesAt I p).filter (fun t => directionCell (q/8) u v t=k) ⊆
      (tubesAt I p).filter (fun t => OriginalScalarCollisionMass.scalarTerminalCell (q/8) u t=k.1) := by
    intro t ht
    obtain ⟨ht,hc⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨ht,congrArg Prod.fst hc⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans
    (scalar_terminal_fiber_cap I u (by positivity : 0 < q/8) hqr hball p k.1)
end OriginalMacroPrintedW
