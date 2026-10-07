import Theorems.Thm_StickyKakeya4_native_same_Q_source_restriction

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeSameQShadowMass
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeRelativeCoarseReadback NativeCubicalIncidenceCounts
open NativeCoarseShadingCapacity NativeCoarseShadingPruning NativeCoarseDyadicShading
open NativeSameQSourceRestriction
open scoped BigOperators ENNReal

/-- Exact cubical shading mass on a specified Q, using its original TQ
antecedents. Fine configured-pair weights remain a separate quantity. -/
theorem sum_shadow_weight_eq_pairs {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (level m b : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hT : ∀ z ∈ T, z.1 ∈ parentLabels D R a (2 ^ m) p)
    (hQ : (parentLabels D R a (2 ^ m) p).Nonempty)
    (hdy : D.thickness = (2 : ℝ)⁻¹ ^ level) (hm : m ≤ level)
    (hb : b ≤ level - m + 6) (Q : Finset Parent) :
    (∑ q ∈ Q, weight (source h R Eref a m p) 0 (level - m + 6) b
      (NativeCoarseDirectionThinning.representative hS univ 0 (2 ^ b))
      (incidences (sourceCells D R T a (2 ^ m) p)) q) =
        (((restrict D a m b p Q T).image (doublePair h R a m p hQ (2 ^ b))).card : ℝ) *
          (32 / ((2 ^ b : ℕ) : ℝ)) ^ 4 := by
  let S := source h R Eref a m p
  let TQ := restrict D a m b p Q T
  let IT := incidences (sourceCells D R TQ a (2 ^ m) p)
  let B := block (level - m + 6) b
  let rep := NativeCoarseDirectionThinning.representative hS univ 0 (2 ^ b)
  have hmesh : (B : ℝ) * S.thickness / 128 = 32 / ((2 ^ b : ℕ) : ℝ) :=
    block_mesh (local_source_dyadic h R Eref a level m p hdy hm) hb
  have hparents : ∀ z ∈ IT, parentLabel S 0 (2 ^ b) z.1 ∈ Q := by
    intro z hz
    rw [show IT = (incidences (sourceCells D R T a (2 ^ m) p)).filter
        (fun w => parentLabel S 0 (2 ^ b) w.1 ∈ Q) from
      source_incidences_restrict h R Eref T a m b p Q] at hz
    exact (mem_filter.mp hz).2
  have hread := NativeCurrentReferenceReadback.selected_relative_incidence_image
    h R Eref TQ a m p hQ (2 ^ b) B
    (fun z hz => hT z (mem_filter.mp hz).1) hS hmesh
  calc
    _ = ∑ q ∈ Q, (volume (wzCellShading ((B : ℝ) * S.thickness / 128)
        (fun _ : Fin 1 => rows S 0 (2 ^ b) B rep IT q) 0)).toReal := by
      apply sum_congr rfl
      intro q hq
      rw [hmesh]
      unfold weight
      rw [source_rows_restrict h R Eref T a m b B p Q rep q hq]
    _ = ((coarse S 0 (2 ^ b) B rep IT).card : ℝ) *
        ((B : ℝ) * S.thickness / 128) ^ 4 :=
      coarse_shading_real hS.1.2.1 0 (2 ^ b) B (block_pos _ _) rep IT Q hparents
    _ = _ := by rw [hread, hmesh]

end NativeSameQShadowMass
