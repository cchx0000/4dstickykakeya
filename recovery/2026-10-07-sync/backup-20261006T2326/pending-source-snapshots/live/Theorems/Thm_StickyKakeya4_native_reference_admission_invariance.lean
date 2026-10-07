/- UNVERIFIED source draft. No strict Lean check has run on this file. -/
import Theorems.Thm_StickyKakeya4_native_configured_output_pairs
import Theorems.Thm_StickyKakeya4_native_full_coarse_shadow
import Theorems.Thm_StickyKakeya4_native_original_parent_density_core

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace NativeReferenceAdmissionInvariance
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeConfiguredIncidenceFibers
open NativeOriginalParentDensityCore

/-- The parent restriction removes no original cells of any label in
the full R-parent. This is equality of the literal cell families. -/
theorem sourceCells_parent_eq {n : ℕ} (D : FiniteScaleSource n)
    (R : Finset (Fin n)) (Eref : Finset (Fin n × Index))
    (a : ℝ) (N : ℕ) (p : Parent) :
    sourceCells D R (parentEdges D a N Eref p) a N p = sourceCells D R Eref a N p := by
  funext i
  have hi := (mem_parentLabels D R a N p _).mp
    (NativePaddedCellSource.originalLabel_mem (parentLabels D R a N p) i)
  change outputCells D (parentEdges D a N Eref p) a N p _=outputCells D Eref a N p _
  ext k
  rw [mem_outputCells,mem_outputCells]
  simp only [parentEdges,mem_filter,hi.2,and_true]

/-- The engine's parent-filtered presentation and the consumer's full-E1
presentation are the identical FiniteScaleSource, including the shading. -/
theorem source_parent_eq {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent) :
    source h R (parentEdges D a (2^m) Eref p) a m p=source h R Eref a m p := by
  unfold source
  rw [sourceCells_parent_eq]

/-- The representative depends on the source and reference labels; the
native accuracy proof enters only the proof of a valid fallback index. -/
theorem representative_eq {n : ℕ} {D : FiniteScaleSource n} {etaA etaB : ℝ}
    (hA : IsWangZakharovNativeFiniteInput D etaA)
    (hB : IsWangZakharovNativeFiniteInput D etaB)
    (R : Finset (Fin n)) (a : ℝ) (N : ℕ) (p : Parent) :
    NativeCoarseDirectionThinning.representative hA R a N p =
      NativeCoarseDirectionThinning.representative hB R a N p := by
  rfl

/-- Re-admitting the SAME source does not alter any fullSource field,
including its literal representative lines and its original cell shading. -/
theorem fullSource_eq {n : ℕ} {D : FiniteScaleSource n} {etaA etaB : ℝ}
    (hA : IsWangZakharovNativeFiniteInput D etaA)
    (hB : IsWangZakharovNativeFiniteInput D etaB)
    (R : Finset (Fin n)) (a : ℝ) (level b : ℕ) (E : Finset (Fin n × Index)) :
    NativeFullCoarseShadow.fullSource hA R a level b E =
      NativeFullCoarseShadow.fullSource hB R a level b E := by
  rfl

/-- Both admission proofs below have exactly source(h,R,Eref,a,m,p) as
their datum. Eref is unchanged, rather than replaced by a new shading. -/
theorem outputTube_eq {n : ℕ} {D : FiniteScaleSource n} {eta etaA etaB : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (a : ℝ) (m b : ℕ) (p : Parent)
    (hA : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaA)
    (hB : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaB) (i : Fin n) :
    outputTube h R Eref a m b p hA i=outputTube h R Eref a m b p hB i := by
  rfl

/-- The deduplicated configured fine graph is literally unchanged by
the prescribed-accuracy admission proof, even before taking its cardinal. -/
theorem fine_graph_eq {n : ℕ} {D : FiniteScaleSource n} {eta etaA etaB : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (m b : ℕ) (p : Parent)
    (hA : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaA)
    (hB : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaB)
    (configured : Index → E4) :
    T.image (fun z => (configured z.2,outputTube h R Eref a m b p hA z.1)) =
      T.image (fun z => (configured z.2,outputTube h R Eref a m b p hB z.1)) := by
  rfl

end NativeReferenceAdmissionInvariance
