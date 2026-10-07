import Theorems.Thm_StickyKakeya4_native_retained_slice_core
import Theorems.Thm_StickyKakeya4_native_slice_count_comparison

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeRetainedSliceActual
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeSquaredGrainQueries
open NativeAnisotropicSliceLabels NativeSliceCountComparison NativeRetainedSliceCore SelfUniform

/-- A cleaned incidence subset of the fixed reference parent receives a
new actual slice core. The three spatial classes coarsen and height stays
fixed, exactly as in the already constructed reference profiles. -/
theorem exists_actual_retained_slice_counts {n d K : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (p : Parent) (E H : Finset (Fin n × Index))
    (hH : H⊆parentEdges D a (2^m) E p) (hHn : H.Nonempty)
    (depths : Fin K → ℕ) (hdepths : ∀j,depths j ≤ phaseDepth m) (Qref : ℕ)
    (HRef : HasUniformFibers (parentEdges D a (2^m) E p) Qref
      (fun z => slicePoint D a m p z.2))
    (lambda G : ℝ) (hlambda : 0 ≤ lambda) (hG : 0 ≤ G)
    (hret : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ G*H.card)
    (lower : Fin K → ℝ)
    (hRatio : ∀j,lower j*(points D a m (depths j) E p).card ≤
      (points D a m (phaseDepth m) E p).card)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀j x,Rel j x x) (hsym : ∀j x y,Rel j x y → Rel j y x)
    (L : ℕ) (hL : 0 < L) :
    let Q := NativeSourceSizeBounds.radix H.card L
    let point := fun z : Fin n × Index => slicePoint D a m p z.2
    ∃T⊆H,T.Nonempty ∧ H.card ≤ refinementCost d K L*T.card ∧
      (∀j x y,x∈T → y∈T → degree (fun _ : Fin n × Index => 1) (Rel j) T x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (Rel j) T y) ∧
      HasUniformFibers T Q point ∧
      (∀j,HasUniformFibers T Q (fun z => sliceClass m (depths j) (point z))) ∧
      lambda*(points D a m (phaseDepth m) E p).card ≤
        G*(refinementCost d K L:ℝ)*(Qref:ℝ)^2*(T.image point).card ∧
      ∀j t,t∈(T.image point).image (sliceClass m (depths j)) →
        lambda*lower j ≤ G*(refinementCost d K L:ℝ)*(Qref:ℝ)^2*(Q:ℝ)^4*
          ((T.image point).filter (fun z => sliceClass m (depths j) z=t)).card ∧
        ((T.image point).filter (fun z => sliceClass m (depths j) z=t)).card ≤
          ((points D a m (phaseDepth m) E p).filter
            (fun z => sliceClass m (depths j) z=t)).card := by
  intro Q point
  have hRatio' : ∀j,lower j*
      (((parentEdges D a (2^m) E p).image point).image (sliceClass m (depths j))).card ≤
      ((parentEdges D a (2^m) E p).image point).card := by
    intro j
    change lower j*((points D a m (phaseDepth m) E p).image
      (horizontalCoarsen (phaseDepth m) (depths j))).card ≤ (points D a m (phaseDepth m) E p).card
    rw [points_coarsen D a m (phaseDepth m) (depths j) (hdepths j) E p]
    exact hRatio j
  exact exists_retained_slice_counts (parentEdges D a (2^m) E p) H hH hHn point
    (fun j => sliceClass m (depths j)) Qref HRef lambda G hlambda hG hret lower hRatio'
    Rel hrefl hsym L hL

end NativeRetainedSliceActual
