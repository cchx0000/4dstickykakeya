/- UNVERIFIED actual original-reference scope readback. No strict check has run. -/
import Theorems.Thm_StickyKakeya4_native_generic_reference_data
import Theorems.Thm_StickyKakeya4_native_middle_grain_parent_budget
import Theorems.Thm_StickyKakeya4_native_same_reference_chart_bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeFinalSourceScopeReadback
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeGenericReferenceData
open NativeLocalParentSource NativeMiddleGrainParentBudget NativeSquaredGrainQueries
open NativeReferenceXYGridPoints NativeSameReferenceChartBounds

/-- Both original-label fields needed by sparse admission come from the
actual first IsCore. The enlarged first dimension is never changed. -/
theorem original_scope {n L g : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau}
    (ref : Reference h tau htau seed e zeta L g) :
    ref.E1⊆incidences ref.original ∧ ∀z∈ref.E1,z.1∈ref.R := by
  refine ⟨ref.core.1.trans (filter_subset _ _),?_⟩
  intro z hz
  exact (mem_filter.mp (ref.core.1 hz)).2

/-- All final incidences are in the literal SAME original parent, including
membership in the unchanged R, rather than just equality of phase labels. -/
theorem parent_scope {n L g : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau}
    (ref : Reference h tau htau seed e zeta L g)
    (m : ℕ) (p : Parent) (T : Finset (Fin n × Index))
    (hT : T⊆ref.E1) (hp : ∀z∈T,parentLabel D ref.a (2^m) z.1=p) :
    ∀z∈T,z.1∈parentLabels D ref.R ref.a (2^m) p := by
  intro z hz
  exact (mem_parentLabels D ref.R ref.a (2^m) p z.1).mpr
    ⟨(original_scope ref).2 z (hT hz),hp z hz⟩

/-- The final nonempty T activates the already installed E1-parent native
supplier. No source is reselected and no nonemptiness certificate is added. -/
theorem active_reference_parent {n L g : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau}
    (ref : Reference h tau htau seed e zeta L g)
    (m : ℕ) (p : Parent) (T : Finset (Fin n × Index))
    (hT : T⊆ref.E1) (hTn : T.Nonempty)
    (hp : ∀z∈T,parentLabel D ref.a (2^m) z.1=p) :
    (parentEdges D ref.a (2^m) ref.E1 p).Nonempty := by
  obtain ⟨z,hz⟩ := hTn
  exact ⟨z,mem_filter.mpr ⟨hT hz,hp z hz⟩⟩

/-- The actual stopping cap and scale identity give the original fine-depth
and initial square guards used by the SAME final-third and parent readers. -/
theorem middle_guards (stop level : ℕ) (delta r : ℝ)
    (hs : 6 ≤ stop) (hcap : stop ≤ level/4) (hd : 0 < delta)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 64*delta ≤ r^2)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1) :
    let m := middleDepth stop
    phaseDepth m ≤ level ∧ delta ≤ (rho m)^2 ∧
      3072*r ≤ (rho m)^2 ∧ (rho m)^2 ≤ 6144*r := by
  intro m
  obtain ⟨_hm6,_hms,_hlo,hfine⟩ := middle_depth_bounds stop hs
  obtain ⟨_hRho,_hRho1,_hSquare,hRlo,hRhi⟩ := middle_scale_bounds stop hs r hidentity
  have hFine : phaseDepth m ≤ level := hfine.trans (by omega)
  have hrSquare : r^2 ≤ r := by nlinarith only [hr,hr1]
  refine ⟨hFine,?_,hRlo,hRhi⟩
  nlinarith only [hd,hsmall,hrSquare,hRlo,hr]

end NativeFinalSourceScopeReadback
