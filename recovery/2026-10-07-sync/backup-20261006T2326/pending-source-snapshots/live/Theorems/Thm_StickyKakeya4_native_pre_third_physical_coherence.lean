import Theorems.Thm_StickyKakeya4_native_physical_local_offset_coherence
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_field

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
noncomputable section

namespace NativePreThirdPhysicalCoherence
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu NativeHeightMetricMenu
open NativeTranslatedGrainHeightOverlap NativeIncidentAffineAnchorGeometry NativeGrainQuotientInjection
open NativeReferenceXYGridLinear NativeHorizontalGrainSlice NativeReferenceXYGridField
open NativeTranslatedGrainHeightSelection NativeFinitePointCoherence NativePhysicalLocalOffsetCoherence
open NativeMatrixHeightWholePoint
open scoped BigOperators Matrix.Norms.Elementwise

/-- A real pre-third selection on the original native source. The translated
matrix field is chosen from the prescribed quotient/height source Sq ONCE.
Both matrix and offset choices act only on original point labels, preserve
every surviving incidence fiber, and retain the exact raw/translated field
readback. No third incidence refinement is performed in this theorem. -/
theorem select_same_field {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (S Sq : Finset (Fin n × Index)) (hS : S.Nonempty)
    (hp : ∀z∈S,parentLabel D a (2^m) z.1=p)
    (plane : Index → Submodule ℝ E4)
    (P0 : Submodule ℝ E4) (hP0 : P0≤ heightKernel) (ell : ℕ) (hell23 : ell=2 ∨ ell=3)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P0=ell-1)
    (hSource : S⊆second D a m ell plane Sq)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin (4-ell))) (error metric shift : ℝ)
    (he : 0 ≤ error) (hmetric : 0 ≤ metric)
    (M : Fin K → ℕ) (hM : ∀j,0 < M j)
    (hwindow : ∀j,meshWidth m/512 ≤ 64/(M j:ℝ))
    (hErrorWindow : ∀j,error ≤ 64/(M j:ℝ))
    (d upper : Fin K → ℝ) (hdpos : ∀j,0 < d j)
    (hF : ∀t,‖Fraw t‖ ≤ (1/4:ℝ))
    (Hmetric : ∀z∈S,∀u∈S,‖Fraw (rawHeight D m z.2)-Fraw (rawHeight D m u.2)‖ ≤
      metric*|chartHeightCoordinate m shift (rawHeight D m z.2)-
        chartHeightCoordinate m shift (rawHeight D m u.2)|)
    (hres : ∀z∈S,‖quotientMap P0 hP0 ell hell hell4 hd (Fraw (rawHeight D m z.2))
      (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error)
    (hlower : ∀j k,k∈S.image Prod.snd → d j ≤
      (((S.filter (fun z => z.2=k)).image (fun z => angularCell D (2^m) (M j) p z.1)).card:ℝ))
    (hupper : ∀j c,((angularMenu D a m (M j) p S c).card:ℝ) ≤ upper j) :
    let F := fixedField D a m ell plane Sq Fraw
    let R := modulus (2*metric)
    (∀t,‖F t‖ ≤ (1/4:ℝ)) ∧
    ∃B⊆S.image Prod.snd,let T := NativeFinitePointCoherence.lift S Prod.snd B
      T.Nonempty ∧ T⊆S ∧ T⊆second D a m ell plane Sq ∧
      S.card ≤ (R^(2*K)*(∏j,⌈((4:ℝ)^(4-ell)*upper j)/d j⌉₊))*T.card ∧
      (∀z∈T,F (translatedHeight D a m z.2)=Fraw (rawHeight D m z.2)) ∧
      (∀z∈T,‖quotientMap P0 hP0 ell hell hell4 hd (F (translatedHeight D a m z.2))
        (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error) ∧
      (∀j z u,z∈T → u∈T → physicalCell D a (2^m) (M j) p z.2=
          physicalCell D a (2^m) (M j) p u.2 →
        ‖F (translatedHeight D a m z.2)-F (translatedHeight D a m u.2)‖ < 64/(M j:ℝ) ∧
        ‖xi z.2-xi u.2‖ ≤ (129/4:ℝ)*(64/(M j:ℝ))) ∧
      (∀k∈B,T.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) ∧
      (∀z∈T,∀u∈S,u.2=z.2 → u∈T) ∧
      (∀j k,k∈B → d j ≤ (((T.filter (fun z => z.2=k)).image
        (fun z => angularCell D (2^m) (M j) p z.1)).card:ℝ)) ∧
      (∀j z u,z∈T → u∈T → physicalCell D a (2^m) (M j) p z.2 (3:Fin 4)=
          physicalCell D a (2^m) (M j) p u.2 (3:Fin 4) →
        ‖F (translatedHeight D a m z.2)-F (translatedHeight D a m u.2)‖ < 64/(M j:ℝ)) := by
  intro F R
  obtain ⟨B,hB,hT,hTS,hCost,hCoherent,hFiber,hLower,hHeight⟩ := select_actual_matrix_offset_menu D a m p S hS hp
    P0 hP0 ell hell23 hell hell4 hd Fraw xi error metric shift he hmetric M hM hwindow hErrorWindow
    d upper hdpos (fun k _ => hF (rawHeight D m k)) Hmetric hres hlower hupper
  have hRead (z : Fin n × Index) (hz : z∈NativeFinitePointCoherence.lift S Prod.snd B) :
      F (translatedHeight D a m z.2)=Fraw (rawHeight D m z.2) :=
    fixedField_readback D a m ell plane Sq Fraw z (hSource (hTS hz))
  refine ⟨fixedField_norm D a m ell plane Sq Fraw hF,B,hB,hT,hTS,hTS.trans hSource,hCost,hRead,?_,?_,hFiber,?_,hLower,?_⟩
  · intro z hz
    rw [hRead z hz]
    exact hres z (hTS hz)
  · intro j z u hz hu hcell
    rw [hRead z hz,hRead u hu]
    exact hCoherent j z u hz hu hcell
  · intro z hz u hu heq
    have hpB := (mem_filter.mp hz).2
    exact mem_filter.mpr ⟨hu,by simpa only [heq] using hpB⟩
  · intro j z u hz hu hheight
    rw [hRead z hz,hRead u hu]
    exact hHeight j z u hz hu hheight

end NativePreThirdPhysicalCoherence
