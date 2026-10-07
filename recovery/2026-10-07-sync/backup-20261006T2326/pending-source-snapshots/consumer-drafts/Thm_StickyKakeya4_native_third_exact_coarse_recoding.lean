/- UNVERIFIED draft, 2026-10-06. Waiting for the fresh prerequisite closure. SAME third source; one quotient only. -/
import Theorems.Thm_StickyKakeya4_exact_height_no_deletion_recoding
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeThirdExactCoarseRecoding
open Classical Finset StickyKakeya4 CanonicalGridRecoding WeightedCanonicalRecoding
open ExactHeightNoDeletionRecoding NativeThirdXYSourceData NativeThirdXYData
open NativeActualQuotientDensity NativeQuotientFiberReadback NativeQuotientLatticeTransport
open NativeReferenceXYGridField NativeReferenceXYGridMaps NativeReferenceXYGridPoints NativeReferenceXYGridSupport
open NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightFibers NativeGrainQuotientFibers
open NativeHorizontalGrainSlice NativeHeightSlopeCoordinates NativeOriginalParentSelection NativeSpatialAngularGeometry
open NativeCommonCubicalMesh NativeSquaredGrainQueries GridQuotientAD
open scoped BigOperators Matrix.Norms.Elementwise

/-- The restored centers use the exact same midpoint convention. -/
theorem center_readback {d : ℕ} (mu : ℝ) (u : CanonicalGridRecoding.Grid d) :
    CanonicalGridRecoding.center mu u=NativeQuotientGridCenters.center mu u := rfl

/-- Existing product-fiber counts are precisely the canonical distinct
fine-X counts on the same original-point fibers. -/
theorem fineXCells_eq_product_fiber_card {E P : Type*} [DecidableEq P]
    {k l : ℕ} (I : Finset E) (point : E → P) (f : P → CanonicalGridRecoding.Label ℤ k l)
    (b : ℤ × CanonicalGridRecoding.Grid l) :
    (fineXCells I point (fun p => (f p).1) (fun p => (f p).2.1) (fun p => (f p).2.2) b).card=
      (GridQuotientAD.fiber (productSlice (I.image (fun e => f (point e))) b.1) b.2).card := by
  rcases b with ⟨height,y⟩
  rw [product_fiber_card]
  simp only [fineXCells,oldPoints,Finset.filter_image,Finset.image_image,Function.comp_def,Prod.mk.injEq]

/-- The population exported by reference_cross_dense, with its actual CX. -/
def finePopulation (m ell : ℕ) (CX : ℝ) : ℝ :=
  (1/((32:ℝ)^(ell-1)*CX))*(halfWidth m:ℝ)^(ell-1)

/-- Same-T source reader. Its lower population is proved from the stored
referenceX field via reference_cross_dense. Exact height freezing is a
pre-third field identity on S, not a new population/AD certificate.
No lower/higher simultaneous quotient assertion is made. -/
theorem from_third_source {n d J ell : ℕ} (D : FiniteScaleSource n)
    (zeta a : ℝ) (m : ℕ) (hm : 6≤m) (plane : Index → Submodule ℝ E4)
    (E Hgraph S T : Finset (Fin n × Index)) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1≤ell) (hell4 : ell≤4) (hd : Module.finrank ℝ P=ell-1)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (p : Parent) (population profileLower profileUpper : ℝ) (Qref : ℕ)
    (lambda G Cpre t : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (CX : ℝ)
    (Hdata : HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP hell hell4 hd Fraw p
      population profileLower profileUpper Qref lambda G Cpre t L3 Rel CX) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell plane Hgraph P hP hell hell4 hd
      (physicalMesh m (phaseDepth m)/8)
    let Fold := fixedField D a m ell plane Sq Fraw
    S⊆second D a m ell plane Sq →
    (∀x∈second D a m ell plane Sq,Fraw (rawHeight D m x.2)=
      nodeSlope P hP ell hell hell4 hd (sliceSpace (plane (spatialLabel D (2^m) x.2)))
        (slice_horizontal (plane (spatialLabel D (2^m) x.2)))) →
    (∀x∈Hgraph,parentLabel D a (2^m) x.1=p) →
    ∀R : ℕ,0 < R → ∀coarseHeight : ℤ → ℤ,
    ∀Fcfg : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ,
    (∀x∈S,Fold (translatedHeight D a m x.2)=Fcfg (coarseHeight (translatedHeight D a m x.2))) →
    let xy := pxy D a m ell p P hP hell hell4 hd Fold
    let W := T.image (fun x => xy x.2)
    let recode := fun x : Fin n × Index => actualLabel (mu m) R coarseHeight Fold Fcfg (xy x.2)
    (∀x∈T,recode x=coarsenLabel R coarseHeight (xy x.2)) ∧
    (taggedEdges T recode).card=T.card ∧
    (taggedEdges T recode).image Prod.fst=T ∧
    (∀k,((taggedEdges T recode).filter (fun z => z.1.2=k)).image Prod.fst=T.filter (fun z => z.2=k)) ∧
    (∀b∈W.image oldIndex,oldY (mu m) R coarseHeight b∈W.image (newY (mu m) R coarseHeight Fold Fcfg)) ∧
    (∀q∈W.image (newY (mu m) R coarseHeight Fold Fcfg),∃b∈W.image oldIndex,
      q=oldY (mu m) R coarseHeight b ∧
      (∀u∈FiniteCoarseYThresholdSelection.oldFiber W oldIndex b,newY (mu m) R coarseHeight Fold Fcfg u=q) ∧
      finePopulation m ell CX/((R:ℝ)^(ell-1))≤
        (((W.filter (fun u => newY (mu m) R coarseHeight Fold Fcfg u=q)).image (newX (mu m) R)).card:ℝ)) := by
  intro Sq Fold hpre Hread hparent R hR coarseHeight Fcfg hExact xy W recode
  have hTS : T⊆S := Hdata.1.1
  have hTn : T.Nonempty := Hdata.1.2.1
  have hTH : T⊆Hgraph := Hdata.1.2.2.2.1
  have hTpre : T⊆second D a m ell plane Sq := hTS.trans hpre
  have hpT : ∀x∈T,parentLabel D a (2^m) x.1=p := fun x hx => hparent x (hTH hx)
  have HX : ∀x∈T,(rho m)^(-((ell:ℝ)-1))≤CX*
      (referenceX D a m ell plane T P hP hell hell4 hd (mu m)
        (referenceKey D a m ell plane P hP hell hell4 hd (mu m) x)).card := by
    simpa only [mu_phase m hm] using Hdata.2.2.1
  have hNative := reference_cross_dense D a m ell (by omega) p plane Sq T hTpre hTn hpT
    P hP hell hell4 hd Fraw Hread CX HX
  have hExactT : ∀k∈T.image Prod.snd,Fold (xy k).1=Fcfg (coarseHeight (xy k).1) := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hk
    exact hExact x (hTS hx)
  have hDense : ∀b∈(T.image ((pointLabel (fun k => (xy k).1) (fun k => (xy k).2.1)
      (fun k => (xy k).2.2))∘Prod.snd)).image oldIndex,
      finePopulation m ell CX≤((fineXCells T Prod.snd (fun k => (xy k).1)
        (fun k => (xy k).2.1) (fun k => (xy k).2.2) b).card:ℝ) := by
    intro b hb
    have hbW : b∈W.image oldIndex := hb
    obtain ⟨u,hu,hub⟩ := mem_image.mp hbW
    have hheight : u.1=b.1 := congrArg (fun b : ℤ × CanonicalGridRecoding.Grid (4-ell) => b.1) hub
    have hy : u.2.2=b.2 := congrArg (fun b : ℤ × CanonicalGridRecoding.Grid (4-ell) => b.2) hub
    have hmem : b.2∈(productSlice W b.1).image Prod.snd :=
      mem_image.mpr ⟨u.2,mem_image.mpr ⟨u,mem_filter.mpr ⟨hu,hheight⟩,rfl⟩,hy⟩
    rw [fineXCells_eq_product_fiber_card]
    exact hNative.2 b.1 b.2 hmem
  have hh := actual_no_deletion_recoding T Prod.snd (fun k => (xy k).1)
    (fun k => (xy k).2.1) (fun k => (xy k).2.2) (mu m) R (mu_pos m) hR
    coarseHeight Fold Fcfg hExactT (finePopulation m ell CX) hDense
  exact hh

end NativeThirdExactCoarseRecoding
