import Theorems.Thm_StickyKakeya4_native_padded_source_mass
import Theorems.Thm_StickyKakeya4_native_unit_parent_volume
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativePaddedSourceTransport
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalPaddedCells NativeContractedUnitParent NativeUnitParentNormalization
open NativePaddedCellSource NativePaddedSourceMass
open scoped ENNReal BigOperators

lemma card_filter_originalLabel {n : ℕ} (R : Finset (Fin n)) (P : Fin n → Prop) [DecidablePred P] :
    ((univ : Finset (Fin R.card)).filter (fun i => P (originalLabel R i))).card=(R.filter P).card := by
  simpa only [Finset.card_filter] using sum_originalLabel (M:=ℕ) R (fun i => if P i then 1 else 0)

lemma source_carrierBallCount {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (a : ℝ) (p : Parent) (hp : ∀i∈R,parentLabel D a 1 i=p)
    (i : Fin R.card) (r : ℝ) :
    wzCarrierBallCount (source h original R a p hp) i r=
      (R.filter (fun j => dist
        (direction (NativeContractedUnitParent.line D a p j),offset (NativeContractedUnitParent.line D a p j))
        (direction (NativeContractedUnitParent.line D a p (originalLabel R i)),
          offset (NativeContractedUnitParent.line D a p (originalLabel R i))) ≤ r)).card := by
  exact card_filter_originalLabel R (fun j => dist
    (direction (NativeContractedUnitParent.line D a p j),offset (NativeContractedUnitParent.line D a p j))
    (direction (NativeContractedUnitParent.line D a p (originalLabel R i)),
      offset (NativeContractedUnitParent.line D a p (originalLabel R i))) ≤ r)

lemma source_containedTubeCount {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (a : ℝ) (p : Parent) (hp : ∀i∈R,parentLabel D a 1 i=p) (U : Set E4) :
    wzContainedTubeCount (source h original R a p hp) U=
      (R.filter (fun j => markedUnitTube (NativeContractedUnitParent.line D a p j) (D.thickness/64) ⊆ U)).card := by
  exact card_filter_originalLabel R (fun j => markedUnitTube (NativeContractedUnitParent.line D a p j) (D.thickness/64) ⊆ U)

lemma convex_contractPoint_preimage {U : Set E4} (hU : Convex ℝ U) :
    Convex ℝ (contractPoint ⁻¹' U) := by
  intro x hx y hy u v hu hv huv
  have he : contractPoint (u • x+v • y)=u • contractPoint x+v • contractPoint y := by
    unfold contractPoint
    module
  change contractPoint (u • x+v • y)∈U
  rw [he]
  exact hU hx hy hu hv huv

lemma convex_physicalMap_preimage {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent)
    {U : Set E4} (hU : Convex ℝ U) : Convex ℝ (physicalMap D a p ⁻¹' U) := by
  exact NativeUnitParentVolume.convex_preimage _ _ (convex_contractPoint_preimage hU)

/-- The exact inverse Jacobian of the complete original physical map is512^4. -/
lemma volume_physicalMap_preimage {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (p : Parent) (U : Set E4) :
    volume (physicalMap D a p ⁻¹' U)=(512:ℝ≥0∞)^4*volume U := by
  change volume (pointMap ((shift D a:ℝ)*mesh D) p ⁻¹' (contractPoint ⁻¹' U))=_
  rw [NativeUnitParentVolume.volume_preimage]
  have hs : volume (contractPoint ⁻¹' U)=(1048576:ℝ≥0∞)*volume U := by
    change volume (((1/32:ℝ) • ·) ⁻¹' U)=(1048576:ℝ≥0∞)*volume U
    rw [Measure.addHaar_preimage_smul volume (by norm_num : (1/32:ℝ) ≠ 0)]
    norm_num [finrank_euclideanSpace_fin]
  rw [hs]
  norm_num
  ring

/-- CW is derived for the actual constructed source. The original/retained
cardinality cost remains visible as the original n until the true retention
estimate is applied; no new CW profile is postulated. -/
theorem source_CW_original_count {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (p : Parent) (hp : ∀i∈R,parentLabel D a 1 i=p)
    (U : Set E4) (hU : Convex ℝ U) :
    (wzContainedTubeCount (source h original R a p hp) U:ℝ≥0∞) ≤
      (512:ℝ≥0∞)^4*(ENNReal.ofReal D.thickness).rpow (-eta)*volume U*n := by
  rw [source_containedTubeCount]
  let F := physicalMap D a p
  have hc : (R.filter (fun j => markedUnitTube (NativeContractedUnitParent.line D a p j) (D.thickness/64) ⊆ U)).card ≤
      wzContainedTubeCount D (F ⁻¹' U) := by
    apply card_le_card
    intro i hi
    obtain ⟨hiR,hiU⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    intro x hx
    exact hiU (original_tube_maps_into_contracted h ha p i (hp i hiR) (Set.mem_image_of_mem F hx))
  have hw := h.1.2.2.2.2.2.2.2.2.2.2.2.1 (F ⁻¹' U) (convex_physicalMap_preimage D a p hU)
  have hv : volume (F ⁻¹' U)=(512:ℝ≥0∞)^4*volume U := volume_physicalMap_preimage D a p U
  rw [hv] at hw
  exact (show _ ≤ (wzContainedTubeCount D (F ⁻¹' U):ℝ≥0∞) by exact_mod_cast hc).trans
    (hw.trans_eq (by ring))
end NativePaddedSourceTransport
