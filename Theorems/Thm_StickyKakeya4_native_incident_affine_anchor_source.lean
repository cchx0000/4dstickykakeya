import Theorems.Thm_StickyKakeya4_native_incident_affine_anchor_geometry
import Theorems.Thm_StickyKakeya4_native_small_loss_parent_budget
import Theorems.Thm_StickyKakeya4_native_actual_height_slope_variation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeIncidentAffineAnchorSource
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeSpatialAngularGeometry
open NativeOriginalParentSelection NativeLocalParentGeometry NativeDirectionRankDichotomy
open NativeHorizontalGrainSlice NativeHorizontalGraphCoordinates NativeHeightSlopeCoordinates
open NativeGrainQuotientGeometry NativeGrainQuotientInjection NativeProjectorCellChart
open NativeIncidentAffineAnchorGeometry NativeCompatibleNodeDirections NativeActualHorizontalGrainSlice
open NativeActualHeightSlopeVariation NativeRankExponentHierarchy NativeRetainedQueryMenu
open NativeMiddleGrainParentBudget NativeSmallLossParentBudget
open scoped BigOperators Matrix.Norms.Elementwise

/-- Definition17.2(4)'s LOCAL affine-anchor estimate on the current retained
parent incidence family. Anchors are actual current tubes at the same original
point. The direction error is derived from the source hierarchy, not assumed.
No relation between anchors at different points is asserted. -/
theorem exists_actual_incident_affine_anchors {n : ℕ} {D : FiniteScaleSource n}
    {eta a q r eta0 c tau epsilon : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hr : 0 < r) (hr1 : r ≤ 1)
    (he : 0 < epsilon) (heHalf : epsilon ≤ 1/2)
    (he0 : 0 ≤ eta0) (heSmall : eta0 ≤ epsilon)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcSmall : c ≤ epsilon/24) (rank : Fin 4) (hrank : rank.val+1 ≤ 3)
    (hrdelta : r ≤ D.thickness^(cutoff c rank)) (htau : 0 ≤ tau) (g K stop m : ℕ)
    (hK : 0 < K) (hs : 6 ≤ stop) (hm : m=grainDepth (2*K) stop (middleIndex K))
    (hTau : tau ≤ commonBudget eta0 c/(1000*(((2*K:ℕ):ℝ)+1)))
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hq : 0 < q) (hq1 : q ≤ 1) (hqlow : r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1)
    (hsmall : D.thickness^(cutoff c rank*epsilon/2) ≤ 1/errorConstant)
    (E H : Finset (Fin n × Index)) (hHE : H⊆E) (S0 : Finset Index)
    (hpoints : ∀z∈H,z.2∈S0)
    (point : Index → Index) (tuple : Index → Fin (rank.val+1) → (Fin n × Index))
    (anchor : Index → Fin (rank.val+1) → Fin n)
    (Hsys : IsNodeDirectionSystem D a m E S0 q (rank.val+1) point tuple anchor)
    (oldPlane : Index → Submodule ℝ E4) (hOld : ∀k∈S0,Module.finrank ℝ (oldPlane k)=rank.val+1)
    (hnear : ∀z∈E,Metric.infDist (slopeVector D z.1) (oldPlane z.2:Set E4) ≤ r)
    (parent : Parent) (hparent : ∀z∈H,parentLabel D a (2^m) z.1=parent)
    (P0 : Submodule ℝ E4) (hP0 : P0≤heightKernel) (hd : Module.finrank ℝ P0=(rank.val+1)-1)
    (hCell : ∀k∈H.image Prod.snd,cell P0=cell (horizontalPlane D tuple (spatialLabel D (2^m) k)))
    (f : ℤ → Matrix (Fin (4-(rank.val+1))) (Fin ((rank.val+1)-1)) ℝ)
    (hread : ∀k∈H.image Prod.snd,f (spatialLabel D (2^m) k (3:Fin 4))=
      nodeSlope P0 hP0 (rank.val+1) (by omega) (by omega) hd
        (horizontalPlane D tuple (spatialLabel D (2^m) k))
        (horizontalPlane_le D tuple (spatialLabel D (2^m) k))) :
    ∃j : Index → Fin n,∃xi : Index → EuclideanSpace ℝ (Fin (4-(rank.val+1))),
      ∀k∈H.image Prod.snd,(j k,k)∈H ∧
        xi k=normalCoordinates P0 hP0 (rank.val+1) (by omega) (by omega) hd
            (localHorizontalSlope D (2^m) parent (j k))-
          matrixVector (f (spatialLabel D (2^m) k (3:Fin 4)))
            (tangentCoordinates P0 (rank.val+1) hd (localHorizontalSlope D (2^m) parent (j k))) ∧
        ‖xi k‖ ≤ (5/2:ℝ) ∧
        ∀i : Fin n,(i,k)∈H→
          ‖normalCoordinates P0 hP0 (rank.val+1) (by omega) (by omega) hd
              (localHorizontalSlope D (2^m) parent i)-xi k-
            matrixVector (f (spatialLabel D (2^m) k (3:Fin 4)))
              (tangentCoordinates P0 (rank.val+1) hd (localHorizontalSlope D (2^m) parent i))‖ ≤
            (5/4:ℝ)*((64:ℝ)/((2^m:ℕ):ℝ))^(1-2*epsilon) := by
  let Q := fun k => horizontalPlane D tuple (spatialLabel D (2^m) k)
  have hkS : ∀k∈H.image Prod.snd,k∈S0 := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
    exact hpoints z hz
  have hQ : ∀k∈H.image Prod.snd,Q k≤heightKernel := fun k _ => horizontalPlane_le D tuple _
  have hDim : ∀k∈H.image Prod.snd,Module.finrank ℝ P0=Module.finrank ℝ (Q k) := by
    intro k hk
    have hnode : spatialLabel D (2^m) k∈nodes D m S0 := mem_image_of_mem _ (hkS k hk)
    have hh := (node_graph_direction Hsys (by omega) hq _ hnode).1
    exact hd.trans hh.symm
  have herror : ∀k∈H.image Prod.snd,∀i j : Fin n,(i,k)∈H→(j,k)∈H→
      Metric.infDist (localHorizontalSlope D (2^m) parent i-localHorizontalSlope D (2^m) parent j)
        (Q k:Set E4) ≤ ((64:ℝ)/((2^m:ℕ):ℝ))^(1-2*epsilon) := by
    intro k hk i j hi hj
    have Hsys' : IsNodeDirectionSystem D a (grainDepth (2*K) stop (middleIndex K)) E S0 q
        (rank.val+1) point tuple anchor := by simpa only [hm] using Hsys
    have hpair : parentLabel D a (2^(grainDepth (2*K) stop (middleIndex K))) i=
        parentLabel D a (2^(grainDepth (2*K) stop (middleIndex K))) j := by
      simpa only [hm] using (hparent (i,k) hi).trans (hparent (j,k) hj).symm
    have hh := actual_middle_parent_direction_small_loss h hr hr1 he heHalf he0 heSmall hc hc1 hcSmall
      rank hrank hrdelta htau g K stop hK hs hTau hgrid hq hq1 hqlow hidentity hsmall
      Hsys' oldPlane hOld hnear k (hkS k hk) i j (hHE hi) (hHE hj) hpair
    change Metric.infDist (((2^(grainDepth (2*K) stop (middleIndex K)):ℕ):ℝ) •
      (slopeVector D i-slopeVector D j))
      (horizontalPlane D tuple (spatialLabel D (2^(grainDepth (2*K) stop (middleIndex K))) k):Set E4) ≤ _ at hh
    rw [←hm] at hh
    have hmid : m=middleDepth stop := hm.trans (grainDepth_middle K stop hK hs)
    rw [←hmid] at hh
    rw [localHorizontalSlope_sub]
    exact hh
  exact exists_incident_affine_anchors D a m parent H ⟨0,h.1.1⟩ hparent P0 hP0
    (rank.val+1) (by omega) (by omega) hd Q hQ hDim hCell f hread
    (((64:ℝ)/((2^m:ℕ):ℝ))^(1-2*epsilon)) herror

end NativeIncidentAffineAnchorSource
