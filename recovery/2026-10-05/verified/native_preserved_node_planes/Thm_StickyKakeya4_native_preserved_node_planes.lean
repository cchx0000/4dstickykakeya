import Theorems.Thm_StickyKakeya4_native_compatible_node_directions
import Theorems.Thm_StickyKakeya4_native_local_plane_packet_transfer
import Theorems.Thm_StickyKakeya4_native_span_coefficient_power

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativePreservedNodePlanes
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeDirectionRankDichotomy NativeIncidentRankSelection NativeOriginalParentSelection
open NativeCompatibleNodeDirections NativeOriginalCoarseTupleMenu NativeSeparatedSpanControl
open NativeSpatialAngularGeometry NativeOriginalAngularTupleMenu

/-- The already installed node tuple controls every incident old direction.
The selected plane may vary with the original point; no tuple is reselected. -/
theorem incident_near_chosen_span {n ell m : ℕ} {D : FiniteScaleSource n} {eta a q r : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hr : 0 < r)
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E S q ell point tuple anchor)
    (P : Index → Submodule ℝ E4)
    (hP : ∀ k∈S,Module.finrank ℝ (P k)=ell)
    (hnear : ∀ z∈E,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ r)
    (k : Index) (hk : k∈S) (j : Fin n) (hjk : (j,k)∈E) :
    Metric.infDist (slopeVector D j)
      (spanOf (fun z : Fin n × Index => slopeVector D z.1)
        (List.ofFn (tuple (spatialLabel D (2^m) k))):Set E4) ≤
      r+8*(r+2/((2^m:ℕ):ℝ))*coefficientCost 2 q ell := by
  let Q := spatialLabel D (2^m) k
  let xs : Fin ell → (Fin n × Index) := fun i => (anchor k i,k)
  have hQ : Q∈nodes D m S := mem_image_of_mem _ hk
  have hchain := (H.1 Q hQ).2.2.1
  have he : angularTuple D a m (List.ofFn xs)=angularTuple D a m (List.ofFn (tuple Q)) := by
    simp only [angularTuple,coarseTuple,List.map_ofFn,Function.comp_def]
    congr 1
    funext i
    exact (H.2.1 k hk i).2
  have hxs : ∀ z∈List.ofFn xs,Metric.infDist (slopeVector D z.1) (P k:Set E4) ≤ r := by
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact hnear (anchor k i,k) (H.2.1 k hk i).1
  have ht := NativeLocalPlanePacketTransfer.matching_chain_plane_transfer h a m
    (pointSet E (point Q)) q r hq hr ell (P k) (hP k hk)
    (List.ofFn xs) (List.ofFn (tuple Q)) he hxs hchain (slopeVector D j)
    (hnear (j,k) hjk)
  have hv := NativeRankOneSlopeCap.slopeVector_norm_le_two h j
  have hC : 0 ≤ coefficientCost 2 q ell := coefficientCost_nonneg (by norm_num) hq ell
  have hm := mul_le_mul_of_nonneg_left hv
    (show 0 ≤ 4*(r+2/((2^m:ℕ):ℝ))*coefficientCost 2 q ell by positivity)
  dsimp only [Q] at ht
  nlinarith only [ht,hm]

/-- The same literal node plane has a polynomial conditioning cost in the
actual separation, at the actual spatial grain radius. -/
theorem incident_near_grain_plane {n ell m : ℕ} {D : FiniteScaleSource n} {eta a q r : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r)
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E S q ell point tuple anchor)
    (P : Index → Submodule ℝ E4)
    (hP : ∀ k∈S,Module.finrank ℝ (P k)=ell)
    (hnear : ∀ z∈E,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ r)
    (hrD : r ≤ 64/((2^m:ℕ):ℝ))
    (k : Index) (hk : k∈S) (j : Fin n) (hjk : (j,k)∈E) :
    Metric.infDist (slopeVector D j)
      (spanOf (fun z : Fin n × Index => slopeVector D z.1)
        (List.ofFn (tuple (spatialLabel D (2^m) k))):Set E4) ≤
      (1+16*(4/q)^ell)*(64/((2^m:ℕ):ℝ)) := by
  have ht := incident_near_chosen_span h hq hr H P hP hnear k hk j hjk
  have hC := NativeSpanCoefficientPower.coefficientCost_le_power hq hq1 ell
  have hCp : 0 ≤ coefficientCost 2 q ell := coefficientCost_nonneg (by norm_num) hq ell
  have hN : (0:ℝ) < ((2^m:ℕ):ℝ) := by positivity
  have hsmall : 2/((2^m:ℕ):ℝ) ≤ 64/((2^m:ℕ):ℝ) := by gcongr; norm_num
  have hprod := mul_le_mul hC (add_le_add hrD hsmall) (by positivity : 0 ≤ r+2/((2^m:ℕ):ℝ)) (by positivity : 0 ≤ (4/q)^ell)
  nlinarith only [ht,hprod,hrD]

end NativePreservedNodePlanes
