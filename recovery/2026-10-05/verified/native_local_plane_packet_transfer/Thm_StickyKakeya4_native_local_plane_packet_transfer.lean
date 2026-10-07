import Theorems.Thm_StickyKakeya4_native_actual_tuple_plane_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeLocalPlanePacketTransfer
open Classical Finset StickyKakeya4 NativeDirectionRankDichotomy
open NativeSeparatedSpanControl NativeEqualRankPlaneTransfer NativeActualTuplePlaneTransfer
open NativeGlobalAngularRepresentatives NativeOriginalAngularTupleMenu NativeOriginalCoarseTupleMenu
open NativeIncidentRankSelection NativeCommonCubicalMesh NativeOriginalParentSelection

/-- Matching literal angular words transfers proximity to the CURRENT old
point's plane. Global representatives need not share its witness point. -/
theorem matching_word_near_plane {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (xs ys : List (Fin n × Index)) (he : angularTuple D a m xs=angularTuple D a m ys)
    (P : Submodule ℝ E4) (r : ℝ)
    (hnear : ∀z∈xs,Metric.infDist (slopeVector D z.1) (P:Set E4) ≤ r) :
    ∀z∈ys,Metric.infDist (slopeVector D z.1) (P:Set E4) ≤ r+2/((2^m:ℕ):ℝ) := by
  have hm : ∀zs,angularTuple D a m zs=zs.map (fun z => (parentLabel D a (2^m) z.1).1) := by
    intro zs
    simp only [angularTuple,coarseTuple,List.map_map]
    rfl
  rw [hm,hm] at he
  intro z hz
  have hmem : (parentLabel D a (2^m) z.1).1∈xs.map (fun z => (parentLabel D a (2^m) z.1).1) := by
    rw [he]
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  obtain ⟨u,hu,huz⟩ := List.mem_map.mp hmem
  have hd := NativeAngularPacketReadback.same_angular_slopeVector_dist D a (2^m) (by positivity) z.1 u.1 huz.symm
  exact (Metric.infDist_le_infDist_add_dist (x:=slopeVector D z.1) (y:=slopeVector D u.1)).trans
    (add_le_add (hnear u hu) hd)

/-- The actual current-point plane may vary with the point. Its rank and
local nearness transfer to a global representative tuple only through the
verified angular-word match, including the explicit 2/N approximation. -/
theorem matching_chain_plane_transfer {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (hNative : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (m : ℕ)
    (A : Finset (Fin n × Index)) (q r : ℝ) (hq : 0 < q) (hr : 0 < r)
    (ell : ℕ) (P : Submodule ℝ E4) (hP : Module.finrank ℝ P=ell)
    (xs ys : List (Fin n × Index))
    (he : angularTuple D a m xs=angularTuple D a m ys)
    (hnear : ∀z∈xs,Metric.infDist (slopeVector D z.1) (P:Set E4) ≤ r)
    (hys : ys∈chains A (fun z => slopeVector D z.1) q ell)
    (w : E4) (hw : Metric.infDist w (P:Set E4) ≤ r) :
    Metric.infDist w (spanOf (fun z : Fin n × Index => slopeVector D z.1) ys:Set E4) ≤
      r+4*(r+2/((2^m:ℕ):ℝ))*coefficientCost 2 q ell*‖w‖ := by
  let h := r+2/((2^m:ℕ):ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  have hlen := chains_length _ _ _ _ _ hys
  have hdim := chain_span_finrank D A q hq ell ys hys
  have hf := span_near_plane (fun z : Fin n × Index => slopeVector D z.1) q 2 h hq
    (by norm_num) hh ys (chains_separated _ _ _ _ _ hys)
    (fun z _hz => NativeRankOneSlopeCap.slopeVector_norm_le_two hNative z.1) P
    (matching_word_near_plane D a m xs ys he P r hnear)
  have hC : 0 ≤ coefficientCost 2 q ell := coefficientCost_nonneg (by norm_num) hq ell
  have ht := transfer_near_plane P (spanOf (fun z : Fin n × Index => slopeVector D z.1) ys)
    (2*h*coefficientCost 2 q ell) r (by positivity) hr.le (hP.trans hdim.symm)
    (by simpa only [hlen] using hf) w hw
  convert ht using 1
  dsimp [h]
  ring


/-- One actual representative tuple per global word controls every compatible
current point using that point's own selected plane. No common-plane premise
is imposed on the original retained source. -/
theorem exists_global_local_plane_representatives {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (hNative : IsWangZakharovNativeFiniteInput D eta)
    (a : ℝ) (m : ℕ) (E : Finset (Fin n × Index)) (q r : ℝ)
    (hq : 0 < q) (hr : 0 < r) (ell : ℕ)
    (P : Index → Submodule ℝ E4) (hP : ∀k∈E.image Prod.snd,Module.finrank ℝ (P k)=ell)
    (hnear : ∀z∈E,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ r) :
    ∃ (point : (globalAngularMenu D a m E q ell) → Index)
      (tuple : (globalAngularMenu D a m E q ell) → Fin ell → (Fin n × Index)),
      ∀tau, point tau∈E.image Prod.snd ∧
        (∀j,tuple tau j∈E ∧ (tuple tau j).2=point tau) ∧
        List.ofFn (tuple tau)∈chains (pointSet E (point tau)) (fun z => slopeVector D z.1) q ell ∧
        angularTuple D a m (List.ofFn (tuple tau))=tau.val ∧
        LinearIndependent ℝ (fun j => slopeVector D (tuple tau j).1) ∧
        q^(2*ell) ≤ (Matrix.gram ℝ (fun j => slopeVector D (tuple tau j).1)).det ∧
        ∀k∈E.image Prod.snd,tau.val∈angularMenu D a m E k q ell →
          ∀z∈pointSet E k,Metric.infDist (slopeVector D z.1)
            (spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple tau)):Set E4) ≤
              r+8*(r+2/((2^m:ℕ):ℝ))*coefficientCost 2 q ell := by
  obtain ⟨point,tuple,H⟩ := exists_global_representatives D a m E q hq ell
  refine ⟨point,tuple,?_⟩
  intro tau
  obtain ⟨hp,hl,hc,ha,hi,hg⟩ := H tau
  refine ⟨hp,hl,hc,ha,hi,hg,?_⟩
  intro k hk hlocal z hz
  obtain ⟨xs,hxs,hmap⟩ := mem_image.mp hlocal
  have hxsnear : ∀u∈xs,Metric.infDist (slopeVector D u.1) (P k:Set E4) ≤ r := by
    intro u hu
    have hpoint := chains_labels _ _ _ _ _ hxs u hu
    obtain ⟨huE,huk⟩ := mem_filter.mp hpoint
    simpa only [huk] using hnear u huE
  have hzE := (mem_filter.mp hz).1
  have hzk := (mem_filter.mp hz).2
  have hznear : Metric.infDist (slopeVector D z.1) (P k:Set E4) ≤ r := by
    simpa only [hzk] using hnear z hzE
  have ht := matching_chain_plane_transfer hNative a m (pointSet E (point tau)) q r hq hr ell
    (P k) (hP k hk) xs (List.ofFn (tuple tau)) (hmap.trans ha.symm) hxsnear hc
    (slopeVector D z.1) hznear
  have hv := NativeRankOneSlopeCap.slopeVector_norm_le_two hNative z.1
  have hC : 0 ≤ coefficientCost 2 q ell := coefficientCost_nonneg (by norm_num) hq ell
  have hm := mul_le_mul_of_nonneg_left hv
    (show 0 ≤ 4*(r+2/((2^m:ℕ):ℝ))*coefficientCost 2 q ell by positivity)
  nlinarith only [ht,hm]

end NativeLocalPlanePacketTransfer
