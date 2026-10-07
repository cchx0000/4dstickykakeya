import Theorems.Thm_StickyKakeya4_native_separated_span_control
import Theorems.Thm_StickyKakeya4_native_equal_rank_plane_transfer
import Theorems.Thm_StickyKakeya4_native_global_angular_representatives
import Theorems.Thm_StickyKakeya4_native_rank_one_slope_cap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeActualTuplePlaneTransfer
open Classical Finset StickyKakeya4 NativeDirectionRankDichotomy
open NativeSeparatedSpanControl NativeEqualRankPlaneTransfer
open NativeGlobalAngularRepresentatives NativeOriginalAngularTupleMenu
open NativeIncidentRankSelection NativeCommonCubicalMesh NativeOriginalParentSelection

/-- The rank of the actual selected span follows from its original chain. -/
theorem chain_span_finrank {n : ℕ} (D : FiniteScaleSource n)
    (A : Finset (Fin n × Index)) (q : ℝ) (hq : 0 < q) (ell : ℕ)
    (xs : List (Fin n × Index))
    (hxs : xs∈chains A (fun z => slopeVector D z.1) q ell) :
    Module.finrank ℝ (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs)=ell := by
  have hi := separated_linearIndependent (fun z : Fin n × Index => slopeVector D z.1) q hq xs
    (chains_separated _ _ _ _ _ hxs)
  rw [spanOf,finrank_span_eq_card hi,Fintype.card_fin]
  exact chains_length _ _ _ _ _ hxs

/-- Transfer the old selected plane to the span of a genuine original chain.
The norm and inverse-frame bounds are derived from the native source and
its actual successive separation, without a supplied plane-gap certificate. -/
theorem actual_chain_plane_transfer {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (hNative : IsWangZakharovNativeFiniteInput D eta)
    (A : Finset (Fin n × Index)) (q r : ℝ) (hq : 0 < q) (hr : 0 < r)
    (ell : ℕ) (P : Submodule ℝ E4) (hP : Module.finrank ℝ P=ell)
    (hnear : ∀z∈A,Metric.infDist (slopeVector D z.1) (P:Set E4) ≤ r)
    (xs : List (Fin n × Index))
    (hxs : xs∈chains A (fun z => slopeVector D z.1) q ell)
    (w : E4) (hw : Metric.infDist w (P:Set E4) ≤ r) :
    Metric.infDist w (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs:Set E4) ≤
      r+4*r*coefficientCost 2 q ell*‖w‖ := by
  have hlen := chains_length _ _ _ _ _ hxs
  have hdim := chain_span_finrank D A q hq ell xs hxs
  have hs := chains_separated _ _ _ _ _ hxs
  have hn : ∀z∈xs,Metric.infDist (slopeVector D z.1) (P:Set E4) ≤ r := by
    intro z hz
    exact hnear z (chains_labels _ _ _ _ _ hxs z hz)
  have hf := span_near_plane (fun z : Fin n × Index => slopeVector D z.1) q 2 r hq
    (by norm_num) hr xs hs (fun z _hz => NativeRankOneSlopeCap.slopeVector_norm_le_two hNative z.1) P hn
  have hC : 0 ≤ coefficientCost 2 q ell := coefficientCost_nonneg (by norm_num) hq ell
  have ht := transfer_near_plane P (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs)
    (2*r*coefficientCost 2 q ell) r (by positivity) hr.le (hP.trans hdim.symm)
    (by simpa only [hlen] using hf) w hw
  convert ht using 1
  ring

/-- The representatives selected globally from E retain the original plane
at every later use. Their witness point may differ from the current one;
only literal original labels are used in both conclusions. -/
theorem exists_global_plane_representatives {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (hNative : IsWangZakharovNativeFiniteInput D eta)
    (a : ℝ) (m : ℕ) (E : Finset (Fin n × Index)) (q r : ℝ)
    (hq : 0 < q) (hr : 0 < r) (ell : ℕ)
    (P : Submodule ℝ E4) (hP : Module.finrank ℝ P=ell)
    (hnear : ∀z∈E,Metric.infDist (slopeVector D z.1) (P:Set E4) ≤ r) :
    ∃ (point : (globalAngularMenu D a m E q ell) → Index)
      (tuple : (globalAngularMenu D a m E q ell) → Fin ell → (Fin n × Index)),
      ∀tau, point tau∈E.image Prod.snd ∧
        (∀j,tuple tau j∈E ∧ (tuple tau j).2=point tau) ∧
        List.ofFn (tuple tau)∈chains (pointSet E (point tau)) (fun z => slopeVector D z.1) q ell ∧
        angularTuple D a m (List.ofFn (tuple tau))=tau.val ∧
        LinearIndependent ℝ (fun j => slopeVector D (tuple tau j).1) ∧
        q^(2*ell) ≤ (Matrix.gram ℝ (fun j => slopeVector D (tuple tau j).1)).det ∧
        Module.finrank ℝ (spanOf (fun z : Fin n × Index => slopeVector D z.1)
          (List.ofFn (tuple tau)))=ell ∧
        ∀z∈E,Metric.infDist (slopeVector D z.1)
          (spanOf (fun z : Fin n × Index => slopeVector D z.1) (List.ofFn (tuple tau)):Set E4) ≤
          r+8*r*coefficientCost 2 q ell := by
  obtain ⟨point,tuple,H⟩ := exists_global_representatives D a m E q hq ell
  refine ⟨point,tuple,?_⟩
  intro tau
  obtain ⟨hp,hl,hc,ha,hi,hg⟩ := H tau
  refine ⟨hp,hl,hc,ha,hi,hg,chain_span_finrank D _ q hq ell _ hc,?_⟩
  intro z hz
  have hn : ∀u∈pointSet E (point tau),Metric.infDist (slopeVector D u.1) (P:Set E4) ≤ r := by
    intro u hu
    exact hnear u (mem_filter.mp hu).1
  have ht := actual_chain_plane_transfer hNative (pointSet E (point tau)) q r hq hr ell P hP hn
    (List.ofFn (tuple tau)) hc (slopeVector D z.1) (hnear z hz)
  have hv := NativeRankOneSlopeCap.slopeVector_norm_le_two hNative z.1
  have hC : 0 ≤ coefficientCost 2 q ell := coefficientCost_nonneg (by norm_num) hq ell
  have hm := mul_le_mul_of_nonneg_left hv (show 0 ≤ 4*r*coefficientCost 2 q ell by positivity)
  nlinarith only [ht,hm]

end NativeActualTuplePlaneTransfer
