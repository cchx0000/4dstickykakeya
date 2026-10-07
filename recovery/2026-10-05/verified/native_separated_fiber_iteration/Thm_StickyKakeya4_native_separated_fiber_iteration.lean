import Theorems.Thm_StickyKakeya4_native_approximate_fiber_iteration
import Theorems.Thm_StickyKakeya4_native_direction_rank_wedge
import Theorems.Thm_StickyKakeya4_native_rank_one_slope_cap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeSeparatedFiberIteration
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeApproximateFiberCount NativeApproximateFiberIteration BackwardFiberGrains
open NativeDirectionRankDichotomy NativeDirectionRankWedge
open scoped BigOperators

/-- Reverse the chronological indexing, while retaining every actual label. -/
def reverseFamily {α : Type*} (v : α → E4) (xs : List α) (i : Fin xs.length) : E4 :=
  v (xs.get i.rev)

lemma reverseFamily_range {α : Type*} (v : α → E4) (xs : List α) :
    Set.range (reverseFamily v xs)=Set.range (fun i : Fin xs.length => v (xs.get i)) := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.rev,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨i.rev,by simp only [reverseFamily,Fin.rev_rev]⟩

lemma reverseFamily_prefix_image {α : Type*} (v : α → E4) (xs : List α) (i : Fin xs.length) :
    (reverseFamily v xs) '' {j : Fin xs.length | j.val < i.val} =
      (fun j : Fin xs.length => v (xs.get j)) '' Set.Ioi i.rev := by
  ext x
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ⟨j.rev,Fin.rev_lt_rev.mpr hj,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    have hlt : j.rev < i := by simpa only [Fin.rev_rev] using Fin.rev_lt_rev.mpr hj
    exact ⟨j.rev,hlt,by simp only [reverseFamily,Fin.rev_rev]⟩

/-- Actual tail separation becomes prefix separation under this fixed reversal. -/
theorem separated_prefix_distances {α : Type*} (v : α → E4) (q : ℝ) (xs : List α)
    (hxs : Separated v q xs) :
    ∀i : Fin xs.length,q ≤ Metric.infDist (reverseFamily v xs i)
      (prefixSpan (reverseFamily v xs) i.val:Set E4) := by
  intro i
  rw [prefixSpan,reverseFamily_prefix_image v xs i]
  exact separated_tail_distances v q xs hxs i.rev

/-- Quantitative approximate fiber iteration for an actually separated tuple.
The computed predecessor factors concern the original thin h-neighborhoods. -/
theorem separated_lower_bound {α : Type*} (v : α → E4) (xs : List α)
    (hlen : xs.length ≤ 4) {q : ℝ} (hxs : Separated v q xs)
    (A : ℕ → Finset Index) {mesh : ℝ} (hm : 0 < mesh) (hq : 0 < q) (hq1 : q ≤ 1)
    (h C : ℝ) (hh : 0 < h) (hC : 1 ≤ C) (hwidth : h ≤ C*mesh)
    (hv : ∀i : Fin xs.length,‖v (xs.get i)‖ ≤ 2) (x : Index) (hx : x∈A xs.length) :
    ((∏i∈range xs.length,predecessorMinimum mesh A (reverseFamily v xs) h i):ℝ)/
        ((41*(256*C)/q)^4)^xs.length ≤
      ((fiber mesh (A 0) (spanOf v xs) (cellCenter mesh x) (radius h xs.length)).card:ℝ) := by
  have hresult := full_lower_bound A (reverseFamily v xs) hlen hm q h C hq hq1 hh hC hwidth
    (separated_prefix_distances v q xs hxs) (fun i => hv i.rev) x hx
  simpa only [reverseFamily_range,spanOf] using hresult

/-- The actual incident-label chain supplies every separation and direction
norm bound used by the geometric iteration. No hpred or transversality input
is added; the vertex layers and their same-scale mesh remain explicit. -/
theorem native_chain_lower_bound {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (hNative : IsWangZakharovNativeFiniteInput D eta)
    (E : Finset (Fin n × Index)) (k : Index) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ell : ℕ) (hell : ell ≤ 4) (xs : List (Fin n × Index))
    (hxs : xs∈chains (E.filter (fun z => z.2=k)) (fun z => slopeVector D z.1) q ell)
    (A : ℕ → Finset Index) {mesh : ℝ} (hm : 0 < mesh) (h C : ℝ)
    (hh : 0 < h) (hC : 1 ≤ C) (hwidth : h ≤ C*mesh)
    (x : Index) (hx : x∈A xs.length) :
    ((∏i∈range xs.length,predecessorMinimum mesh A
        (reverseFamily (fun z : Fin n × Index => slopeVector D z.1) xs) h i):ℝ)/
        ((41*(256*C)/q)^4)^xs.length ≤
      ((fiber mesh (A 0) (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs)
        (cellCenter mesh x) (radius h xs.length)).card:ℝ) := by
  have hlen : xs.length ≤ 4 := by
    rw [chains_length _ _ _ _ _ hxs]
    exact hell
  exact separated_lower_bound (fun z : Fin n × Index => slopeVector D z.1) xs hlen
    (chains_separated _ _ _ _ _ hxs) A hm hq hq1 h C hh hC hwidth
    (fun i => NativeRankOneSlopeCap.slopeVector_norm_le_two hNative (xs.get i).1) x hx

end NativeSeparatedFiberIteration
