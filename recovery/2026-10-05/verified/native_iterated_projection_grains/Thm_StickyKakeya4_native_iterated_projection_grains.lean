import Theorems.Thm_StickyKakeya4_native_quantized_projection_grains
import Theorems.Thm_StickyKakeya4_native_separated_fiber_iteration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

noncomputable section
namespace NativeIteratedProjectionGrains
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeApproximateFiberCount NativeApproximateFiberIteration BackwardFiberGrains
open NativeQuantizedProjectionGrains NativeSeparatedFiberIteration
open NativeDirectionRankDichotomy
open scoped BigOperators

lemma minimumFiber_attained {α : Type*} (A : Finset Index) (B : Finset α)
    (loc : α → Index) (mesh : ℝ) (P : Submodule ℝ E4) (H : ℝ) (hB : B.Nonempty) :
    ∃b∈B,minimumFiber A B loc mesh P H=(fiber mesh A P (cellCenter mesh (loc b)) H).card := by
  have hV : (B.image loc).Nonempty := hB.image loc
  let f := fun y => (fiber mesh A P (cellCenter mesh y) H).card
  have hS : ((B.image loc).image f).Nonempty := hV.image f
  obtain ⟨y,hy,he⟩ := mem_image.mp (((B.image loc).image f).min'_mem hS)
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
  refine ⟨b,hb,?_⟩
  simp only [minimumFiber,minimumPredecessor,dif_pos hV]
  exact he.symm

/-- The actual predecessor product controls the number of quantized parallel
grains. Both the numerator and all overlap losses are computed from geometry;
no final fiber lower-bound certificate is supplied. -/
theorem iterated_grain_count {α : Type*} {n : ℕ} (A : ℕ → Finset Index)
    (v : Fin n → E4) (B : Finset α) (loc : α → Index)
    {mesh : ℝ} (hm : 0 < mesh) (q h : ℝ) (hq : 0 < q) (hh : 0 < h)
    (htrans : ∀i : Fin n,q ≤ Metric.infDist (v i) (prefixSpan v i.val:Set E4))
    (hv : ∀i : Fin n,‖v i‖ ≤ 2) (hloc : ∀b∈B,loc b∈A n) :
    (B.image (fun b => vertexLabel mesh (Submodule.span ℝ (Set.range v)) (radius h n) (loc b))).card *
        (∏i∈range n,predecessorMinimum mesh A v h i) ≤
      625*(A 0).card*(∏i∈range n,overlap mesh q h i) := by
  by_cases hB : B.Nonempty
  · let P := Submodule.span ℝ (Set.range v)
    let H := radius h n
    let G := (B.image (fun b => vertexLabel mesh P H (loc b))).card
    let L := ∏i∈range n,predecessorMinimum mesh A v h i
    let D := ∏i∈range n,overlap mesh q h i
    obtain ⟨b,hb,he⟩ := minimumFiber_attained (A 0) B loc mesh P H hB
    have hpoint := iterated_count A v hm q h hq hh htrans hv n le_rfl (loc b) (hloc b hb)
    rw [prefixSpan_full] at hpoint
    have hlower : L ≤ D*minimumFiber (A 0) B loc mesh P H := by
      rw [he]
      exact hpoint
    have hcount := grain_count_computed (A 0) B loc mesh P H (radius_pos hh n)
    change G*L ≤ 625*(A 0).card*D
    calc
      _ ≤ G*(D*minimumFiber (A 0) B loc mesh P H) := Nat.mul_le_mul_left G hlower
      _ = D*(G*minimumFiber (A 0) B loc mesh P H) := by ring
      _ ≤ D*(625*(A 0).card) := Nat.mul_le_mul_left D hcount
      _ = _ := by ring
  · have he : B=∅ := not_nonempty_iff_eq_empty.mp hB
    simp only [he,image_empty,card_empty,zero_mul]
    exact Nat.zero_le _

/-- The incident-label chain itself supplies quantitative separation and
direction bounds. The original final labels can map noninjectively to vertices. -/
theorem native_chain_grain_count {α : Type*} {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (hNative : IsWangZakharovNativeFiniteInput D eta)
    (E : Finset (Fin n × Index)) (k : Index) (q : ℝ) (hq : 0 < q)
    (ell : ℕ) (xs : List (Fin n × Index))
    (hxs : xs∈chains (E.filter (fun z => z.2=k)) (fun z => slopeVector D z.1) q ell)
    (A : ℕ → Finset Index) (B : Finset α) (loc : α → Index)
    {mesh : ℝ} (hm : 0 < mesh) (h : ℝ) (hh : 0 < h)
    (hloc : ∀b∈B,loc b∈A xs.length) :
    (B.image (fun b => vertexLabel mesh (spanOf (fun z : Fin n × Index => slopeVector D z.1) xs)
      (radius h xs.length) (loc b))).card *
        (∏i∈range xs.length,predecessorMinimum mesh A
          (reverseFamily (fun z : Fin n × Index => slopeVector D z.1) xs) h i) ≤
      625*(A 0).card*(∏i∈range xs.length,overlap mesh q h i) := by
  have hresult := iterated_grain_count A
    (reverseFamily (fun z : Fin n × Index => slopeVector D z.1) xs) B loc hm q h hq hh
    (separated_prefix_distances _ _ _ (chains_separated _ _ _ _ _ hxs))
    (fun i => NativeRankOneSlopeCap.slopeVector_norm_le_two hNative (xs.get i.rev).1) hloc
  simpa only [reverseFamily_range,spanOf] using hresult

end NativeIteratedProjectionGrains
