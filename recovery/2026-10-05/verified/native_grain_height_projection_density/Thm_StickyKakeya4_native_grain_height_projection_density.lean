import Theorems.Thm_StickyKakeya4_native_grain_height_projection_fibers

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeGrainHeightProjectionDensity
open Classical Finset StickyKakeya4 NativeGrainQuotientGeometry NativeGrainQuotientBins
open NativeGrainQuotientFibers NativeGrainQuotientImage NativeGrainHeightProjectionSource
open NativeGrainHeightProjectionFibers NativeHorizontalGrainSlice NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeSquaredGrainQueries NativeParentGrainIncidenceCleanup
open NativeProjectorCellChart NativeDirectionRankDichotomy NativeCompatibleNodeDirections
open NativeSpatialAngularGeometry

/-- The new quotient cost uses at most four additional inverse powers of q. -/
lemma quotient_cost_le_fourth (ell : ℕ) (hell4 : ell ≤ 4) {q : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) :
    (32002*(4/q)^ell)^(4-ell) ≤ (32002:ℝ)^4*(4/q)^4 := by
  have hbase : (1:ℝ) ≤ 4/q := (le_div_iff₀ hq).mpr (by linarith)
  have hexp : ell*(4-ell) ≤ 4 := by interval_cases ell <;> norm_num
  rw [mul_pow,←pow_mul]
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 32002) (Nat.sub_le 4 ell))
    (pow_le_pow_right₀ hbase hexp) (by positivity) (by positivity)

/-- Source-facing dense X at the coarse node's actual quotient class. It
contains ALL raw heights in that class; the visible time factor is only an
X-bin preimage bound, and no point is moved to a surrogate location. -/
theorem source_exists_dense_wholeX {n ell m : ℕ} {D : FiniteScaleSource n} {eta a q r : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r)
    (hm6 : 6 ≤ m) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    {E0 : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E0 S q ell point tuple anchor)
    (A : Index → Submodule ℝ E4) (hA : ∀k∈S,Module.finrank ℝ (A k)=ell)
    (hnear : ∀z∈E0,Metric.infDist (slopeVector D z.1) (A z.2:Set E4) ≤ r)
    (hrD : r ≤ 64/((2^m:ℕ):ℝ))
    (E : Finset (Fin n × Index)) (hEE0 : E⊆E0) (c : Parent × (Index × Index))
    (z : Fin n × Index) (hz : z∈mixedFiber D a m (nodePlane D tuple) ell E c) (hzS : z.2∈S)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=ell-1)
    (hc : cell P=cell (sliceSpace (nodePlane D tuple c.2.1))) :
    let mu := physicalMesh m (phaseDepth m)/8
    let V := mixedVertices D a m (phaseDepth m) (nodePlane D tuple) ell E c
    let f := fun k => label mu (rawCoordinates D a m ell c.1 P
      (sliceSpace (nodePlane D tuple c.2.1)) hP hell hell4 hd k)
    ∃b∈V.image f,
      (wholeFiber D a m ell (nodePlane D tuple) E c P hP hell hell4 hd mu b).Nonempty ∧
      (wholeX D a m ell (nodePlane D tuple) E c P hP hell hell4 hd mu b).Nonempty ∧
      (V.card:ℝ) ≤ (32002*(4/q)^ell)^(4-ell)*(((2^(phaseDepth m-m):ℕ):ℝ))*
        (wholeX D a m ell (nodePlane D tuple) E c P hP hell hell4 hd mu b).card := by
  intro mu V f
  have hm : m ≤ phaseDepth m := by dsimp [phaseDepth]; omega
  have hmu : 0 < mu := div_pos (physicalMesh_pos m (phaseDepth m)) (by norm_num)
  have hV : V.Nonempty := ⟨spatialLabel D (2^(phaseDepth m)) z.2,mem_image_of_mem _ hz⟩
  have hcount : ((V.image f).card:ℝ) ≤ (32002*(4/q)^ell)^(4-ell) :=
    (source_occupied_quotient_card h hq hq1 hr hm hell hell4 H A hA hnear hrD E hEE0 c z hz hzS
      P hP hd hc mu hmu).trans (source_quotient_cost m ell hm6 hq hq1)
  obtain ⟨b,hb,hF,hX,hdense⟩ := exists_dense_wholeX D a m ell hm (nodePlane D tuple) E c hV
    P hP hell hell4 hd mu hmu le_rfl
  refine ⟨b,hb,hF,hX,hdense.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

end NativeGrainHeightProjectionDensity
