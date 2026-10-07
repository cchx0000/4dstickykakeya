import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeWeightedGrainQuotientSource
open Classical Finset StickyKakeya4 NativeWeightedGrainQuotientSelection NativeWeightedGrainQuotientGeometry
open NativeGrainHeightProjectionSource NativeGrainHeightProjectionDensity NativeGrainQuotientFibers
open NativeHorizontalGrainSlice NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeSquaredGrainQueries NativeParentGrainIncidenceCleanup NativeProjectorCellChart
open NativeDirectionRankDichotomy NativeCompatibleNodeDirections NativeSpatialAngularGeometry RichDirectionalLayers

/-- Computed uniform all-height quotient cap, independent of the grain. -/
def quotientCap (q : ℝ) : ℝ := (32002:ℝ)^4*(4/q)^4

lemma quotientCap_pos {q : ℝ} (hq : 0 < q) : 0 < quotientCap q := by unfold quotientCap; positivity

/-- Every actual original mixed grain has at most the computed number of
occupied quotient labels. The count is derived on original physical points. -/
theorem source_quotient_cap {n ell m : ℕ} {D : FiniteScaleSource n} {eta a q r : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r)
    (hm6 : 6 ≤ m) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    {E0 : Finset (Fin n × Index)} {S0 : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (Hsys : IsNodeDirectionSystem D a m E0 S0 q ell point tuple anchor)
    (A : Index → Submodule ℝ E4) (hA : ∀k∈S0,Module.finrank ℝ (A k)=ell)
    (hnear : ∀z∈E0,Metric.infDist (slopeVector D z.1) (A z.2:Set E4) ≤ r)
    (hrD : r ≤ 64/((2^m:ℕ):ℝ))
    (H : Finset (Fin n × Index)) (hHE0 : H⊆E0) (hpoints : ∀z∈H,z.2∈S0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=ell-1)
    (hchart : ∀z∈H,cell P=cell (sliceSpace (nodePlane D tuple (spatialLabel D (2^m) z.2))))
    (c : Parent × (Index × Index)) :
    (((mixedFiber D a m (nodePlane D tuple) ell H c).image
      (quotientLabel D a m ell (nodePlane D tuple) P hP hell hell4 hd (physicalMesh m (phaseDepth m)/8))).card:ℝ) ≤
        quotientCap q := by
  rw [quotient_image_eq]
  have hm : m ≤ phaseDepth m := by dsimp [phaseDepth]; omega
  have hmu : 0 < physicalMesh m (phaseDepth m)/8 := div_pos (physicalMesh_pos _ _) (by norm_num)
  by_cases hn : (mixedFiber D a m (nodePlane D tuple) ell H c).Nonempty
  · obtain ⟨z,hz⟩ := hn
    have hzc := hz
    simp only [mixedFiber,classFiber,mem_filter] at hzc
    have hnode : spatialLabel D (2^m) z.2=c.2.1 := congrArg (fun c : Parent × (Index × Index) => c.2.1) hzc.2
    have hc := hchart z hzc.1
    rw [hnode] at hc
    exact (source_occupied_quotient_card h hq hq1 hr hm hell hell4 Hsys A hA hnear hrD H hHE0 c z hz
      (hpoints z hzc.1) P hP hd hc _ hmu).trans
        ((source_quotient_cost m ell hm6 hq hq1).trans (quotient_cost_le_fourth ell hell4 hq hq1))
  · rw [not_nonempty_iff_eq_empty] at hn
    simp only [mixedVertices,hn,image_empty,card_empty,Nat.cast_zero]
    exact (quotientCap_pos hq).le

/-- Original-incidence weighted retention with simultaneous per-grain
lower bounds and exact preservation of the occupied mixed-grain alphabet. -/
theorem source_retention {n ell m : ℕ} {D : FiniteScaleSource n} {eta a q r : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r)
    (hm6 : 6 ≤ m) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    {E0 : Finset (Fin n × Index)} {S0 : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (Hsys : IsNodeDirectionSystem D a m E0 S0 q ell point tuple anchor)
    (A : Index → Submodule ℝ E4) (hA : ∀k∈S0,Module.finrank ℝ (A k)=ell)
    (hnear : ∀z∈E0,Metric.infDist (slopeVector D z.1) (A z.2:Set E4) ≤ r)
    (hrD : r ≤ 64/((2^m:ℕ):ℝ))
    (H : Finset (Fin n × Index)) (hHE0 : H⊆E0) (hpoints : ∀z∈H,z.2∈S0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=ell-1)
    (hchart : ∀z∈H,cell P=cell (sliceSpace (nodePlane D tuple (spatialLabel D (2^m) z.2)))) :
    let mu := physicalMesh m (phaseDepth m)/8
    let S := retained D a m ell (nodePlane D tuple) H P hP hell hell4 hd mu
    S⊆H ∧ H.card ≤ ⌈quotientCap q⌉₊*S.card ∧
      S.image (mixedLabel D a m (nodePlane D tuple) ell)=H.image (mixedLabel D a m (nodePlane D tuple) ell) ∧
      ∀c : Parent × (Index × Index),
        ((mixedFiber D a m (nodePlane D tuple) ell H c).card:ℝ) ≤
          quotientCap q*(mixedFiber D a m (nodePlane D tuple) ell S c).card := by
  intro mu S
  let g := mixedLabel D a m (nodePlane D tuple) ell
  let f := quotientLabel D a m ell (nodePlane D tuple) P hP hell hell4 hd mu
  have hcap (c : Parent × (Index × Index)) : (((grain H g c).image f).card:ℝ) ≤ quotientCap q := by
    dsimp only [g,f]
    rw [grain_mixed_eq]
    exact source_quotient_cap h hq hq1 hr hm6 hell hell4 Hsys A hA hnear hrD H hHE0 hpoints P hP hd hchart c
  refine ⟨retained_subset D a m ell _ H P hP hell hell4 hd mu,
    card_retention_ceil H g f (quotientCap q) hcap,selected_grain_image (fun _ => 1) H g f,?_⟩
  intro c
  simpa only [g,f,S,retained,grain_mixed_eq] using local_card_retention H g f c (quotientCap q) (hcap c)

/-- Any already computed original mixed-incidence threshold transfers to
EVERY retained occurrence, with the sharp real quotient loss displayed. -/
theorem threshold_transfer {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H S : Finset (Fin n × Index)) (hSH : S⊆H)
    (C L : ℝ)
    (hret : ∀c : Parent × (Index × Index),((mixedFiber D a m plane ell H c).card:ℝ) ≤
      C*(mixedFiber D a m plane ell S c).card)
    (hthreshold : ∀x∈H,L < ((mixedFiber D a m plane ell H (mixedLabel D a m plane ell x)).card:ℝ)) :
    ∀x∈S,L < C*(mixedFiber D a m plane ell S (mixedLabel D a m plane ell x)).card := by
  intro x hx
  exact (hthreshold x (hSH hx)).trans_le (hret _)

end NativeWeightedGrainQuotientSource
