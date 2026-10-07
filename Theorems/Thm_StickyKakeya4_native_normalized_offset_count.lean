import Theorems.Thm_StickyKakeya4_native_normalized_offset_field

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeNormalizedOffsetCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu NativeHeightMetricMenu
open NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric NativeNormalizedOffsetField
open NativeIncidentAffineAnchorGeometry NativeGrainQuotientInjection NativeGrainQuotientBins
open NativeReferenceXYGridLinear NativeHorizontalGrainSlice
open scoped Matrix.Norms.Elementwise

/-- The offset count now consumes the actual field modulus and physical
cell membership. Its variation bound is derived, including height rounding. -/
theorem offset_count_from_raw_field {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m M : ℕ) (hM : 0 < M) (p : Parent) (I : Finset (Fin n × Index))
    (hp : ∀z∈I,parentLabel D a (2^m) z.1=p) (cell : Index)
    (hcell : ∀z∈I,physicalCell D a (2^m) M p z.2=cell)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (ell : ℕ)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin (4-ell))) (error metric shift d : ℝ)
    (he : 0 ≤ error) (hmetric : 0 ≤ metric) (hwindow : meshWidth m/512 ≤ 64/(M:ℝ))
    (hF : ∀k∈I.image Prod.snd,‖F (rawHeight D m k)‖ ≤ (1/4:ℝ))
    (Hmetric : ∀z∈I,∀w∈I,‖F (rawHeight D m z.2)-F (rawHeight D m w.2)‖ ≤
      metric*|chartHeightCoordinate m shift (rawHeight D m z.2)-
        chartHeightCoordinate m shift (rawHeight D m w.2)|)
    (hres : ∀z∈I,‖quotientMap P hP ell hell hell4 hd (F (rawHeight D m z.2))
      (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error)
    (hlower : ∀k∈I.image Prod.snd,d ≤
      (((I.filter (fun z => z.2=k)).image (fun z => angularCell D (2^m) M p z.1)).card:ℝ)) :
    let H := 2*error+48/(M:ℝ)+16*metric*(64/(M:ℝ))
    d*((I.image (fun z => label H (xi z.2))).card:ℝ) ≤
      (4:ℝ)^(4-ell)*(I.image (fun z => angularCell D (2^m) M p z.1)).card := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have Hvar := raw_field_variation D a (2^m) M m hM p I cell hcell F metric shift hmetric Hmetric
  have hvar : ∀k∈I.image Prod.snd,∀l∈I.image Prod.snd,
      ‖F (rawHeight D m k)-F (rawHeight D m l)‖ ≤ 2*metric*(64/(M:ℝ)) :=
    fun k hk l hl => (Hvar k hk l hl).trans (window_variation_le_twice hmetric hwindow)
  have hh := NativeActualOffsetMenu.actual_offset_count D a (2^m) M hM p I hp P hP ell hell hell4 hd
    (fun k => F (rawHeight D m k)) xi error (2*metric*(64/(M:ℝ))) d hF hvar hres hlower (by positivity)
  have heq : 2*error+48/(M:ℝ)+8*(2*metric*(64/(M:ℝ)))=
      2*error+48/(M:ℝ)+16*metric*(64/(M:ℝ)) := by ring
  simpa only [heq] using hh

/-- The same estimate for the actual mapped field on any later retained
incidence subset. Its raw readback avoids an additional factor3 in the modulus. -/
theorem offset_count_from_mapped_field {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m M : ℕ) (hM : 0 < M) (p : Parent) (I : Finset (Fin n × Index))
    (hp : ∀z∈I,parentLabel D a (2^m) z.1=p) (cell : Index)
    (hcell : ∀z∈I,physicalCell D a (2^m) M p z.2=cell)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (ell : ℕ)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (plane : Index → Submodule ℝ E4) (S : Finset (Fin n × Index))
    (hI : I⊆NativeTranslatedGrainHeightSelection.second D a m ell plane S)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin (4-ell))) (error metric shift d : ℝ)
    (he : 0 ≤ error) (hmetric : 0 ≤ metric) (hwindow : meshWidth m/512 ≤ 64/(M:ℝ))
    (hF : ∀k∈I.image Prod.snd,‖mapped D a m ell plane S F (translatedHeight D a m k)‖ ≤ (1/4:ℝ))
    (Hmetric : ∀z∈I,∀w∈I,‖F (rawHeight D m z.2)-F (rawHeight D m w.2)‖ ≤
      metric*|chartHeightCoordinate m shift (rawHeight D m z.2)-
        chartHeightCoordinate m shift (rawHeight D m w.2)|)
    (hres : ∀z∈I,‖quotientMap P hP ell hell hell4 hd
      (mapped D a m ell plane S F (translatedHeight D a m z.2))
      (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error)
    (hlower : ∀k∈I.image Prod.snd,d ≤
      (((I.filter (fun z => z.2=k)).image (fun z => angularCell D (2^m) M p z.1)).card:ℝ)) :
    let H := 2*error+48/(M:ℝ)+16*metric*(64/(M:ℝ))
    d*((I.image (fun z => label H (xi z.2))).card:ℝ) ≤
      (4:ℝ)^(4-ell)*(I.image (fun z => angularCell D (2^m) M p z.1)).card := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have Hvar := mapped_raw_field_variation D a (2^m) M m ell hM p plane S I hI
    cell hcell F metric shift hmetric Hmetric
  have hvar : ∀k∈I.image Prod.snd,∀l∈I.image Prod.snd,
      ‖mapped D a m ell plane S F (translatedHeight D a m k)-
        mapped D a m ell plane S F (translatedHeight D a m l)‖ ≤ 2*metric*(64/(M:ℝ)) :=
    fun k hk l hl => (Hvar k hk l hl).trans (window_variation_le_twice hmetric hwindow)
  have hh := NativeActualOffsetMenu.actual_offset_count D a (2^m) M hM p I hp P hP ell hell hell4 hd
    (fun k => mapped D a m ell plane S F (translatedHeight D a m k)) xi error (2*metric*(64/(M:ℝ))) d
    hF hvar hres hlower (by positivity)
  have heq : 2*error+48/(M:ℝ)+8*(2*metric*(64/(M:ℝ)))=
      2*error+48/(M:ℝ)+16*metric*(64/(M:ℝ)) := by ring
  simpa only [heq] using hh

end NativeNormalizedOffsetCount
