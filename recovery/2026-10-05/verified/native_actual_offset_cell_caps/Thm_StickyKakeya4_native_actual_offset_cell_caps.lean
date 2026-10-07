import Theorems.Thm_StickyKakeya4_native_normalized_offset_count
import Theorems.Thm_StickyKakeya4_native_finite_point_coherence

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeActualOffsetCellCaps
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu NativeHeightMetricMenu
open NativeTranslatedGrainHeightOverlap NativeNormalizedOffsetCount NativeIncidentAffineAnchorGeometry
open NativeGrainQuotientInjection NativeGrainQuotientBins NativeReferenceXYGridLinear NativeHorizontalGrainSlice
open scoped Matrix.Norms.Elementwise

lemma point_fiber_in_cell {A X C : Type*} [DecidableEq A] [DecidableEq X] [DecidableEq C]
    (S : Finset A) (point : A → X) (cell : X → C) (c : C) (x : X)
    (hx : x∈(S.filter (fun z => cell (point z)=c)).image point) :
    (S.filter (fun z => cell (point z)=c)).filter (fun z => point z=x)=
      S.filter (fun z => point z=x) := by
  obtain ⟨z,hz,hzx⟩ := mem_image.mp hx
  have hxc : cell x=c := hzx ▸ (mem_filter.mp hz).2
  ext u
  simp only [mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · intro h
    exact ⟨⟨h.1,h.2.symm ▸ hxc⟩,h.2⟩

/-- Convert the actual original-edge/angular lower and union upper into
the offset cap in EVERY normalized physical cell. The time/F readback is
derived internally from the literal cell map. -/
theorem actual_cell_offset_cap {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m M : ℕ) (hM : 0 < M) (p : Parent) (S : Finset (Fin n × Index))
    (hp : ∀z∈S,parentLabel D a (2^m) z.1=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (ell : ℕ)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin (4-ell))) (error metric shift d upper : ℝ)
    (he : 0 ≤ error) (hmetric : 0 ≤ metric) (hwindow : meshWidth m/512 ≤ 64/(M:ℝ)) (hdpos : 0 < d)
    (hF : ∀k∈S.image Prod.snd,‖F (rawHeight D m k)‖ ≤ (1/4:ℝ))
    (Hmetric : ∀z∈S,∀w∈S,‖F (rawHeight D m z.2)-F (rawHeight D m w.2)‖ ≤
      metric*|chartHeightCoordinate m shift (rawHeight D m z.2)-
        chartHeightCoordinate m shift (rawHeight D m w.2)|)
    (hres : ∀z∈S,‖quotientMap P hP ell hell hell4 hd (F (rawHeight D m z.2))
      (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error)
    (hlower : ∀k∈S.image Prod.snd,d ≤
      (((S.filter (fun z => z.2=k)).image (fun z => angularCell D (2^m) M p z.1)).card:ℝ))
    (hupper : ∀c : Index,((angularMenu D a m M p S c).card:ℝ) ≤ upper) :
    let H := 2*error+48/(M:ℝ)+16*metric*(64/(M:ℝ))
    ∀c : Index,(((S.filter (fun z => physicalCell D a (2^m) M p z.2=c)).image
      (fun z => label H (xi z.2))).card:ℝ) ≤ ((4:ℝ)^(4-ell)*upper)/d := by
  intro H c
  let I := S.filter (fun z => physicalCell D a (2^m) M p z.2=c)
  have hIS : I⊆S := filter_subset _ _
  have hlowerI : ∀k∈I.image Prod.snd,d ≤
      (((I.filter (fun z => z.2=k)).image (fun z => angularCell D (2^m) M p z.1)).card:ℝ) := by
    intro k hk
    rw [point_fiber_in_cell S Prod.snd (physicalCell D a (2^m) M p) c k hk]
    exact hlower k (image_subset_image hIS hk)
  have hh := offset_count_from_raw_field D a m M hM p I
    (fun z hz => hp z (hIS hz)) c (fun _z hz => (mem_filter.mp hz).2)
    P hP ell hell hell4 hd F xi error metric shift d he hmetric hwindow
    (fun k hk => hF k (image_subset_image hIS hk))
    (fun z hz w hw => Hmetric z (hIS hz) w (hIS hw))
    (fun z hz => hres z (hIS hz)) hlowerI
  have hbound : d*((I.image (fun z => label H (xi z.2))).card:ℝ) ≤ (4:ℝ)^(4-ell)*upper :=
    hh.trans (mul_le_mul_of_nonneg_left (hupper c) (by positivity))
  exact (le_div_iff₀ hdpos).mpr (by simpa only [mul_comm] using hbound)

end NativeActualOffsetCellCaps
