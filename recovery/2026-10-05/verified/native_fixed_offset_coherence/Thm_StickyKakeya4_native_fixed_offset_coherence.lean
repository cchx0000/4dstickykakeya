import Theorems.Thm_StickyKakeya4_native_actual_offset_cell_caps

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeFixedOffsetCoherence
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu NativeHeightMetricMenu
open NativeTranslatedGrainHeightOverlap NativeIncidentAffineAnchorGeometry NativeGrainQuotientInjection
open NativeGrainQuotientBins NativeReferenceXYGridLinear NativeHorizontalGrainSlice
open NativeActualOffsetCellCaps NativeFinitePointCoherence NativeNormalizedOffsetTime
open scoped BigOperators Matrix.Norms.Elementwise

def offsetMesh (error metric : ℝ) (M : ℕ) : ℝ := 2*error+48/(M:ℝ)+16*metric*(64/(M:ℝ))

lemma offsetMesh_pos {error metric : ℝ} (he : 0 ≤ error) (hmetric : 0 ≤ metric)
    (M : ℕ) (hM : 0 < M) : 0 < offsetMesh error metric M := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  unfold offsetMesh
  positivity

lemma same_offset_norm {ell : ℕ} (hell : 1 ≤ ell) {H : ℝ} (hH : 0 < H)
    (x y : EuclideanSpace ℝ (Fin (4-ell))) (heq : label H x=label H y) : ‖x-y‖ ≤ 3*H := by
  have hcoord (j : Fin (4-ell)) : |x j-y j| ≤ H :=
    same_floor_distance hH (congrFun heq j)
  have hsum := sum_le_sum (fun j (_hj : j∈(univ:Finset (Fin (4-ell)))) => hcoord j)
  have hdim : ((4-ell:ℕ):ℝ) ≤ 3 := by exact_mod_cast (show 4-ell ≤ 3 by omega)
  calc
    _ ≤ ∑j : Fin (4-ell),|x j-y j| := by simpa only [PiLp.sub_apply] using euclidean_norm_le_sum (x-y)
    _ ≤ ((4-ell:ℕ):ℝ)*H := by simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using hsum
    _ ≤ _ := mul_le_mul_of_nonneg_right hdim hH.le

/-- Actual fixed-menu coherence. The same F and xi are used in every round.
Selection acts on the ORIGINAL point support with its original edge weights,
then lifts back every original incidence at each retained point. -/
theorem select_fixed_offset_menu {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (S : Finset (Fin n × Index)) (hS : S.Nonempty)
    (hp : ∀z∈S,parentLabel D a (2^m) z.1=p)
    (P0 : Submodule ℝ E4) (hP0 : P0≤heightKernel) (ell : ℕ)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P0=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin (4-ell))) (error metric shift : ℝ)
    (he : 0 ≤ error) (hmetric : 0 ≤ metric)
    (M : Fin K → ℕ) (hM : ∀j,0 < M j) (hwindow : ∀j,meshWidth m/512 ≤ 64/(M j:ℝ))
    (d upper : Fin K → ℝ) (hdpos : ∀j,0 < d j)
    (hF : ∀k∈S.image Prod.snd,‖F (rawHeight D m k)‖ ≤ (1/4:ℝ))
    (Hmetric : ∀z∈S,∀w∈S,‖F (rawHeight D m z.2)-F (rawHeight D m w.2)‖ ≤
      metric*|chartHeightCoordinate m shift (rawHeight D m z.2)-
        chartHeightCoordinate m shift (rawHeight D m w.2)|)
    (hres : ∀z∈S,‖quotientMap P0 hP0 ell hell hell4 hd (F (rawHeight D m z.2))
      (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error)
    (hlower : ∀j k,k∈S.image Prod.snd → d j ≤
      (((S.filter (fun z => z.2=k)).image (fun z => angularCell D (2^m) (M j) p z.1)).card:ℝ))
    (hupper : ∀j c,((angularMenu D a m (M j) p S c).card:ℝ) ≤ upper j) :
    ∃P⊆S.image Prod.snd,let T := NativeFinitePointCoherence.lift S Prod.snd P
      T.Nonempty ∧ S.card ≤ (∏j,⌈((4:ℝ)^(4-ell)*upper j)/d j⌉₊)*T.card ∧
      (∀j z w,z∈T → w∈T → physicalCell D a (2^m) (M j) p z.2=physicalCell D a (2^m) (M j) p w.2 →
        label (offsetMesh error metric (M j)) (xi z.2)=label (offsetMesh error metric (M j)) (xi w.2) ∧
        ‖xi z.2-xi w.2‖ ≤ 3*offsetMesh error metric (M j)) ∧
      (∀k∈P,T.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) ∧
      (∀j k,k∈P → d j ≤ (((T.filter (fun z => z.2=k)).image
        (fun z => angularCell D (2^m) (M j) p z.1)).card:ℝ)) := by
  have hcap (j : Fin K) := actual_cell_offset_cap D a m (M j) (hM j) p S hp P0 hP0 ell hell hell4 hd
    F xi error metric shift (d j) (upper j) he hmetric (hwindow j) (hdpos j) hF Hmetric hres
    (hlower j) (hupper j)
  obtain ⟨P,hP,hT,hCost,hCompat,hFiber⟩ := select_original_point_fibers S hS Prod.snd K
    (fun j => physicalCell D a (2^m) (M j) p)
    (fun j k => label (offsetMesh error metric (M j)) (xi k))
    (fun j => ((4:ℝ)^(4-ell)*upper j)/d j) hcap
  refine ⟨P,hP,hT,hCost,?_,hFiber,?_⟩
  · intro j z w hz hw hcell
    have hh := hCompat j z w hz hw hcell
    exact ⟨hh,same_offset_norm hell (offsetMesh_pos he hmetric (M j) (hM j)) _ _ hh⟩
  · intro j k hk
    rw [hFiber k hk]
    exact hlower j k (hP hk)

end NativeFixedOffsetCoherence
