import Theorems.Thm_StickyKakeya4_native_common_phi_grid
import Theorems.Thm_StickyKakeya4_native_fixed_offset_coherence

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeCommonPhiSource
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentGeometry NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu
open NativeHeightMetricMenu NativeTranslatedGrainHeightOverlap NativeIncidentAffineAnchorGeometry
open NativeGrainQuotientInjection NativeGrainQuotientBins NativeHorizontalGrainSlice
open NativeReferenceXYGridLinear NativeReferenceXYGridAngularCap NativeCommonPhiMetric NativeCommonPhiGrid
open NativeNormalizedOffsetField NativeFixedOffsetCoherence
open scoped BigOperators Matrix.Norms.Elementwise

/-- The exact source error/scale term is retained. It can be paid together
with the metric loss, without assuming the old affine error≤rho. -/
def cellThickness (error metric rho : ℝ) : ℝ := 7*error/rho+64*metric+9/4

lemma cellThickness_nonneg {error metric rho : ℝ} (he : 0 ≤ error)
    (hm : 0 ≤ metric) (hrho : 0 < rho) : 0 ≤ cellThickness error metric rho := by
  unfold cellThickness
  positivity

lemma cellThickness_le {error metric rho : ℝ} (hrho : 0 < rho) (he : error ≤ rho) :
    cellThickness error metric rho ≤ 64*metric+10 := by
  have hh := (div_le_one hrho).mpr he
  unfold cellThickness
  have hi : 7*error/rho=7*(error/rho) := by ring
  rw [hi]
  linarith only [hh]

/-- The existing full angularCell has exactly the rho/8 mesh. -/
lemma angularCell_readback {n : ℕ} (D : FiniteScaleSource n) (N M : ℕ)
    (hM : 0 < M) (p : Parent) (i : Fin n) :
    angularCell D N M p i=angle ((64/(M:ℝ))/8) (localHorizontalSlope D N p i) := by
  funext j
  simp only [angularCell,angle,localHorizontalSlope,ActualSlopeSource.heightPoint_castSucc]
  congr 1
  have hMr : (M:ℝ)≠0 := by exact_mod_cast hM.ne'
  field_simp
  ring

/-- The horizontal embedding preserves the full local slope distance. -/
lemma localSlope_distance {n : ℕ} (D : FiniteScaleSource n) (N : ℕ)
    (p : Parent) (i j : Fin n) :
    ‖localHorizontalSlope D N p i-localHorizontalSlope D N p j‖=
      ‖localSlope D N p i-localSlope D N p j‖ := by
  have hs : ‖localHorizontalSlope D N p i-localHorizontalSlope D N p j‖^2=
      ‖localSlope D N p i-localSlope D N p j‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_castSucc]
    simp only [PiLp.sub_apply,localHorizontalSlope,ActualSlopeSource.heightPoint_castSucc,
      ActualSlopeSource.heightPoint_last,sub_self,zero_pow (by decide : 2≠0),add_zero]
  nlinarith only [hs,norm_nonneg (localHorizontalSlope D N p i-localHorizontalSlope D N p j),
    norm_nonneg (localSlope D N p i-localSlope D N p j)]

/-- The existing raw-height modulus and selected offset coherence freeze
one actual physical cell around one of its ORIGINAL retained edges. -/
theorem coherent_cell_residual {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m M : ℕ) (hM : 0 < M) (p : Parent) (I : Finset (Fin n × Index))
    (hp : ∀z∈I,parentLabel D a (2^m) z.1=p) (cell : Index)
    (hcell : ∀z∈I,physicalCell D a (2^m) M p z.2=cell)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (ell : ℕ)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin (4-ell))) (error metric shift : ℝ)
    (_he : 0 ≤ error) (hmetric : 0 ≤ metric) (hwindow : meshWidth m/512 ≤ 64/(M:ℝ))
    (hF : ∀k∈I.image Prod.snd,‖F (rawHeight D m k)‖ ≤ (1/4:ℝ))
    (Hmetric : ∀z∈I,∀w∈I,‖F (rawHeight D m z.2)-F (rawHeight D m w.2)‖ ≤
      metric*|chartHeightCoordinate m shift (rawHeight D m z.2)-
        chartHeightCoordinate m shift (rawHeight D m w.2)|)
    (hres : ∀z∈I,‖quotientMap P hP ell hell hell4 hd (F (rawHeight D m z.2))
      (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error)
    (hoff : ∀z∈I,∀w∈I,‖xi z.2-xi w.2‖ ≤ 3*offsetMesh error metric M)
    (z0 : Fin n × Index) (hz0 : z0∈I) :
    let rho := 64/(M:ℝ)
    ∀z∈I,‖quotientMap P hP ell hell hell4 hd (F (rawHeight D m z0.2))
      (localHorizontalSlope D (2^m) p z.1)-xi z0.2‖ ≤ cellThickness error metric rho*rho := by
  intro rho z hz
  have Hvar := raw_field_variation D a (2^m) M m hM p I cell hcell F metric shift hmetric Hmetric
  have hvar : ‖F (rawHeight D m z.2)-F (rawHeight D m z0.2)‖ ≤ 2*metric*rho :=
    (Hvar z.2 (mem_image_of_mem _ hz) z0.2 (mem_image_of_mem _ hz0)).trans
      (window_variation_le_twice hmetric hwindow)
  have hh := frozen_residual P hP ell hell hell4 hd (F (rawHeight D m z.2))
    (F (rawHeight D m z0.2)) (hF _ (mem_image_of_mem _ hz0))
    (localHorizontalSlope D (2^m) p z.1) (localHorizontalSlope_norm D a (2^m) p z.1 (hp z hz))
    (xi z.2) (xi z0.2) error (2*metric*rho) (3*offsetMesh error metric M)
    (hres z hz) hvar (hoff z hz z0 hz0)
  have hMr : (M:ℝ)≠0 := by exact_mod_cast hM.ne'
  have heq : error+8*(2*metric*rho)+3*offsetMesh error metric M=
      cellThickness error metric rho*rho := by
    dsimp [rho,offsetMesh,cellThickness]
    field_simp
    ring
  exact hh.trans_eq heq

/-- Actual same-source full-angular/tangent-grid transfer in one physical
cell. It retains every original index and every error/mesh factor. -/
theorem coherent_cell_projection {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m M : ℕ) (hM : 0 < M) (p : Parent) (I : Finset (Fin n × Index))
    (hp : ∀z∈I,parentLabel D a (2^m) z.1=p) (cell : Index)
    (hcell : ∀z∈I,physicalCell D a (2^m) M p z.2=cell)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (ell : ℕ)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin (4-ell))) (error metric shift : ℝ)
    (he : 0 ≤ error) (hmetric : 0 ≤ metric) (hwindow : meshWidth m/512 ≤ 64/(M:ℝ))
    (hF : ∀k∈I.image Prod.snd,‖F (rawHeight D m k)‖ ≤ (1/4:ℝ))
    (Hmetric : ∀z∈I,∀w∈I,‖F (rawHeight D m z.2)-F (rawHeight D m w.2)‖ ≤
      metric*|chartHeightCoordinate m shift (rawHeight D m z.2)-
        chartHeightCoordinate m shift (rawHeight D m w.2)|)
    (hres : ∀z∈I,‖quotientMap P hP ell hell hell4 hd (F (rawHeight D m z.2))
      (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error)
    (hoff : ∀z∈I,∀w∈I,‖xi z.2-xi w.2‖ ≤ 3*offsetMesh error metric M)
    (z0 : Fin n × Index) (hz0 : z0∈I) :
    let rho := 64/(M:ℝ)
    let E := cellThickness error metric rho
    let Phi := fun z : Fin n × Index => label rho (tangentCoordinates P ell hd (localHorizontalSlope D (2^m) p z.1))
    let C := (129:ℝ)^3*(2*E+2)^(4-ell)
    (∀v : Fin (ell-1) → ℤ,
      (((I.filter (fun z => Phi z=v)).image (fun z => angularCell D (2^m) M p z.1)).card:ℝ) ≤ C) ∧
    (∀v : Fin 3 → ℤ,
      ((I.filter (fun z => angularCell D (2^m) M p z.1=v)).image Phi).card ≤ 3^(ell-1)) ∧
    (((I.image (fun z => angularCell D (2^m) M p z.1)).card:ℝ) ≤ C*(I.image Phi).card) ∧
    ∀sigma : ℝ,rho ≤ sigma → ∀x∈I,∀y∈I,∀center : EuclideanSpace ℝ (Fin (ell-1)),
      ‖tangentCoordinates P ell hd (localHorizontalSlope D (2^m) p x.1)-center‖ ≤ sigma →
      ‖tangentCoordinates P ell hd (localHorizontalSlope D (2^m) p y.1)-center‖ ≤ sigma →
      ‖localSlope D (2^m) p x.1-localSlope D (2^m) p y.1‖ ≤ (4+2*E)*sigma := by
  intro rho E Phi C
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hE : 0 ≤ E := cellThickness_nonneg he hmetric hrho
  have hfr := coherent_cell_residual D a m M hM p I hp cell hcell P hP ell hell hell4 hd
    F xi error metric shift he hmetric hwindow hF Hmetric hres hoff z0 hz0
  have hF0 := hF _ (mem_image_of_mem Prod.snd hz0)
  have hhoriz : ∀z∈I,localHorizontalSlope D (2^m) p z.1∈heightKernel :=
    fun z _ => localHorizontalSlope_mem_heightKernel D (2^m) p z.1
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    have hh := inverse_projected_fiber_cap I (fun z => localHorizontalSlope D (2^m) p z.1)
      P hP ell hell hell4 hd (F (rawHeight D m z0.2)) hF0 (xi z0.2) hrho hE hhoriz hfr v
    simpa only [angularCell_readback D (2^m) M hM p] using hh
  · intro v
    have hh := forward_projected_fiber_cap I (fun z => localHorizontalSlope D (2^m) p z.1)
      P ell hd hrho hhoriz v
    simpa only [angularCell_readback D (2^m) M hM p] using hh
  · have hh := angular_card_le_projected I (fun z => localHorizontalSlope D (2^m) p z.1)
      P hP ell hell hell4 hd (F (rawHeight D m z0.2)) hF0 (xi z0.2) hrho hE hhoriz hfr
    simpa only [angularCell_readback D (2^m) M hM p] using hh
  · intro sigma hrs x hx y hy center hbx hby
    rw [←localSlope_distance]
    exact tangent_ball_pair_inverse P hP ell hell hell4 hd (F (rawHeight D m z0.2)) hF0
      (xi z0.2) _ _ (hhoriz x hx) (hhoriz y hy) rho sigma E hE hrs
      (hfr x hx) (hfr y hy) center hbx hby

end NativeCommonPhiSource
