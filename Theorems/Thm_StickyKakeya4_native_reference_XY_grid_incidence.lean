import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_field
import Theorems.Thm_StickyKakeya4_native_original_parent_physical_data
import Theorems.Thm_StickyKakeya4_native_actual_squared_grain_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeReferenceXYGridIncidence
open Classical Finset StickyKakeya4 NativeReferenceXYGridLinear NativeReferenceXYGridPoints
open NativeHorizontalGrainSlice NativeGrainQuotientInjection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeOriginalParentSelection NativeCubicalIncidenceCounts
open NativeOriginalParentPhysicalData NativeSquaredGrainQueries
open scoped Matrix.Norms.Elementwise

/-- A literal original shading edge gives incidence at the SAME rawPoint
used by pxy, against its unchanged parent-normalized ORIGINAL marked line.
The exact original thickness and phase-rounding terms are both retained. -/
theorem original_edge_rawPoint {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m : ℕ) (hm : 6 ≤ m) (p : Parent) (i : Fin n) (k : Index)
    (hk : (i,k)∈incidences cells) (hi : parentLabel D a (2^m) i=p) :
    rawPoint D a m p k∈markedUnitTube (NativeLocalParentGeometry.line D a (2^m) p i)
      ((((2^m:ℕ):ℝ)*D.thickness)/64+128*mu m) := by
  have hcell := original_cell_in_tube h cells hcells hk
  have hdelta : 2*mesh D=D.thickness := by unfold mesh; ring
  rw [hdelta] at hcell
  have hlocal := NativeLocalParentPhysicalMap.original_tube_maps h ha (2^m) (by positivity) p i hi
    (Set.mem_image_of_mem (NativeLocalParentPhysicalMap.physicalMap D a (2^m) p) hcell)
  have hround := physical_rounding h m hm p i hi k
  change Metric.infDist (oldPoint D a m p k) (unitFront {NativeLocalParentGeometry.line D a (2^m) p i}) ≤
    (((2^m:ℕ):ℝ)*D.thickness)/64 at hlocal
  have htri := Metric.infDist_le_infDist_add_dist
    (x:=rawPoint D a m p k) (y:=oldPoint D a m p k)
    (s:=unitFront {NativeLocalParentGeometry.line D a (2^m) p i})
  change Metric.infDist _ _ ≤ _
  linarith

/-- The genuine squared-grain scale gives the explicit3Delta tube error.
This removes a point-incidence premise using the original shading itself. -/
theorem original_edge_rawPoint_three_rho {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m : ℕ) (hm : 6 ≤ m) (hscale : D.thickness ≤ (rho m)^2)
    (p : Parent) (i : Fin n) (k : Index) (hk : (i,k)∈incidences cells)
    (hi : parentLabel D a (2^m) i=p) :
    rawPoint D a m p k∈markedUnitTube (NativeLocalParentGeometry.line D a (2^m) p i) (3*rho m) := by
  have hh := original_edge_rawPoint h cells hcells ha m hm p i k hk hi
  have hs := mul_le_mul_of_nonneg_left hscale (by positivity : (0:ℝ) ≤ ((2^m:ℕ):ℝ))
  have he : (((2^m:ℕ):ℝ)*(rho m)^2)/64=rho m := by
    unfold rho
    have hN : (((2^m:ℕ):ℝ))≠0 := by positivity
    field_simp
  change Metric.infDist _ _ ≤ _ at hh ⊢
  unfold mu at hh
  have hscaled : (((2^m:ℕ):ℝ)*D.thickness)/64 ≤ rho m := by
    exact (div_le_div_of_nonneg_right hs (by norm_num)).trans_eq he
  linarith

/-- The scale premise is itself derived from the actual source dyadic level
and the certified terminal phase depth. -/
theorem dyadic_original_edge_rawPoint {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level : ℕ) (hm : 6 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : phaseDepth m ≤ level)
    (p : Parent) (i : Fin n) (k : Index) (hk : (i,k)∈incidences cells)
    (hi : parentLabel D a (2^m) i=p) :
    rawPoint D a m p k∈markedUnitTube (NativeLocalParentGeometry.line D a (2^m) p i) (3*rho m) :=
  original_edge_rawPoint_three_rho h cells hcells ha m hm
    (NativeActualSquaredGrainSelection.thickness_le_squared_scale m level hm hdy hf) p i k hk hi

/-- Arbitrary later original-incidence cuts, including H3, keep this exact
point-to-original-tube incidence without an added incidence certificate. -/
theorem retained_original_rawPoint_incidence {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level : ℕ) (hm : 6 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : phaseDepth m ≤ level)
    (p : Parent) (H3 : Finset (Fin n × Index)) (h3 : H3⊆incidences cells)
    (hparent : ∀z∈H3,parentLabel D a (2^m) z.1=p) :
    ∀z∈H3,rawPoint D a m p z.2∈markedUnitTube
      (NativeLocalParentGeometry.line D a (2^m) p z.1) (3*rho m) := by
  intro z hz
  exact dyadic_original_edge_rawPoint h cells hcells ha m level hm hdy hf p z.1 z.2 (h3 hz) (hparent z hz)

/-- The fixed UNQUOTIENTED frame. It is a linear coordinate change and
contains no height-dependent F. -/
def frame (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) :
    E4 →ₗ[ℝ] (EuclideanSpace ℝ (Fin (ell-1)) × (EuclideanSpace ℝ (Fin (4-ell)) × ℝ)) :=
  (tangentCoordinates P ell hd).prod
    ((normalCoordinates P hP ell hell hell4 hd).prod (EuclideanSpace.projₗ (3:Fin 4)))

/-- Every actual marked straight line stays affine in the fixed unquotiented
coordinates. The height-varying quotient is never used to map a tube. -/
theorem frame_line_formula (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (line : MarkedLine) (t : ℝ) :
    frame P hP ell hell hell4 hd (rawFrontParam (line,t))=
      frame P hP ell hell hell4 hd (offset line)+(mark line+t) • frame P hP ell hell hell4 hd (direction line) := by
  simp only [rawFrontParam,map_add,map_smul]

lemma frame_dist_le (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (x y : E4) :
    dist (frame P hP ell hell hell4 hd x) (frame P hP ell hell hell4 hd y) ≤ dist x y := by
  rw [dist_eq_norm,←map_sub,dist_eq_norm]
  change max ‖tangentCoordinates P ell hd (x-y)‖
    (max ‖normalCoordinates P hP ell hell hell4 hd (x-y)‖ ‖(x-y) (3:Fin 4)‖) ≤ ‖x-y‖
  exact max_le (tangent_norm_le P ell hd _) (max_le (normal_norm_le P hP ell hell hell4 hd _)
    (PiLp.norm_apply_le (x-y) (3:Fin 4)))

lemma frame_infDist_le (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (x : E4) (W : Set E4) (hW : W.Nonempty) :
    Metric.infDist (frame P hP ell hell hell4 hd x) (frame P hP ell hell hell4 hd '' W) ≤ Metric.infDist x W := by
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨y,hy,hxy⟩ := (Metric.infDist_lt_iff hW).mp (lt_add_of_pos_right (Metric.infDist x W) heps)
  exact (Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem _ hy)).trans
    ((frame_dist_le P hP ell hell hell4 hd x y).trans hxy.le)

/-- Quotient coordinates only PARAMETRIZE points: adding F(t)X back recovers
the actual unquotiented normal coordinate exactly, at every chosen height. -/
lemma point_quotient_reconstruction (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (t : ℤ) (x : E4) :
    normalCoordinates P hP ell hell hell4 hd x=
      quotientMap P hP ell hell hell4 hd (F t) x+(F t).toEuclideanLin (tangentCoordinates P ell hd x) := by
  change _=(_- (F t).toEuclideanLin (tangentCoordinates P ell hd x))+(F t).toEuclideanLin (tangentCoordinates P ell hd x)
  exact (sub_add_cancel _ _).symm

/-- The fixed full frame does not collapse a nontrivial straight line. -/
lemma frame_injective (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) :
    Function.Injective (frame P hP ell hell hell4 hd) := by
  intro x y hxy
  have ht : tangentCoordinates P ell hd x=tangentCoordinates P ell hd y := congrArg Prod.fst hxy
  have hn : normalCoordinates P hP ell hell hell4 hd x=normalCoordinates P hP ell hell hell4 hd y :=
    congrArg (fun z => z.2.1) hxy
  have hh : x (3:Fin 4)=y (3:Fin 4) := congrArg (fun z => z.2.2) hxy
  have hzero : quotientMap P hP ell hell hell4 hd (0:Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)=
      normalCoordinates P hP ell hell hell4 hd := by simp [quotientMap]
  have hi := inverse_norm P hP ell hell hell4 hd (0:Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (by norm_num) (x-y)
  rw [hzero,map_sub,map_sub,ht,hn] at hi
  have hz : ‖x-y‖ ≤ 0 := by simpa only [sub_self,norm_zero,mul_zero,zero_add,PiLp.sub_apply,hh,abs_zero] using hi
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

/-- The original-incidence conclusion also holds in the fixed linear frame,
against the affine image of that SAME unchanged original local unit front. -/
theorem framed_retained_original_incidence {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,D.shading i=wzCellShading (mesh D) cells i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level : ℕ) (hm : 6 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : phaseDepth m ≤ level)
    (p : Parent) (H3 : Finset (Fin n × Index)) (h3 : H3⊆incidences cells)
    (hparent : ∀z∈H3,parentLabel D a (2^m) z.1=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) :
    ∀z∈H3,Metric.infDist (frame P hP ell hell hell4 hd (rawPoint D a m p z.2))
      (frame P hP ell hell hell4 hd '' unitFront {NativeLocalParentGeometry.line D a (2^m) p z.1}) ≤ 3*rho m := by
  intro z hz
  have hi := retained_original_rawPoint_incidence h cells hcells ha m level hm hdy hf p H3 h3 hparent z hz
  have hfront : (unitFront {NativeLocalParentGeometry.line D a (2^m) p z.1}).Nonempty :=
    ⟨rawFrontParam (NativeLocalParentGeometry.line D a (2^m) p z.1,0),
      rawFrontParam_mem_unitFront_singleton _ (by constructor <;> norm_num)⟩
  exact (frame_infDist_le P hP ell hell hell4 hd _ _ hfront).trans hi

end NativeReferenceXYGridIncidence
