import Theorems.Thm_StickyKakeya4_native_dense_source_coarse_family
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeDyadicCoarseNormalization
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeSourceCoarseReadback NativeDenseSourceCoarseFamily
open NativeCoarseOriginalIncidences NativeCoarseOriginalGeometry
open scoped ENNReal
variable {T : Type*}
/-- Changing the common normalization scales the SAME physical coarse point. -/
theorem coordinates_between_scales (P : PhysicalRescalingIncidenceTransfer.Data T)
    (c : ShearBinFibers.Index) {r R : ℝ} (hr : 0 < r) :
    height P R c=(r/R)*height P r c ∧
      ∀ j, (coordinates P R c).1 j=(r/R)*(coordinates P r c).1 j := by
  constructor
  · rw [coordinates_scale_height P R c,coordinates_scale_height P r c]
    calc
      _ = ((ShearBinFibers.oldCenter P.σ c).2*(r/r))/R := by rw [div_self hr.ne',mul_one]
      _ = _ := by ring
  · intro j
    rw [coordinates_scale_space P R c j,coordinates_scale_space P r c j]
    calc
      _ = ((ShearBinFibers.oldCenter P.σ c).1 j*(r/r))/R := by rw [div_self hr.ne',mul_one]
      _ = _ := by ring
/-- Unit-box bounds survive a larger common normalization on original labels. -/
theorem larger_normalization_box (P : PhysicalRescalingIncidenceTransfer.Data T)
    (c : ShearBinFibers.Index) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (ht : |height P r c| ≤ 1) (hx : ∀ j, |(coordinates P r c).1 j| ≤ 1) :
    |height P R c| ≤ 1 ∧ ∀ j, |(coordinates P R c).1 j| ≤ 1 := by
  have hR : 0 < R := hr.trans_le hrR
  have hratio : 0 ≤ r/R := div_nonneg hr.le hR.le
  have hratio1 : r/R ≤ 1 := (div_le_iff₀ hR).mpr (by simpa using hrR)
  have hscale := coordinates_between_scales P c hr (R := R)
  constructor
  · rw [hscale.1,abs_mul,abs_of_nonneg hratio]
    exact (mul_le_mul hratio1 ht (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  · intro j
    rw [hscale.2 j,abs_mul,abs_of_nonneg hratio]
    exact (mul_le_mul hratio1 (hx j) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
/-- Slopes stay unchanged; offsets and residuals scale with the SAME point
 and time coordinates, so the error coefficient relative to mesh is unchanged. -/
theorem larger_normalization_residual (P : PhysicalRescalingIncidenceTransfer.Data T)
    (c : ShearBinFibers.Index) (tube : T) (j : Fin 3) {r R C : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hres : |(coordinates P r c).1 j-P.offset tube j/r-P.slope tube j*height P r c| ≤ C*(P.σ/r)) :
    |(coordinates P R c).1 j-P.offset tube j/R-P.slope tube j*height P R c| ≤ C*(P.σ/R) := by
  have hscale := coordinates_between_scales P c hr (R := R)
  have hoff : P.offset tube j/R=(r/R)*(P.offset tube j/r) := by
    calc
      _ = (P.offset tube j*(r/r))/R := by rw [div_self hr.ne',mul_one]
      _ = _ := by ring
  have hid : (coordinates P R c).1 j-P.offset tube j/R-P.slope tube j*height P R c=
      (r/R)*((coordinates P r c).1 j-P.offset tube j/r-P.slope tube j*height P r c) := by
    rw [hscale.1,hscale.2 j,hoff]
    ring
  rw [hid,abs_mul,abs_of_nonneg (div_nonneg hr.le hR.le)]
  calc
    _ ≤ (r/R)*(C*(P.σ/r)) := mul_le_mul_of_nonneg_left hres (div_nonneg hr.le hR.le)
    _ = C*(P.σ/R) := by field_simp
lemma native_dyadic_scale {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) : (data D cells a N p).σ/32=(N:ℝ)*D.thickness/256 := by
  dsimp [data,PhysicalRescalingIncidenceTransfer.Data.σ,NativeOriginalParentSelection.mesh]
  ring
/-- The normalized mesh is exactly dyadic when the original scale and
 parent factor are dyadic; the index condition is explicit. -/
theorem dyadic_mesh_readback (m n : ℕ) (hm : m ≤ n+8) :
    ((2^m:ℕ):ℝ)*((2:ℝ)^n)⁻¹/256=((2:ℝ)^(n+8-m))⁻¹ := by
  norm_num only [Nat.cast_pow,Nat.cast_ofNat]
  have hpow : ((2:ℝ)^n)*256=((2:ℝ)^m)*((2:ℝ)^(n+8-m)) := by
    calc
      _ = (2:ℝ)^(n+8) := by rw [pow_add]; norm_num
      _ = (2:ℝ)^(m+(n+8-m)) := by congr 1; omega
      _ = _ := pow_add _ _ _
  calc
    _ = ((2:ℝ)^m)/(((2:ℝ)^n)*256) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = ((2:ℝ)^m)/(((2:ℝ)^m)*((2:ℝ)^(n+8-m))) := by rw [hpow]
    _ = _ := by field_simp
/-- Dyadic normalization of the ACTUAL native original coarse family. Its
 bins and tube labels are identical to the frozen physical construction. -/
theorem exists_actual_dyadic_coarse_family {n : ℕ} {D : FiniteScaleSource n} {eta beta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i,D.shading i=wzCellShading (NativeOriginalParentSelection.mesh D) cells i)
    (hne : (NativeCubicalIncidenceCounts.incidences cells).Nonempty) (hexp : 0 ≤ eta+beta)
    (htube : ∀ i,(ENNReal.ofReal D.thickness).rpow (3+beta) ≤
      MeasureTheory.volume (markedUnitTube (D.line i) D.thickness))
    (N : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*(D.thickness/8) ≤ 1)
    {L d : ℕ} (hL : 0 < L) (radii timeDiv : Fin d → ℕ) (offsetMesh slopeMesh : Fin d → ℝ) :
    ∃ a : ℝ, ∃ p ∈ parents D a N, ∃ E0 : Finset (Fin n × Index),
      E0 ⊆ NativeCubicalIncidenceCounts.incidences cells ∧
      let P := data D cells a N p
      let I := originalFamily P (shift D a) E0
      let deltaNew := (N:ℝ)*D.thickness/256
      P.Hypotheses ∧ I.Nonempty ∧
      TwoTubePathCollisionCount.tubes I=E0.image Prod.fst ∧ E0.card ≤ N*I.card ∧
      (D.thickness^(eta+beta)/(32*(NativeSelectedPhysicalMultiplicity.refinementLoss d L:ℝ)))*
        (TwoTubePathCollisionCount.tubes I).card ≤ deltaNew*(I.card:ℝ) ∧
      ∀ e ∈ I, |height P 32 e.1| ≤ 1 ∧
        (∀ j, |(coordinates P 32 e.1).1 j| ≤ 1) ∧
        (∀ j, |(coordinates P 32 e.1).1 j-P.offset e.2 j/32-
          P.slope e.2 j*height P 32 e.1| ≤ 13*deltaNew) := by
  obtain ⟨a,p,hp,E0,hE0,hP,hI,hT,hCap,hDen,hGeo⟩ := exists_actual_original_coarse_family
    h cells hcells hne hexp htube N hN hscale hL radii timeDiv offsetMesh slopeMesh
  let P := data D cells a N p
  let I := originalFamily P (shift D a) E0
  have hR : normalization P=28 := (native_scale_readback D cells a N p).2.1
  have hOld : P.σ/normalization P=(N:ℝ)*D.thickness/224 := (native_scale_readback D cells a N p).2.2
  have hNew : P.σ/32=(N:ℝ)*D.thickness/256 := native_dyadic_scale D cells a N p
  refine ⟨a,p,hp,E0,hE0,hP,hI,hT,hCap,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hDen (by norm_num : (0:ℝ) ≤ 28/32)
    have hleft : (28/32:ℝ)*(D.thickness^(eta+beta)/(28*(NativeSelectedPhysicalMultiplicity.refinementLoss d L:ℝ))*
        (TwoTubePathCollisionCount.tubes I).card)=
        D.thickness^(eta+beta)/(32*(NativeSelectedPhysicalMultiplicity.refinementLoss d L:ℝ))*
          (TwoTubePathCollisionCount.tubes I).card := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    have hright : (28/32:ℝ)*(((N:ℝ)*D.thickness/224)*(I.card:ℝ))=
        ((N:ℝ)*D.thickness/256)*(I.card:ℝ) := by ring
    rw [hleft,hright] at hh
    exact hh
  · intro e he
    obtain ⟨ht,hx,hr⟩ := hGeo e he
    have hbox := larger_normalization_box P e.1 (normalization_pos P)
      (show normalization P ≤ 32 by rw [hR]; norm_num) ht hx
    refine ⟨hbox.1,hbox.2,?_⟩
    intro j
    have hres : |(coordinates P (normalization P) e.1).1 j-P.offset e.2 j/normalization P-
        P.slope e.2 j*height P (normalization P) e.1| ≤ 13*(P.σ/normalization P) := by
      rw [hOld]
      exact hr j
    have hh := larger_normalization_residual P e.1 e.2 j (normalization_pos P) (by norm_num : (0:ℝ)<32) hres
    rwa [hNew] at hh
end NativeDyadicCoarseNormalization
