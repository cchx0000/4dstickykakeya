import Theorems.Thm_StickyKakeya4_native_finite_point_coherence
import Theorems.Thm_StickyKakeya4_native_height_metric_menu
import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu
import Theorems.Thm_StickyKakeya4_native_matrix_height_interface

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
noncomputable section

namespace NativePhysicalMatrixPalette
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeNormalizedCellRelativeMenu NativeHeightMetricMenu NativeSpatialAngularGeometry
open NativeFinitePointCoherence NativeMatrixHeightInterface
open NativeLocalParentPhysicalMap NativeOriginalCellChartGeometry
open NativeMatrixHeightWholePoint
open scoped BigOperators Matrix.Norms.Elementwise

/-- Only the literal physical HEIGHT coordinate is needed for the source
raw-time window. No equality of horizontal cell coordinates is assumed. -/
lemma physical_height_chart_window {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N M m : ℕ) (hM : 0 < M) (p : Parent) (k l : Index) (shift : ℝ)
    (hcell : physicalCell D a N M p k (3:Fin 4)=physicalCell D a N M p l (3:Fin 4)) :
    |chartHeightCoordinate m shift (spatialLabel D (2^m) k (3:Fin 4))-chartHeightCoordinate m shift (spatialLabel D (2^m) l (3:Fin 4))| ≤
      64/(M:ℝ)+meshWidth m/512 := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  change ⌊physicalPoint D a N p k (3:Fin 4)/(64/(M:ℝ))⌋=
    ⌊physicalPoint D a N p l (3:Fin 4)/(64/(M:ℝ))⌋ at hcell
  have ht : |physicalPoint D a N p k (3:Fin 4)-physicalPoint D a N p l (3:Fin 4)| ≤
      64/(M:ℝ) := by
    apply le_of_lt
    apply same_height_cell_close (shift:=0) (by positivity : (0:ℝ)<64/(M:ℝ))
    simpa only [heightCell,sub_zero] using hcell
  change |physicalMap D a N p (cellCenter (mesh D) k) (3:Fin 4)-
    physicalMap D a N p (cellCenter (mesh D) l) (3:Fin 4)| ≤ 64/(M:ℝ) at ht
  rw [NativeAnisotropicShortRowGeometry.chart_height_sub D a N p
    (cellCenter (mesh D) l) (cellCenter (mesh D) k),abs_div] at ht
  rw [abs_of_pos (by norm_num : (0:ℝ)<512)] at ht
  have ht' := (div_le_iff₀ (by norm_num : (0:ℝ)<512)).mp ht
  have quantized (x y : ℝ) :
      |meshWidth m*(⌊x/meshWidth m⌋:ℝ)-meshWidth m*(⌊y/meshWidth m⌋:ℝ)| ≤
        |x-y|+meshWidth m := by
    have hxlo := (le_div_iff₀ (meshWidth_pos m)).mp (Int.floor_le (x/meshWidth m))
    have hxhi := (div_lt_iff₀ (meshWidth_pos m)).mp (Int.lt_floor_add_one (x/meshWidth m))
    have hylo := (le_div_iff₀ (meshWidth_pos m)).mp (Int.floor_le (y/meshWidth m))
    have hyhi := (div_lt_iff₀ (meshWidth_pos m)).mp (Int.lt_floor_add_one (y/meshWidth m))
    have hdlo := neg_abs_le (x-y)
    have hdhi := le_abs_self (x-y)
    exact abs_le.mpr ⟨by linarith only [hxhi,hylo,hdlo],by linarith only [hxlo,hyhi,hdhi]⟩
  have hraw := quantized
    (cellCenter (mesh D) k (3:Fin 4)) (cellCenter (mesh D) l (3:Fin 4))
  have hbound : |rawHeightCoordinate m (spatialLabel D (2^m) k (3:Fin 4))-rawHeightCoordinate m (spatialLabel D (2^m) l (3:Fin 4))| ≤
      512*(64/(M:ℝ))+meshWidth m := by
    change |meshWidth m*(⌊cellCenter (mesh D) k (3:Fin 4)/meshWidth m⌋:ℝ)-
      meshWidth m*(⌊cellCenter (mesh D) l (3:Fin 4)/meshWidth m⌋:ℝ)| ≤ _
    exact hraw.trans (by linarith only [ht'])
  rw [chartHeightCoordinate_distance m shift] at hbound
  linarith only [hbound]

/-- Original-point matrix selection on the LITERAL native physical HEIGHT cell.
Its matrix diameter is derived from the actual raw-height window, including
the one-bin rounding cost. No height-grid identity or local variation is assumed. -/
theorem select_actual_raw_matrix_palette {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (S : Finset (Fin n × Index)) (hS : S.Nonempty)
    (ell : ℕ) (hell : ell=2 ∨ ell=3)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (metric shift : ℝ) (hmetric : 0 ≤ metric)
    (M : Fin K → ℕ) (hM : ∀j,0 < M j)
    (hwindow : ∀j,meshWidth m/512 ≤ 64/(M j:ℝ))
    (Hmetric : ∀z∈S,∀u∈S,‖F (spatialLabel D (2^m) z.2 (3:Fin 4))-F (spatialLabel D (2^m) u.2 (3:Fin 4))‖ ≤
      metric*|chartHeightCoordinate m shift (spatialLabel D (2^m) z.2 (3:Fin 4))-
        chartHeightCoordinate m shift (spatialLabel D (2^m) u.2 (3:Fin 4))|) :
    let R := modulus (2*metric)
    ∃B⊆S.image Prod.snd,let T := NativeFinitePointCoherence.lift S Prod.snd B
      T.Nonempty ∧ S.card ≤ R^(2*K)*T.card ∧
      (∀j z u,z∈T → u∈T → physicalCell D a (2^m) (M j) p z.2 (3:Fin 4)=
          physicalCell D a (2^m) (M j) p u.2 (3:Fin 4) →
        ‖F (spatialLabel D (2^m) z.2 (3:Fin 4))-F (spatialLabel D (2^m) u.2 (3:Fin 4))‖ < 64/(M j:ℝ)) ∧
      (∀k∈B,T.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) := by
  intro R
  have hR : 0 < R := modulus_pos _
  let : Nonempty (Fin 2 → Fin R) := ⟨fun _ => ⟨0,hR⟩⟩
  obtain ⟨entry,hentry⟩ := exists_entry_readback ell hell
  let rho := fun j : Fin K => 64/(M j:ℝ)
  have hrho (j : Fin K) : 0 < rho j := by
    have hMr : (0:ℝ) < M j := by exact_mod_cast hM j
    dsimp [rho]
    positivity
  let paint := fun (j : Fin K) (k : Index) =>
    SeparatedAlignmentPatches.color R hR
      (SeparatedAlignmentPatches.cell (rho j) (entry (F (spatialLabel D (2^m) k (3:Fin 4)))))
  have hcap (j : Fin K) (c : ℤ) :
      (((S.filter (fun z => physicalCell D a (2^m) (M j) p z.2 (3:Fin 4)=c)).image
        (fun z => paint j z.2)).card:ℝ) ≤ ((R^2:ℕ):ℝ) := by
    have hh := card_le_univ
      ((S.filter (fun z => physicalCell D a (2^m) (M j) p z.2 (3:Fin 4)=c)).image (fun z => paint j z.2))
    have hc : ((S.filter (fun z => physicalCell D a (2^m) (M j) p z.2 (3:Fin 4)=c)).image
        (fun z => paint j z.2)).card ≤ R^2 := by
      simpa only [Fintype.card_fun,Fintype.card_fin] using hh
    exact_mod_cast hc
  obtain ⟨B,hB,hT,hCost,hCompat,hFiber⟩ := select_original_point_fibers S hS Prod.snd K
    (fun j k => physicalCell D a (2^m) (M j) p k (3:Fin 4)) paint (fun _ => ((R^2:ℕ):ℝ)) hcap
  have hprod : (∏_j : Fin K,⌈((R^2:ℕ):ℝ)⌉₊)=R^(2*K) := by
    simp only [Nat.ceil_natCast,prod_const,card_univ,Fintype.card_fin]
    exact (pow_mul R 2 K).symm
  rw [hprod] at hCost
  refine ⟨B,hB,hT,hCost,?_,hFiber⟩
  intro j z u hz hu hcell
  have hzS := (mem_filter.mp hz).1
  have huS := (mem_filter.mp hu).1
  have ht := physical_height_chart_window D a (2^m) (M j) m (hM j) p z.2 u.2 shift hcell
  have htime : |chartHeightCoordinate m shift (spatialLabel D (2^m) z.2 (3:Fin 4))-
      chartHeightCoordinate m shift (spatialLabel D (2^m) u.2 (3:Fin 4))| ≤ 2*rho j := by
    have hw := hwindow j
    dsimp [rho]
    linarith only [ht,hw]
  have hvar : ‖F (spatialLabel D (2^m) z.2 (3:Fin 4))-F (spatialLabel D (2^m) u.2 (3:Fin 4))‖ ≤ (2*metric)*rho j := by
    have hh := (Hmetric z hzS u huS).trans (mul_le_mul_of_nonneg_left htime hmetric)
    nlinarith only [hh]
  have hclose : dist (entry (F (spatialLabel D (2^m) z.2 (3:Fin 4)))) (entry (F (spatialLabel D (2^m) u.2 (3:Fin 4)))) <
      (2*metric+1)*rho j := by
    rw [hentry]
    nlinarith only [hvar,hrho j]
  have hgap : (2*metric+1)*rho j ≤ ((R:ℝ)-1)*rho j := by
    apply mul_le_mul_of_nonneg_right _ (hrho j).le
    have hh := Nat.le_ceil (2*metric)
    dsimp [R,modulus]
    push_cast
    linarith only [hh]
  have heq := SeparatedAlignmentPatches.close_same_color_cell_eq (rho j) ((2*metric+1)*rho j)
    (hrho j) R hR hgap (entry (F (spatialLabel D (2^m) z.2 (3:Fin 4)))) (entry (F (spatialLabel D (2^m) u.2 (3:Fin 4))))
    (hCompat j z u hz hu hcell) hclose
  have hh := SeparatedAlignmentPatches.same_cell_dist_lt (rho j) (hrho j) _ _ heq
  rw [hentry] at hh
  exact hh

end NativePhysicalMatrixPalette
