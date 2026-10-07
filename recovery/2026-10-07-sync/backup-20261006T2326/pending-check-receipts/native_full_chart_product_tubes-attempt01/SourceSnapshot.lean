import Theorems.Thm_StickyKakeya4_native_full_chart_tube_graph
import Theorems.Thm_StickyKakeya4_native_coordinate_volume_transport

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeFullChartProductTubes
open Classical StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeFullCoarseShadow NativeFullChartTubeGraph

/-- The original E4 tube in the SAME scalar product coordinates used by
the volume/CW transport lies in its actual analytic8Delta graph tube. -/
theorem scalar_tube_containment {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level b : ℕ) (hb : 8 ≤ b) (E : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3:Fin 4)=x (3:Fin 4))
    (i : Fin (R.image (parentLabel D a (2^b))).card) :
    let lines := fun t => MarkedIsometricChart.line O 0 ((fullSource h R a level b E).line t)
    NativeCoordinateVolumeTransport.scalar '' markedUnitTube (lines i) (64/((2^b:ℕ):ℝ)) ⊆
      {q : NativeCoordinateVolumeTransport.ScalarSpace | |q.2.2| ≤ 1 ∧
        ‖q.1-intercept (lines i) 0-q.2.2 • slope (lines i) 0‖ ≤ 8*(64/((2^b:ℕ):ℝ)) ∧
        ‖q.2.1-(intercept (lines i) 1, intercept (lines i) 2)-
          q.2.2 • (slope (lines i) 1, slope (lines i) 2)‖ ≤ 8*(64/((2^b:ℕ):ℝ))} := by
  intro lines y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hh := full_source_graph_bounds h R a level b hb E O hO i x hx
  refine ⟨hh.1, ?_, ?_⟩
  · simpa only [lines, NativeCoordinateVolumeTransport.scalar, Real.norm_eq_abs, smul_eq_mul,
      show (0:Fin 3).castSucc=(0:Fin 4) from rfl, mul_comm] using hh.2 (0:Fin 3)
  · have hn := max_le (hh.2 (1:Fin 3)) (hh.2 (2:Fin 3))
    simpa only [lines, NativeCoordinateVolumeTransport.scalar, Prod.norm_def, Prod.fst_sub,
      Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Real.norm_eq_abs, smul_eq_mul,
      show (1:Fin 3).castSucc=(1:Fin 4) from rfl,
      show (2:Fin 3).castSucc=(2:Fin 4) from rfl, mul_comm] using hn

/-- The planar tangent grouping uses the same original tube, with its
two tangent residuals combined by the ordinary product norm. -/
theorem planar_tube_containment {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level b : ℕ) (hb : 8 ≤ b) (E : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3:Fin 4)=x (3:Fin 4))
    (i : Fin (R.image (parentLabel D a (2^b))).card) :
    let lines := fun t => MarkedIsometricChart.line O 0 ((fullSource h R a level b E).line t)
    NativeCoordinateVolumeTransport.planar '' markedUnitTube (lines i) (64/((2^b:ℕ):ℝ)) ⊆
      {q : NativeCoordinateVolumeTransport.PlanarSpace | |q.2.2| ≤ 1 ∧
        ‖q.1-(intercept (lines i) 0, intercept (lines i) 1)-
          q.2.2 • (slope (lines i) 0, slope (lines i) 1)‖ ≤ 8*(64/((2^b:ℕ):ℝ)) ∧
        ‖q.2.1-intercept (lines i) 2-q.2.2 • slope (lines i) 2‖ ≤ 8*(64/((2^b:ℕ):ℝ))} := by
  intro lines y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hh := full_source_graph_bounds h R a level b hb E O hO i x hx
  refine ⟨hh.1, ?_, ?_⟩
  · have hn := max_le (hh.2 (0:Fin 3)) (hh.2 (1:Fin 3))
    simpa only [lines, NativeCoordinateVolumeTransport.planar, Prod.norm_def, Prod.fst_sub,
      Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Real.norm_eq_abs, smul_eq_mul,
      show (0:Fin 3).castSucc=(0:Fin 4) from rfl,
      show (1:Fin 3).castSucc=(1:Fin 4) from rfl, mul_comm] using hn
  · simpa only [lines, NativeCoordinateVolumeTransport.planar, Real.norm_eq_abs, smul_eq_mul,
      show (2:Fin 3).castSucc=(2:Fin 4) from rfl, mul_comm] using hh.2 (2:Fin 3)

end NativeFullChartProductTubes
