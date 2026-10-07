import Theorems.Thm_StickyKakeya4_native_local_direction_tube_support

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeAngularPacketReadback
open Classical StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeDirectionRankDichotomy
open NativeLocalDirectionTubeSupport

/-- A literal common angular grid label controls the actual graph vectors;
intercept labels are not identified. -/
theorem same_angular_slopeVector_dist {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (hN : 0 < N) (i j : Fin n)
    (hangular : (parentLabel D a N i).1=(parentLabel D a N j).1) :
    dist (slopeVector D i) (slopeVector D j) ≤ 2/(N:ℝ) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hcoord : ∀v : Fin 3, |slope (D.line i) v-slope (D.line j) v| ≤ 1/(N:ℝ) := by
    intro v
    have he : ⌊(N:ℝ)*slope (D.line i) v⌋=⌊(N:ℝ)*slope (D.line j) v⌋ := congrFun hangular v
    have hi0 := Int.floor_le ((N:ℝ)*slope (D.line i) v)
    have hi1 := Int.lt_floor_add_one ((N:ℝ)*slope (D.line i) v)
    have hj0 := Int.floor_le ((N:ℝ)*slope (D.line j) v)
    have hj1 := Int.lt_floor_add_one ((N:ℝ)*slope (D.line j) v)
    rw [he] at hi0 hi1
    have hh : |(N:ℝ)*(slope (D.line i) v-slope (D.line j) v)| ≤ 1 :=
      abs_le.mpr ⟨by nlinarith,by nlinarith⟩
    rw [abs_mul,abs_of_pos hNr] at hh
    apply (le_div_iff₀ hNr).mpr
    nlinarith
  have hsq : ‖slopeVector D i-slopeVector D j‖^2 ≤ 3*(1/(N:ℝ))^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_castSucc,Fin.sum_univ_three]
    simp only [PiLp.sub_apply,slopeVector,ActualSlopeSource.heightPoint_castSucc,
      ActualSlopeSource.heightPoint_last,sub_self,zero_pow (by decide : 2≠0),add_zero]
    have h0 := pow_le_pow_left₀ (abs_nonneg _) (hcoord 0) 2
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (hcoord 1) 2
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (hcoord 2) 2
    simp only [sq_abs] at h0 h1 h2
    nlinarith only [h0,h1,h2]
  rw [dist_eq_norm]
  have hp : 0 ≤ 1/(N:ℝ) := by positivity
  rw [show (2:ℝ)/(N:ℝ)=2*(1/(N:ℝ)) by ring]
  nlinarith only [hsq,norm_nonneg (slopeVector D i-slopeVector D j),sq_nonneg (1/(N:ℝ)),hp]

/-- The selected angular tuple's fine witness really controls original
tube pieces at the squared spatial scale. It uses the literal old cell,
old marked tube and same angular label, without changing old errors. -/
theorem original_tube_packet_from_angular_label {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (hNlarge : 64/(N:ℝ) ≤ 1)
    (hscale : D.thickness ≤ (64/(N:ℝ))^2)
    {i : Fin n} {k : Index} (hik : (i,k)∈incidences original)
    (j : Fin n) (hangular : (parentLabel D a N i).1=(parentLabel D a N j).1)
    {y : E4} (hy : y∈markedUnitTube (D.line i) D.thickness)
    (hheight : |y (3:Fin 4)-cellCenter (mesh D) k (3:Fin 4)| ≤ 64/(N:ℝ)) :
    Metric.infDist (y-cellCenter (mesh D) k)
      (Submodule.span ℝ {slopeVector D j}:Set E4) ≤ 14*(64/(N:ℝ))^2 := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hj : slopeVector D j∈(Submodule.span ℝ {slopeVector D j}:Set E4) :=
    Submodule.subset_span (by simp)
  have hn : Metric.infDist (slopeVector D i)
      (Submodule.span ℝ {slopeVector D j}:Set E4) ≤ 64/(N:ℝ) := by
    apply (Metric.infDist_le_dist_of_mem hj).trans
    exact (same_angular_slopeVector_dist D a N hN i j hangular).trans
      (div_le_div_of_nonneg_right (by norm_num) hNr.le)
  exact original_local_quadratic_packet h original horiginal hik
    (Submodule.span ℝ {slopeVector D j}) (by positivity) hNlarge hscale hn hy hheight

end NativeAngularPacketReadback
