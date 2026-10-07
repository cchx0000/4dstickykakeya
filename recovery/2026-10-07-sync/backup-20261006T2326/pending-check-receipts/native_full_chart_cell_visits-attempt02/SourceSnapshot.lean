import Theorems.Thm_StickyKakeya4_native_graph_tube_cell_visits
import Theorems.Thm_StickyKakeya4_native_full_chart_tube_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeFullChartCellVisits
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeFullCoarseShadow NativeGraphTubeCellVisits

/-- Homogeneous graph coordinates keep the actual time coordinate. -/
def graphBase (l : MarkedLine) : E4 := WithLp.toLp 2 (Fin.lastCases 0 (intercept l))
def graphSlope (l : MarkedLine) : E4 := WithLp.toLp 2 (Fin.lastCases 1 (slope l))

/-- The same full-source tube family supplies both the bounded slopes and
analytic graph error internally. There is no admission or separation premise
on the coarse fullSource, and its Euclidean thickness remains64/2^b. -/
theorem actual_full_source_visits {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level b : ℕ) (hb : 8 ≤ b) (E : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4, O x (3:Fin 4)=x (3:Fin 4))
    (I : Finset (E4 × Fin (R.image (parentLabel D a (2^b))).card))
    {rho Delta : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hscale : 8*(64/((2^b:ℕ):ℝ)) ≤ rho^2) (hDelta : rho/2 ≤ Delta)
    (hI : ∀x i, (x,i)∈I → x∈markedUnitTube
      (MarkedIsometricChart.line O 0 ((fullSource h R a level b E).line i))
      (64/((2^b:ℕ):ℝ)))
    (hdiam : ∀x∈I.image Prod.fst, ∀y∈I.image Prod.fst, |x 3-y 3| ≤ rho)
    (i : Fin (R.image (parentLabel D a (2^b))).card) (hi : i∈I.image Prod.snd) :
    (visited I Delta i).card ≤ 17^4 := by
  let line := fun i => MarkedIsometricChart.line O 0 ((fullSource h R a level b E).line i)
  apply visited_card_le I (fun i => graphBase (line i)) (fun i => graphSlope (line i))
    hrho hrho1 hscale hDelta ?_ ?_ hdiam i hi
  · intro x i hxi j
    have hg := (NativeFullChartTubeGraph.full_source_graph_bounds h R a level b hb E O hO i x
      (hI x i hxi)).2
    refine Fin.lastCases ?_ (fun k => ?_) j
    · change |x (3:Fin 4)-0-x (3:Fin 4)*1| ≤ 8*(64/((2^b:ℕ):ℝ))
      simp only [sub_zero,mul_one,sub_self,abs_zero]
      positivity
    · simp only [graphBase,graphSlope,PiLp.toLp_apply,Fin.lastCases_castSucc]
      simpa only [mul_comm] using hg k
  · intro i _hi j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · change |(1:ℝ)| ≤ 2
      norm_num
    · simp only [graphSlope,PiLp.toLp_apply,Fin.lastCases_castSucc]
      exact NativeFullChartDirectionBounds.full_source_slope_bound h R a level b E O hO 0 i k

end NativeFullChartCellVisits
