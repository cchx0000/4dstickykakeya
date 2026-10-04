import Theorems.Thm_StickyKakeya4_native_original_height_vertices
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeSourceHeightDensity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeOriginalSlicePopulation
open NativeDenseSourceRefinement NativeOriginalHeightVertices OriginalWCoarseEscapeMenus

/-- Literal source-D-to-phase-vertex adapter. Every time, residual, tube and
point label is read from the same original physical incidence subset. -/
theorem actual_source_height_vertex_density {n : ℕ} (D : FiniteScaleSource n)
    (cells : Fin n→Finset Index) (a : ℝ) (N : ℕ) (p : Parent)
    (hp : p∈parents D a N) (hdelta : D.thickness≤1)
    (hP : (data D cells a N p).Hypotheses)
    (E : Finset (Fin n×Cell)) (F : ℕ) (hF : 0<F) {lam : ℝ}
    (hlam : 0≤lam) (hl : lam≤(data D cells a N p).lam)
    (hE : E⊆(data D cells a N p).incidences)
    (hret : (data D cells a N p).incidences.card≤F*E.card) :
    (lam/(87808*(F:ℝ)))*((heights E (D.thickness/8)).card:ℝ)*
      (TwoTubePathCollisionCount.tubes (pointTube E)).card≤
        (vertices (pointTube E) (height (D.thickness/8))).card := by
  let P := data D cells a N p
  have hmesh : P.δ=D.thickness/8 := by dsimp [P,data,mesh]; ring
  have hm : 0<D.thickness/8 := hmesh ▸ hP.delta_pos
  have hm1 : D.thickness/8≤1 := by linarith
  have hden := refinement_tube_density D cells a N p hp E F hlam hP.delta_pos.le hl hE hret
  rw [hmesh] at hden
  apply original_height_vertex_density E F hm hm1 hF P.tubeSlope P.tubeOffset _ _ hden
  · intro t c hc
    have hh := hP.time_bound (t,c) (hE hc)
    change |height P.δ c|≤1 at hh
    rwa [hmesh] at hh
  · intro t c hc j
    have hh := hP.physical_bound (t,c) (hE hc) j
    have hrho : 0<P.ρ := one_div_pos.mpr (by exact_mod_cast hP.N_pos)
    rw [P.residual_eq_original,abs_div,abs_of_pos hrho] at hh
    have hx := (div_le_iff₀ hrho).mp hh
    have hcancel : (P.E:ℝ)*P.σ*P.ρ=12*(D.thickness/8) := by
      change (12:ℝ)*((N:ℝ)*(mesh D/4))*(1/(N:ℝ))=12*(D.thickness/8)
      have hn : (N:ℝ)≠0 := by exact_mod_cast hP.N_pos.ne'
      dsimp [mesh]
      field_simp
      ring
    rw [hcancel,hmesh] at hx
    exact hx

end NativeSourceHeightDensity
