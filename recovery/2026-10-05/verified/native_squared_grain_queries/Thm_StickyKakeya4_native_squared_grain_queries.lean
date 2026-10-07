import Theorems.Thm_StickyKakeya4_native_actual_query_rank_configuration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section

namespace NativeSquaredGrainQueries
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning NativeJointUniformCoarseRelations
open NativeRetainedQueryMenu NativeActualQueryRankConfiguration
open NativeActualMesoscopicRankConfiguration NativeAllTwoScaleConfiguration

/-- A phase parent and raw vertex at squared grain scale. -/
def phaseDepth (m : ℕ) : ℕ := 2*m-6

lemma phaseDepth_bounds (m stop level : ℕ) (hm6 : 6 ≤ m) (hm : m ≤ stop)
    (hstop : stop ≤ level/4) : m ≤ phaseDepth m ∧ phaseDepth m ≤ level := by
  dsimp [phaseDepth]
  omega

/-- The exact physical mesh identity, including the native factor 64. -/
lemma squared_scale_identity (m : ℕ) (hm6 : 6 ≤ m) :
    (64:ℝ)/((2^(phaseDepth m):ℕ):ℝ)=((64:ℝ)/((2^m:ℕ):ℝ))^2 := by
  have hexp : phaseDepth m+6=m*2 := by dsimp [phaseDepth]; omega
  have hpow : (2:ℕ)^(phaseDepth m)*64=(2^m)^2 := by
    calc
      _ = 2^(phaseDepth m+6) := by rw [pow_add]; norm_num
      _ = _ := by rw [hexp,pow_mul]
  have hpowR : ((2^(phaseDepth m):ℕ):ℝ)*64=((2^m:ℕ):ℝ)^2 := by exact_mod_cast hpow
  rw [div_pow]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  nlinarith

lemma phase_inverse_le_square (m : ℕ) (hm6 : 6 ≤ m) :
    (1:ℝ)/((2^(phaseDepth m):ℕ):ℝ) ≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2 := by
  rw [←squared_scale_identity m hm6]
  exact div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 64) (by positivity)

lemma short_fine_scale_ratio (m : ℕ) (hm6 : 6 ≤ m) :
    ((64:ℝ)/((2^m:ℕ):ℝ))/((64:ℝ)/((2^(phaseDepth m):ℕ):ℝ))=
      1/((64:ℝ)/((2^m:ℕ):ℝ)) := by
  rw [squared_scale_identity m hm6]
  field_simp

/-- One short-row query and one squared-vertex query per independent grain.
The total count is fixed before tau, while stop is the actual selected depth. -/
def pairedQueries (J stop : ℕ) : Fin ((J+1)+(J+1)) → ℕ × ℕ :=
  Fin.addCases
    (fun i : Fin (J+1) => (phaseDepth (grainDepth J stop i),grainDepth J stop i))
    (fun i : Fin (J+1) => (phaseDepth (grainDepth J stop i),phaseDepth (grainDepth J stop i)))

lemma paired_query_count (J : ℕ) : (J+1)+(J+1)=2*(J+1) := by omega

lemma pairedQueries_short (J stop : ℕ) (i : Fin (J+1)) :
    pairedQueries J stop (Fin.castAdd (J+1) i)=
      (phaseDepth (grainDepth J stop i),grainDepth J stop i) := by
  simp only [pairedQueries,Fin.addCases_left]

lemma pairedQueries_vertex (J stop : ℕ) (i : Fin (J+1)) :
    pairedQueries J stop (Fin.natAdd (J+1) i)=
      (phaseDepth (grainDepth J stop i),phaseDepth (grainDepth J stop i)) := by
  simp only [pairedQueries,Fin.addCases_right]

lemma pairedQueries_valid (J stop level : ℕ) (hstop6 : 6 ≤ stop) (hstop : stop ≤ level/4) :
    ∀i : Fin ((J+1)+(J+1)),(pairedQueries J stop i).2 ≤ (pairedQueries J stop i).1 ∧
      (pairedQueries J stop i).1 ≤ level := by
  have hb (i : Fin (J+1)) := phaseDepth_bounds (grainDepth J stop i) stop level
    (by simpa only [grainQueries] using grainQueries_six_le J stop hstop6 i)
    (grainDepth_bounds J stop i).2 hstop
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [pairedQueries,Fin.addCases_left] using hb j
  · intro j
    simpa only [pairedQueries,Fin.addCases_right] using
      (show phaseDepth (grainDepth J stop j) ≤ phaseDepth (grainDepth J stop j) ∧
        phaseDepth (grainDepth J stop j) ≤ level from ⟨le_rfl,(hb j).2⟩)

/-- Decode both geometries on the SAME E2: projected short-row labels at
(fine phase depth, angular grain depth), and raw physical vertices at phase depth. -/
theorem pairedQueries_uniformities {n J : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level stop : ℕ) (E2 : Finset (Fin n × Index)) (Q2 : ℕ)
    (HF : ∀i,HasUniformFibers E2 Q2 (fineQueryPair h R a level (pairedQueries J stop) i))
    (HC : ∀i,HasUniformFibers E2 Q2 (shortQueryPair h R a level (pairedQueries J stop) i))
    (HV : ∀i,HasUniformFibers E2 Q2 (rawQueryPoint D (pairedQueries J stop) i)) :
    ∀i : Fin (J+1),
      let m := grainDepth J stop i
      let b := phaseDepth m
      let rep := representative h R a (2^b)
      HasUniformFibers E2 Q2 (fixedPair D a level b b rep) ∧
      HasUniformFibers E2 Q2 (fixedPair D a level b m rep) ∧
      HasUniformFibers E2 Q2 (fun z => NativeSpatialAngularGeometry.spatialLabel D (2^b) z.2) ∧
      HasUniformFibers E2 Q2 (fun z => NativeSpatialAngularGeometry.spatialLabel D (2^m) z.2) := by
  intro i
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [fineQueryPair,pairedQueries_short] using HF (Fin.castAdd (J+1) i)
  · simpa only [shortQueryPair,pairedQueries_short] using HC (Fin.castAdd (J+1) i)
  · have hv := HV (Fin.natAdd (J+1) i)
    change HasUniformFibers E2 Q2 (fun z => NativeSpatialAngularGeometry.spatialLabel D
      (2^(pairedQueries J stop (Fin.natAdd (J+1) i)).2) z.2) at hv
    simpa only [pairedQueries_vertex] using hv
  · have hv := HV (Fin.castAdd (J+1) i)
    change HasUniformFibers E2 Q2 (fun z => NativeSpatialAngularGeometry.spatialLabel D
      (2^(pairedQueries J stop (Fin.castAdd (J+1) i)).2) z.2) at hv
    simpa only [pairedQueries_short] using hv

/-- The selected source schedule has the exact same mesoscopic cap used to
validate squared-grain phase depths. -/
lemma stopping_depth_cap {tau : ℝ} (htau : 0 < tau) (g level : ℕ)
    (schedule : Fin (g+1) → Fin (level+1))
    (hschedule : schedule=fullSchedule tau htau g level) (j : Fin (g+1))
    (hj : j∈NativeRankMesoscopicRadiusMenu.menu (rankWindow tau) (rankWindow_pos htau).le g level) :
    (schedule j).val ≤ level/4 := by
  rw [hschedule,fullSchedule_eq_rankWindow]
  exact (mem_filter.mp hj).2

end NativeSquaredGrainQueries
