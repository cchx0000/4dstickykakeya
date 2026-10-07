import Theorems.Thm_StickyKakeya4_native_saturated_source_angular_rank_lower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeScheduledAngularAncestor
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalMenuInterpolation NativeJointUniformCoarseRelations NativeMiddleWindowBalance
open NativeFixedSizeScaleMenu NativeActualMesoscopicRankConfiguration NativeAllTwoScaleConfiguration
open SelfUniform

/-- The actual scheduled relation already stored by the source is exactly
formalPair equality, so its constant is read back without a refinement. -/
theorem formal_uniformity_readback {n : ℕ} (D : FiniteScaleSource n)
    (E1 : Finset (Fin n × Index)) (a : ℝ) (depth Q : ℕ)
    (H : ∀x y,x∈E1 → y∈E1 →
      degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^depth)) E1 x≤ 
        Q^2*degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^depth)) E1 y) :
    HasUniformFibers E1 Q (formalPair D a depth) := by
  intro x hx y hy
  have hh := H x y hx hy
  change degree (fun _ : Fin n × Index => 1) (fun u v => formalPair D a depth u=formalPair D a depth v) E1 x≤
    Q^2*degree (fun _ : Fin n × Index => 1) (fun u v => formalPair D a depth u=formalPair D a depth v) E1 y at hh
  simpa only [unit_degree_eq_fiber] using hh

/-- The source's fixed rankWindow grid supplies an already uniform
ancestor for any requested depth in that window. Its exact gap is at most
2/g, which is paid by tau; no relation is added after E1. -/
theorem exists_actual_angular_ancestor {n : ℕ} (D : FiniteScaleSource n)
    (E1 : Finset (Fin n × Index)) (a tau : ℝ) (htau : 0< tau)
    (g level depth Q : ℕ) (hg : 0< g) (hgl : g≤ level)
    (hgrid : 1/(g:ℝ)< rankWindow tau/4)
    (schedule : Fin (g+1) → Fin (level+1)) (hschedule : schedule=fullSchedule tau htau g level)
    (H : ∀j x y,x∈E1 → y∈E1 →
      degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^(schedule j).val)) E1 x≤ 
        Q^2*degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^(schedule j).val)) E1 y)
    (hlo : rankWindow tau*(level:ℝ)≤ depth)
    (hhi : (depth:ℝ)≤ (1-rankWindow tau)*(level:ℝ)) :
    0≤ 2/(g:ℝ) ∧ 2/(g:ℝ)≤ tau ∧
      ∃j : Fin (g+1),(schedule j).val≤ depth ∧
        ((depth-(schedule j).val:ℕ):ℝ)≤ (2/(g:ℝ))*(level:ℝ) ∧
        HasUniformFibers E1 Q (formalPair D a (schedule j).val) := by
  have hw := rankWindow_pos htau
  have hwsmall : rankWindow tau< 1/2 :=
    (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num))
  have hlarge := large_level_of_grid (rankWindow tau) hw g level hg hgrid hgl
  have hgapTau : 2/(g:ℝ)≤ tau := by
    have hwTau : rankWindow tau≤ (tau/16)/1000 := min_le_right _ _
    rw [show 2/(g:ℝ)=2*(1/(g:ℝ)) by ring]
    linarith only [hgrid,hwTau,htau]
  have hsched : schedule=windowSchedule (rankWindow tau) hw.le g level := by
    rw [hschedule]
    exact fullSchedule_eq_rankWindow tau htau g level
  obtain ⟨j,hj,_hgapNat,hgap⟩ := exists_window_predecessor (rankWindow tau) hw hwsmall
    g level depth hg hgrid hlarge hlo hhi
  rw [←hsched] at hj hgap
  exact ⟨by positivity,hgapTau,j,hj,gap_le_twice_fraction g level depth _ hg hgl hgap,
    formal_uniformity_readback D E1 a (schedule j).val Q (H j)⟩

end NativeScheduledAngularAncestor
