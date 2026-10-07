import Theorems.Thm_StickyKakeya4_native_actual_all_parent_near_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

noncomputable section
namespace NativeOldParentNearLower
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeSameSourceMultiplicityBalance NativeSameSourceBalanceAbsorption NativeIncidenceMultiplicityTower
open scoped BigOperators ENNReal

/-- The OLD parent incidence lower survives uniformly on all active parents.
This direction is proved before the physical local-source transfer, so it can
be used when merging finer original parents at an intermediate scale. -/
theorem all_old_parent_near_lower {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (E : Finset (T × X)) (f : T → P) (hne : E.Nonempty)
    {delta rho eps kappa theta gamma loss C : ℝ}
    (hd : 0<delta) (hr : 0<rho) (he : 0<eps) (hscale : rho*eps=delta)
    (F rad : ℕ)
    (hnear : delta^(-kappa+theta) ≤ (F:ℝ)*multiplicity E)
    (hphysical : multiplicity (coarse E f) ≤ 125*(rad:ℝ)^4*C)
    (hupper : C ≤ delta^(-gamma)*rho^(-kappa-loss))
    (hformal : ∀x∈E,∀y∈E,
      (E.filter (fun z => (f z.1,z.2)=(f x.1,x.2))).card ≤
        rad^2*(E.filter (fun z => (f z.1,z.2)=(f y.1,y.2))).card)
    (q : P) (hq : (parent E f q).Nonempty) :
    delta^(theta+gamma)*rho^loss*eps^(-kappa) ≤
      (125:ℝ)*(F:ℝ)*(rad:ℝ)^6*multiplicity (parent E f q) := by
  obtain ⟨p,_hp,hpne,hlo⟩ := exists_parent_near_lower E f hne hd hr he hscale F rad hnear hphysical hupper
  have hcomp := NativeParentAverageUniformity.parent_multiplicity_le E f rad hformal p hpne q hq
  exact (hlo.trans (mul_le_mul_of_nonneg_left hcomp
    (show (0:ℝ)≤125*(F:ℝ)*(rad:ℝ)^4 by positivity))).trans_eq (by ring)

lemma old_cost_le_balance (F rad : ℕ) (hF : 0<F) :
    (125:ℝ)*(F:ℝ)*(rad:ℝ)^6 ≤ balanceCost*(F:ℝ)^2*(rad:ℝ)^6 := by
  have hFr : (1:ℝ)≤F := by exact_mod_cast hF
  have hF2 : (F:ℝ)≤(F:ℝ)^2 := by nlinarith
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (mul_le_mul_of_nonneg_right (by norm_num [balanceCost,localCost] : (125:ℝ)≤balanceCost)
    (Nat.cast_nonneg F)).trans
    (mul_le_mul_of_nonneg_left hF2 (by norm_num [balanceCost,localCost]))

/-- Actual source/core specialization of the old-parent lower, using the
proved geometric comparison with the literal full physical coarse shadow. -/
theorem actual_old_parent_near_lower
    {n : ℕ} {D : FiniteScaleSource n} {eta zeta a kappa theta gamma loss : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index))
    (d g L level : ℕ) (hdg : 0<d+g) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (schedule : Fin g → Fin (level+1))
    (hcore : IsCore D original R a eta zeta d g L Rel (fun j => 2^(schedule j).val) E)
    (j : Fin g)
    (hnear : D.thickness^(-kappa+theta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal)
    (hpair : let m := (schedule j).val
      let rep := NativeCoarseDirectionThinning.representative h R a (2^m)
      let B := NativeCoarseDyadicShading.block level m
      ∀x∈E,∀y∈E,
      (E.filter (fun z => NativeCoarseShadingCapacity.label D a (2^m) B rep z=
        NativeCoarseShadingCapacity.label D a (2^m) B rep x)).card ≤
        (coreRadix original R L)^2*(E.filter (fun z => NativeCoarseShadingCapacity.label D a (2^m) B rep z=
          NativeCoarseShadingCapacity.label D a (2^m) B rep y)).card)
    (hpoint : let m := (schedule j).val
      let rep := NativeCoarseDirectionThinning.representative h R a (2^m)
      let B := NativeCoarseDyadicShading.block level m
      ∀x∈E,∀y∈E,
      (E.filter (fun z => NativeCoarsePointMultiplicity.pointLabel D a (2^m) B rep z=
        NativeCoarsePointMultiplicity.pointLabel D a (2^m) B rep x)).card ≤
        (coreRadix original R L)^2*(E.filter (fun z => NativeCoarsePointMultiplicity.pointLabel D a (2^m) B rep z=
          NativeCoarsePointMultiplicity.pointLabel D a (2^m) B rep y)).card)
    (hformal : ∀x∈E,∀y∈E,
      (E.filter (fun z => (parentLabel D a (2^(schedule j).val) z.1,z.2)=
        (parentLabel D a (2^(schedule j).val) x.1,x.2))).card ≤
        (coreRadix original R L)^2*(E.filter (fun z => (parentLabel D a (2^(schedule j).val) z.1,z.2)=
          (parentLabel D a (2^(schedule j).val) y.1,y.2))).card)
    (hcoarse : (NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level (schedule j).val E)).toReal ≤
      D.thickness^(-gamma)*(64/((2^(schedule j).val:ℕ):ℝ))^(-kappa-loss))
    (p : Parent) (hp : (parentEdges D a (2^(schedule j).val) E p).Nonempty) :
    let rho := 64/((2^(schedule j).val:ℕ):ℝ)
    let eps := ((2^(schedule j).val:ℕ):ℝ)*D.thickness/64
    D.thickness^(theta+gamma)*rho^loss*eps^(-kappa) ≤
      (125:ℝ)*(factor d g L:ℝ)*(coreRadix original R L:ℝ)^6*
        NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^(schedule j).val) E p) := by
  let m := (schedule j).val
  let f := parentLabel D a (2^m)
  let F := factor d g L
  let rad := coreRadix original R L
  have hEA : E ⊆ retained original R := hcore.1
  have hE : E ⊆ incidences original := hEA.trans (filter_subset _ _)
  have hR : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hEA hz)).2
  have hF : 0<F := by
    have hb : 0<d+g+g := by omega
    dsimp [F,factor,NativeLocalPairUniformCore.retentionCost]
    positivity
  have hnearE := selected_source_near h original horiginal E hE F hF hcore.2.2.1 hnear
  have hphysical := NativeCoarsePointMultiplicity.multiplicity_le_full_source h original horiginal ha
    R E hE hR level m hdy (Nat.le_of_lt_succ (schedule j).isLt) rad hpair hpoint
  have hr : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  have he : (0:ℝ)<((2^m:ℕ):ℝ)*D.thickness/64 := by have hd:=h.1.2.1; positivity
  have hscale := actual_scale_product (delta:=D.thickness) (by positivity : 0<2^m)
  exact all_old_parent_near_lower E f hcore.2.1 h.1.2.1 hr he hscale
    F rad hnearE hphysical hcoarse hformal p hp

end NativeOldParentNearLower
