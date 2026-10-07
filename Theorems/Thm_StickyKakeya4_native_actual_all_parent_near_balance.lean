import Theorems.Thm_StickyKakeya4_native_actual_same_source_near_balance
import Theorems.Thm_StickyKakeya4_native_all_parent_near_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeActualAllParentNearBalance
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeLocalParentSource NativeSameSourceMultiplicityBalance NativeSameSourceBalanceAbsorption
open NativeActualSameSourceNearBalance
open scoped BigOperators ENNReal

/-- Every active literal local source is near extremal on the same original
core E, once formal parent-point equality was included in its old menu.
The global comparison is the proved physical coarse-label theorem. -/
theorem actual_all_parent_near_lower
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
    D.thickness^(theta+gamma+eta)*rho^loss*eps^(-kappa) ≤
      (balanceCost*(factor d g L:ℝ)^2*(coreRadix original R L:ℝ)^8)*
        (NativeFiniteKakeyaCounts.multiplicity
          (source h R (parentEdges D a (2^(schedule j).val) E p) a (schedule j).val p)).toReal := by
  let m := (schedule j).val
  let f := parentLabel D a (2^m)
  let F := factor d g L
  let rad := coreRadix original R L
  let S := fun p => (NativeFiniteKakeyaCounts.multiplicity
    (source h R (parentEdges D a (2^m) E p) a m p)).toReal
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
  have htransfer : ∀q,(NativeIncidenceMultiplicityTower.parent E f q).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (NativeIncidenceMultiplicityTower.parent E f q) ≤
        localCost*(F:ℝ)*(rad:ℝ)^2*D.thickness^(-eta)*S q := by
    intro q hq
    exact core_parent_transfer h original horiginal ha R E d g L level hdg Rel schedule hcore j q hq
  have hr : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  have he : (0:ℝ)<((2^m:ℕ):ℝ)*D.thickness/64 := by have hd:=h.1.2.1; positivity
  have hscale := actual_scale_product (delta:=D.thickness) (by positivity : 0<2^m)
  exact NativeAllParentNearBalance.all_actual_parent_near_lower E f hcore.2.1 h.1.2.1 hr he hscale
    F rad S hnearE hphysical hcoarse hformal htransfer p hp

end NativeActualAllParentNearBalance
