import Theorems.Thm_StickyKakeya4_native_same_source_balance_absorption
import Theorems.Thm_StickyKakeya4_native_coarse_point_multiplicity
import Theorems.Thm_StickyKakeya4_native_actual_local_admission

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeActualSameSourceNearBalance
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeLocalParentSource NativeSameSourceMultiplicityBalance NativeSameSourceBalanceAbsorption
open scoped BigOperators ENNReal

/-- The stored local-pair lower bound of IsCore gives the exact original
parent-to-physical-source comparison on every active scheduled parent. -/
theorem core_parent_transfer {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index))
    (d g L level : ℕ) (hdg : 0<d+g)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (schedule : Fin g → Fin (level+1))
    (hcore : IsCore D original R a eta zeta d g L Rel (fun j => 2^(schedule j).val) E)
    (j : Fin g) (p : Parent) (hp : (parentEdges D a (2^(schedule j).val) E p).Nonempty) :
    let Ep := parentEdges D a (2^(schedule j).val) E p
    (Ep.card:ℝ)/(Ep.image Prod.snd).card ≤
      localCost*(factor d g L:ℝ)*(coreRadix original R L:ℝ)^2*D.thickness^(-eta)*
        (NativeFiniteKakeyaCounts.multiplicity (source h R Ep a (schedule j).val p)).toReal := by
  have hEA : E ⊆ retained original R := hcore.1
  have hE : E ⊆ incidences original := hEA.trans (filter_subset _ _)
  have hF : (0:ℝ)<factor d g L := by
    have hb : 0<d+g+g := by omega
    unfold factor NativeLocalPairUniformCore.retentionCost
    positivity
  have hrad : (0:ℝ)<coreRadix original R L := by
    have hh := NativeSourceSizeBounds.radix_four_le (retained original R).card L
    exact_mod_cast (show 0<coreRadix original R L by dsimp [coreRadix]; omega)
  have hQ : ∀z∈parentEdges D a (2^(schedule j).val) E p,
      z.1∈parentLabels D R a (2^(schedule j).val) p := by
    intro z hz
    obtain ⟨hzE,hzp⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨(mem_filter.mp (hEA hzE)).2,hzp⟩
  exact NativeActualLocalAdmission.source_parent_multiplicity_transfer h original horiginal ha
    R E hE (schedule j).val p hF hrad (hcore.2.2.2.2.2.2 j) hp hQ

/-- Deterministic near-extremal balance for literal original E, literal full
physical coarse shadow, and literal local-parent sources. The physical
comparison is proved from the two actual label-fiber uniformities inside this
proof; it is not a matched-multiplicity certificate supplied as a premise.
The upper inequalities are the conclusions of the joint admission consumer. -/
theorem actual_same_source_near_balance
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
    (hlocal : ∀p,(parentEdges D a (2^(schedule j).val) E p).Nonempty →
      (NativeFiniteKakeyaCounts.multiplicity
        (source h R (parentEdges D a (2^(schedule j).val) E p) a (schedule j).val p)).toReal ≤
          (((2^(schedule j).val:ℕ):ℝ)*D.thickness/64)^(-kappa-loss))
    (hcoarse : (NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level (schedule j).val E)).toReal ≤
      D.thickness^(-gamma)*(64/((2^(schedule j).val:ℕ):ℝ))^(-kappa-loss)) :
    let rho := 64/((2^(schedule j).val:ℕ):ℝ)
    let eps := ((2^(schedule j).val:ℕ):ℝ)*D.thickness/64
    let cost := balanceCost*(factor d g L:ℝ)^2*(coreRadix original R L:ℝ)^6
    D.thickness^(theta+eta)*eps^loss*rho^(-kappa) ≤
      cost*(NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level (schedule j).val E)).toReal ∧
    ∃p,(parentEdges D a (2^(schedule j).val) E p).Nonempty ∧
      D.thickness^(theta+gamma+eta)*rho^loss*eps^(-kappa) ≤
        cost*(NativeFiniteKakeyaCounts.multiplicity
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
  have hpne : ∀p∈E.image (fun z => f z.1),(parentEdges D a (2^m) E p).Nonempty :=
    fun p hp => NativeIncidenceMultiplicityTower.parent_nonempty E f hp
  have htransfer : ∀p∈E.image (fun z => f z.1),
      NativeIncidenceMultiplicityTower.multiplicity (NativeIncidenceMultiplicityTower.parent E f p) ≤
        localCost*(F:ℝ)*(rad:ℝ)^2*D.thickness^(-eta)*S p := by
    intro p hp
    exact core_parent_transfer h original horiginal ha R E d g L level hdg Rel schedule hcore j p (hpne p hp)
  have hparent : ∀p∈E.image (fun z => f z.1),
      NativeIncidenceMultiplicityTower.multiplicity (NativeIncidenceMultiplicityTower.parent E f p) ≤
        localCost*(F:ℝ)*(rad:ℝ)^2*D.thickness^(-eta)*
          (((2^m:ℕ):ℝ)*D.thickness/64)^(-kappa-loss) := by
    intro p hp
    exact (htransfer p hp).trans (mul_le_mul_of_nonneg_left (hlocal p (hpne p hp))
      (by have hd := h.1.2.1; dsimp [localCost]; positivity))
  have hr : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  have he : (0:ℝ)<((2^m:ℕ):ℝ)*D.thickness/64 := by have hd:=h.1.2.1; positivity
  have hscale := actual_scale_product (delta:=D.thickness) (by positivity : 0<2^m)
  refine ⟨coarse_near_lower E f h.1.2.1 hr he hscale F rad hnearE hparent hphysical,?_⟩
  obtain ⟨p,_hp,hpne,hlo⟩ := exists_actual_parent_near_lower E f hcore.2.1 h.1.2.1 hr he hscale
    F rad S hnearE hphysical hcoarse htransfer
  exact ⟨p,hpne,hlo⟩

end NativeActualSameSourceNearBalance
