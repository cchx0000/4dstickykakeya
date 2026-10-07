import Theorems.Thm_StickyKakeya4_native_two_axis_power_interpolation
import Theorems.Thm_StickyKakeya4_native_two_scale_configuration
import Theorems.Thm_StickyKakeya4_native_conditional_coarse_interpolation
import Theorems.Thm_StickyKakeya4_native_conditional_coarse_diagonal
import Theorems.Thm_StickyKakeya4_native_coarse_scale_reverse

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeTwoAxisConditionalTransfer
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeDyadicParentCells NativeJointUniformCoarseRelations
open NativeIncidenceMultiplicityTower NativeConditionalCoarseInterpolation NativeConditionedPairMenu
open NativeTwoAxisPowerInterpolation NativeTwoScaleConfiguration NativeFixedCompactKakeyaExponent

/-- Exact physical readback on an arbitrary literal original parent. -/
lemma conditional_full_eq_image {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m f : ℕ)
    (hER : ∀z∈E,z.1∈R) (p : Parent) :
    (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E p))).toReal =
      multiplicity ((parentEdges D a (2^m) E p).image (physicalPair h R a level f)) := by
  exact NativeCoarsePointMultiplicity.full_source_multiplicity_real h R a level f _
    (fun z hz => hER z (mem_filter.mp hz).1)

lemma scheduled_image_bounds {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m f : ℕ) (loss : ℝ)
    (hER : ∀z∈E,z.1∈R) (H : HasConditionalTwoScale h R E a level m f loss)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty) :
    D.thickness^loss*depthPower extremalExponent m f ≤
      multiplicity ((parentEdges D a (2^m) E p).image (physicalPair h R a level f)) ∧
    multiplicity ((parentEdges D a (2^m) E p).image (physicalPair h R a level f)) ≤
      D.thickness^(-loss)*depthPower extremalExponent m f := by
  rw [depthPower_eq_relative,←conditional_full_eq_image h R E a level m f hER p]
  exact H p hp

/-- The finite caller's one core directly retains all conditioned physical
uniformities. No second uniformization or assumed fiber certificate is used. -/
theorem core_conditioned_uniformities {n d g level : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (L : ℕ)
    (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : IsCore D original R a eta zeta (menuSize (pairMenuSize d g) g) g L
      (relationMenu h R a schedule (pairRelationMenu h R a schedule Rel))
      (fun j => 2^(schedule j).val) E) (i j : Fin g) :
    HasUniformFibers E (coreRadix original R L)
      (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
    HasUniformFibers E (coreRadix original R L)
      (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val) := by
  have hCaller : ∀j x y,x∈E → y∈E →
      SelfUniform.degree (fun _ : Fin n × Index => 1) (pairRelationMenu h R a schedule Rel j) E x ≤
        (coreRadix original R L)^2*
          SelfUniform.degree (fun _ : Fin n × Index => 1) (pairRelationMenu h R a schedule Rel j) E y := by
    intro j x y hx hy
    simpa only [relationMenu,Fin.addCases_left] using
      H.2.2.2.1 (Fin.castAdd (g+(g+g)) j) x y hx hy
  obtain ⟨hG,hX,_hR,_hY⟩ := pairRelationMenu_uniformities h R a schedule Rel E _ hCaller i j
  exact ⟨hG,hX⟩

/-- Genuine two-axis interpolation at a far pair. The scheduled lower uses
finer outer parents; the scheduled upper uses the coarse outer ancestor.
Every actual projection uses the original global-R representatives. -/
theorem far_pair_bounds {n : ℕ} {D : FiniteScaleSource n} {eta a loss s : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆NativeCubicalIncidenceCounts.incidences original)
    (hER : ∀z∈E,z.1∈R) (level c m d b f : ℕ)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hcm : c ≤ m) (hmd : m ≤ d)
    (hdb : d ≤ b) (hbf : b ≤ f) (hfl : f ≤ level)
    (hgapC : ((m-c:ℕ):ℝ) ≤ s*level) (hgapD : ((d-m:ℕ):ℝ) ≤ s*level)
    (hgapF : ((f-b:ℕ):ℝ) ≤ s*level) (rad : ℕ)
    (hG : HasUniformFibers E rad (conditionedGlobalPair h R a level c b))
    (hX : HasUniformFibers E rad (conditionedGlobalPoint h R a level c b))
    (hcostQ : (729:ℝ)*(rad:ℝ)^4 ≤ D.thickness^(-loss))
    (hcost : (729:ℝ) ≤ D.thickness^(-loss))
    (HMupper : ∀q,(parentEdges D a (2^c) E q).Nonempty →
      multiplicity ((parentEdges D a (2^c) E q).image (physicalPair h R a level b)) ≤
        D.thickness^(-loss)*depthPower extremalExponent c b)
    (HMlower : ∀q,(parentEdges D a (2^d) E q).Nonempty →
      D.thickness^loss*depthPower extremalExponent d b ≤
        multiplicity ((parentEdges D a (2^d) E q).image (physicalPair h R a level b)))
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty) :
    D.thickness^(2*loss+s*(4+2*extremalExponent))*depthPower extremalExponent m f ≤
      multiplicity ((parentEdges D a (2^m) E p).image (physicalPair h R a level f)) ∧
    multiplicity ((parentEdges D a (2^m) E p).image (physicalPair h R a level f)) ≤
      D.thickness^(-(2*loss+s*(10+extremalExponent)))*depthPower extremalExponent m f := by
  let Ep := parentEdges D a (2^m) E p
  let r := ((2^(f-b):ℕ):ℝ)
  have hd := h.1.2.1
  have hEp : Ep⊆NativeCubicalIncidenceCounts.incidences original := (filter_subset _ _).trans hE
  have hEpR : ∀z∈Ep,z.1∈R := fun z hz => hER z (mem_filter.mp hz).1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hratio : r ≤ D.thickness^(-s) := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgapF
  constructor
  · have hLow := coarser_outer_parent_lower h R E a level m d b hmd hdb
      (D.thickness^loss*depthPower extremalExponent d b)
      (mul_nonneg (Real.rpow_pos_of_pos hd _).le (depthPower_pos _ _ _).le) HMlower p hp
    have hForward := NativeCoarseScaleInterpolation.actual_multiplicity_le h original horiginal ha
      R Ep hEp hEpR level b f hdy hbf hfl
    exact lower_transfer hd hr hratio hcost (NativeSameSourceMultiplicityBalance.multiplicity_nonneg _)
      (lower_menu_power hdy extremalExponent_nonneg hmd hbf hgapD hgapF) hLow hForward
  · have hSubset := NativeLocalMenuInterpolation.parentEdges_subset_ancestor D a E hcm p
    have hAncestor : (parentEdges D a (2^c) E (ancestor m c p)).Nonempty := hp.mono hSubset
    have hPair : HasUniformFibers (parentEdges D a (2^c) E (ancestor m c p)) rad
        (physicalPair h R a level b) := conditioned_uniformity E
      (fun z => parentLabel D a (2^c) z.1) (physicalPair h R a level b) rad hG _
    have hPoint : HasUniformFibers (parentEdges D a (2^c) E (ancestor m c p)) rad
        (fun z => (physicalPair h R a level b z).2) := conditioned_uniformity E
      (fun z => parentLabel D a (2^c) z.1) (physicalPoint h R a level b) rad hX _
    have hOuter := finer_outer_parent_upper h R E a level c m b rad hcm p hPair hPoint
    have hReverse := NativeCoarseScaleReverse.actual_multiplicity_le h original horiginal ha
      R Ep hEp hEpR level b f hdy hbf hfl
    have hTransfer : multiplicity (Ep.image (physicalPair h R a level f)) ≤
        ((729:ℝ)*(rad:ℝ)^4)*r^10*
          multiplicity ((parentEdges D a (2^c) E (ancestor m c p)).image (physicalPair h R a level b)) := by
      calc
        _ ≤ 729*r^10*multiplicity (Ep.image (physicalPair h R a level b)) := hReverse
        _ ≤ 729*r^10*((rad:ℝ)^4*multiplicity
            ((parentEdges D a (2^c) E (ancestor m c p)).image (physicalPair h R a level b))) :=
          mul_le_mul_of_nonneg_left hOuter (by positivity)
        _ = _ := by ring
    exact upper_transfer hd hr hratio (by positivity) hcostQ (depthPower_pos _ _ _).le
      (upper_menu_power hdy extremalExponent_nonneg hcm hbf hgapC)
      (HMupper _ hAncestor) hTransfer

end NativeTwoAxisConditionalTransfer
