import Theorems.Thm_StickyKakeya4_native_reference_parent_angular_upper
import Theorems.Thm_StickyKakeya4_native_reference_relative_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeCandidateReferenceAdmission
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeLocalParentSource NativeMiddleWindowBalance
open NativeCubicalIncidenceCounts NativeReferenceParentPopulation NativeReferenceParentAngularUpper
open NativeUnitParentNormalization NativeRelativeCoarseReadback NativeJointUniformCoarseRelations
open NativeFixedCompactKakeyaExponent NativeNormalizedCellAngularMenu SelfUniform
open NativeMiddleGrainParentBudget

/-- Every predetermined middle candidate is admitted on the SAME original
E1. The relative pair and point bounds are decoded from its installed caller
relations; no off-menu admissibility, rank retention, or target bound is assumed.
F remains the actual factor of the enlarged first-stage core. -/
theorem exists_candidate_menu_angular_upper (epsilon window budget : ℝ)
    (hepsilon : 0 < epsilon) (hwindow : 0 < window) (hbudget : 0 < budget) :
    ∃e localEta seedCap delta0 : ℝ,
      0 < e ∧ e ≤ 32*budget/(7*window) ∧ 0 < localEta ∧ 0 < seedCap ∧ 0 < delta0 ∧ delta0 ≤ 1/8 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0 ≤ zeta → eta ≤ seed/8 → zeta ≤ seed/256 → seed ≤ seedCap → D.thickness ≤ delta0 →
      ∀(original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ),
        HasOriginalBackbone D original R a level zeta → 6 ≤ level →
      ∀(E1 : Finset (Fin n × Index)),E1⊆retained original R →
      ∀(F Q G K : ℕ) (stops : Fin G → Fin (level+1)) (relativeDepth : Fin G → Fin K → ℕ),
        (incidences original).card ≤ F*E1.card →
        (∀j x y,x∈E1 → y∈E1 →
          degree (fun _ : Fin n × Index => 1)
            (NativeReferenceRelativeMenu.relations h R a (fun i => middleDepth (stops i).val)
              (fun i j => 2^(relativeDepth i j)) j) E1 x ≤
          Q^2*degree (fun _ : Fin n × Index => 1)
            (NativeReferenceRelativeMenu.relations h R a (fun i => middleDepth (stops i).val)
              (fun i j => 2^(relativeDepth i j)) j) E1 y) →
        (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)) →
      ∀i : Fin G,∀p : Parent,
        (parentEdges D a (2^(middleDepth (stops i).val)) E1 p).Nonempty →
        let m := middleDepth (stops i).val
        let E := parentEdges D a (2^m) E1 p
        IsWangZakharovNativeFiniteInput (source h R E a m p) localEta ∧
        (∀t,(source h R E a m p).line t∈fixedCompactClass) ∧
        ∀j : Fin K,relativeDepth i j ≤ level-m+6 →
          1/((2^(relativeDepth i j):ℕ):ℝ) ≤ (source h R E a m p).thickness^window →
          (source h R E a m p).thickness/(1/((2^(relativeDepth i j):ℕ):ℝ)) ≤
            (source h R E a m p).thickness^window →
        ∀T⊆E,∀q : Index,((angularMenu D a m (2^(relativeDepth i j)) p T q).card:ℝ) ≤
          81*(Q:ℝ)^4*(source h R E a m p).thickness^(-budget)*
            (64/((2^(relativeDepth i j):ℕ):ℝ))^(-extremalExponent-epsilon) := by
  obtain ⟨e,localEta,seedCap,delta0,he,heBound,hLocal,hSeed,hd0,hd01,Hupper⟩ :=
    exists_reference_parent_angular_upper epsilon window budget hepsilon hwindow hbudget
  refine ⟨e,localEta,seedCap,delta0,he,heBound,hLocal,hSeed,hd0,hd01,?_⟩
  intro n D eta zeta seed a h hzeta heta hzseed hseed hsmall original R level HB hlevel E1 hE1
    F Q G K stops relativeDepth hret hMenu hCost i p hp
  obtain ⟨hParent,hRelative⟩ := NativeReferenceRelativeMenu.caller_uniformities h R a
    (fun i => middleDepth (stops i).val) (fun i j => 2^(relativeDepth i j)) E1 Q hMenu i
  have hstop : (stops i).val ≤ level := Nat.le_of_lt_succ (stops i).isLt
  have hm := (candidate_middle_bounds level (stops i).val hlevel hstop).2
  have hsquare := candidate_middle_square level (stops i).val HB.2.1 hstop
  obtain ⟨hS,hSK,Hangles⟩ := Hupper n D eta zeta seed a h hzeta heta hzseed hseed hsmall
    original R level HB E1 hE1 F Q (middleDepth (stops i).val) hm hsquare hret hParent hCost p hp
  refine ⟨hS,hSK,?_⟩
  intro j hj hcoarse hfine T hT q
  have hParentR : (parentLabels D R a (2^(middleDepth (stops i).val)) p).Nonempty := by
    obtain ⟨z,hz⟩ := hp
    obtain ⟨hzE,hzp⟩ := mem_filter.mp hz
    exact ⟨z.1,mem_filter.mpr ⟨(mem_filter.mp (hE1 hzE)).2,hzp⟩⟩
  exact Hangles hParentR (relativeDepth i j) hj hcoarse hfine
    (hRelative p hParentR j).1 (hRelative p hParentR j).2 T hT q

end NativeCandidateReferenceAdmission
