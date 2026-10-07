import Theorems.Thm_StickyKakeya4_native_anisotropic_row_count_lower
import Theorems.Thm_StickyKakeya4_native_anisotropic_counts_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeAnisotropicGlobalSourceBridge
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeLocalPairFibers NativeSpatialAngularGeometry NativeCoarseShadingUniformity
open NativeCoarseDirectionThinning NativeJointUniformCoarseRelations
open NativeAnisotropicShortRowGeometry NativeAnisotropicColumnCapacity NativeAnisotropicRowCountLower
open NativeAnisotropicCountsUpper NativeHaloCountTransfer NativeRawShadowPairComparison
open NativeIncidenceMultiplicityTower

/-- Original fine phase-parent paired with a separately binned parent-chart
point. This is neither an isotropic old cube nor a local-source double shadow. -/
def columnPair {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ) (p : Parent)
    (z : Fin n × Index) : Parent × Index :=
  (parentLabel D a (2^f) z.1,
    columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2)

/-- All geometric halo and fixed-R shadow costs are absolute. -/
def comparisonCost : ℝ := ((2401:ℝ)*chargeConstant)^2*((2401:ℝ)*2051^4)

lemma comparisonCost_pos : 0 < comparisonCost := by
  norm_num [comparisonCost,chargeConstant]

lemma image_multiplicity_of_time_counts {X P Q S T : Type*}
    [DecidableEq P] [DecidableEq Q] [DecidableEq S] [DecidableEq T]
    (E : Finset X) (hE : E.Nonempty) (u : X → P × Q) (v : X → S × T)
    (time eps C : ℝ) (htime : 0 < time) (heps : 0 < eps)
    (hil : eps*time*(E.image u).card ≤ C*(E.image v).card)
    (hiu : (E.image v).card ≤ C*time*(E.image u).card)
    (hpl : eps*time*(E.image (fun z => (u z).2)).card ≤ C*(E.image (fun z => (v z).2)).card)
    (hpu : (E.image (fun z => (v z).2)).card ≤ C*time*(E.image (fun z => (u z).2)).card) :
    (eps/C^2)*multiplicity (E.image v) ≤ multiplicity (E.image u) ∧
      multiplicity (E.image u) ≤ (C^2/eps)*multiplicity (E.image v) := by
  have hiap : (0:ℝ)<(E.image u).card := by exact_mod_cast card_pos.mpr (hE.image u)
  have hibp : (0:ℝ)<(E.image v).card := by exact_mod_cast card_pos.mpr (hE.image v)
  have hpap : (0:ℝ)<(E.image (fun z => (u z).2)).card := by exact_mod_cast card_pos.mpr (hE.image _)
  have hpbp : (0:ℝ)<(E.image (fun z => (v z).2)).card := by exact_mod_cast card_pos.mpr (hE.image _)
  have hh := multiplicity_transfer hiap hpap hibp hpbp htime heps hil hiu hpl hpu
  simpa only [NativeIncidenceMultiplicityTower.multiplicity,image_image,Function.comp_def] using hh

/-- Actual Step6 reference comparison with the ORIGINAL GLOBAL fullSource.
This is exactly the source used by HasConditionalTwoScale: the same D/h/R,
with parentEdges only restricting its shading. Actual short-row richness
cancels the time factor2^(f-m) on both pair and point counts. The separate
locally normalized parent double shadow is never identified with this source. -/
theorem queried_global_source_comparison {n level : ℕ} {D : FiniteScaleSource n}
    {eta eta2 a lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hER : ∀z∈E,z.1∈R)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2) (heta2 : 0 ≤ eta2)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hlambda : 0 < lambda)
    (hRich : ∀e,e∈E → D.thickness^eta*(2^level:ℕ)/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E (localPair D a (2^level) e)).card)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta2) ≤ D.thickness^(-c2))
    (f m : ℕ) (hmf : m ≤ f) (hfL : f ≤ level) (hm6 : 6 ≤ m)
    (hwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ))
    (HF : HasUniformFibers E Q2 (fixedPair D a level f f (representative h R a (2^f))))
    (HC : HasUniformFibers E Q2 (fixedPair D a level f m (representative h R a (2^f))))
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty) :
    let F := parentEdges D a (2^m) E p
    let eps := lambda*D.thickness^(c1+3*c2)
    let full := (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource h R a level f F)).toReal
    eps/comparisonCost*full ≤ multiplicity (F.image (columnPair D a m f p)) ∧
      multiplicity (F.image (columnPair D a m f p)) ≤ comparisonCost/eps*full := by
  intro F eps full
  let C : ℝ := 2401*chargeConstant
  let shadow : ℝ := (2401:ℝ)*2051^4
  let time : ℝ := ((2^(f-m):ℕ):ℝ)
  have htime : 0 < time := by dsimp [time]; positivity
  have heps : 0 < eps := mul_pos hlambda (Real.rpow_pos_of_pos h.1.2.1 _)
  have hC : 0 < C := by norm_num [C,chargeConstant]
  have hshadow : 0 < shadow := by norm_num [shadow]
  have h65 : (6655:ℝ) ≤ C := by norm_num [C,chargeConstant]
  have hratio : (64/((2^m:ℕ):ℝ))/(64/((2^f:ℕ):ℝ))=time := by
    rw [dyadic_height_eq m f hmf]
    dsimp only [time]
    field_simp
  have hl := queried_parent_counts_lower h original horiginal ha R E hE hER
    F1 F2 G Q1 Q2 hF1 hG hQ2 hQ1 hGF heta2 hdy hlambda hRich hcost1 hcost2
    f m hmf hfL hm6 hwindow HF HC p hp
  dsimp only at hl
  rw [hratio] at hl
  have hu := parent_counts_upper (a:=a) h m f hmf E p
  have hiu : ((F.image (rawPair D a f)).card:ℝ) ≤
      C*time*(F.image (columnPair D a m f p)).card := by
    have hh : ((F.image (rawPair D a f)).card:ℝ) ≤
        6655*time*(F.image (columnPair D a m f p)).card := by
      dsimp only [F,time,columnPair]
      exact_mod_cast hu.2
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h65 htime.le) (Nat.cast_nonneg _))
  have hpu : ((F.image (fun z => spatialLabel D (2^f) z.2)).card:ℝ) ≤
      C*time*(F.image (fun z => (columnPair D a m f p z).2)).card := by
    have hh : ((F.image (fun z => spatialLabel D (2^f) z.2)).card:ℝ) ≤
        6655*time*(F.image (fun z => (columnPair D a m f p z).2)).card := by
      dsimp only [F,time,columnPair]
      exact_mod_cast hu.1
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h65 htime.le) (Nat.cast_nonneg _))
  have hm := image_multiplicity_of_time_counts F hp (columnPair D a m f p) (rawPair D a f)
    time eps C htime heps hl.2 hiu hl.1 hpu
  have hg := same_R_full_source_multiplicity_comparison h original horiginal ha R F
    ((filter_subset _ _).trans hE) (fun z hz => hER z (mem_filter.mp hz).1) level f hdy hfL
  change eps/(C^2*shadow)*full ≤ _ ∧ _ ≤ (C^2*shadow)/eps*full
  constructor
  · calc
      _ ≤ (eps/(C^2*shadow))*(shadow*multiplicity (F.image (rawPair D a f))) :=
        mul_le_mul_of_nonneg_left hg.1 (by positivity)
      _ = (eps/C^2)*multiplicity (F.image (rawPair D a f)) := by dsimp only [shadow]; ring
      _ ≤ _ := hm.1
  · calc
      _ ≤ (C^2/eps)*multiplicity (F.image (rawPair D a f)) := hm.2
      _ ≤ (C^2/eps)*(shadow*full) := mul_le_mul_of_nonneg_left hg.2 (by positivity)
      _ = _ := by ring

end NativeAnisotropicGlobalSourceBridge
