import Theorems.Thm_StickyKakeya4_native_raw_shadow_point_comparison
import Theorems.Thm_StickyKakeya4_native_coarse_scale_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

noncomputable section
namespace NativeRawShadowPairComparison
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeOriginalPaddedCells
open NativeCoarsePointMultiplicity NativeCoarseShadingCapacity NativeCoarseScaleInterpolation
open NativeRawShadowPointComparison NativeSpatialAngularGeometry

/-- Literal spatial64/2^f cells, with the unchanged original fine parent. -/
def rawPair {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (f : ℕ)
    (z : Fin n × Index) : Parent × Index :=
  (parentLabel D a (2^f) z.1,spatialLabel D (2^f) z.2)

/-- On one fixed first-coordinate fiber, counting pairs counts just points. -/
lemma pair_image_card_of_constant {X P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (E : Finset X) (p : X → P) (q : X → Q) (v : P)
    (hp : ∀z∈E,p z=v) :
    (E.image (fun z => (p z,q z))).card=(E.image q).card := by
  have he : E.image (fun z => (p z,q z))=(E.image q).image (fun w => (v,w)) := by
    rw [image_image]
    apply image_congr
    intro z hz
    exact Prod.ext (hp z hz) rfl
  rw [he,card_image_of_injective _ (fun _ _ hh => congrArg Prod.snd hh)]

/-- A point-image comparison valid on every subset lifts without any loss
to pairs having the same first-coordinate map. -/
theorem pair_image_card_le_of_point_comparison {X P Q S : Type*}
    [DecidableEq P] [DecidableEq Q] [DecidableEq S]
    (E : Finset X) (p : X → P) (q : X → Q) (s : X → S) (C : ℕ)
    (H : ∀F⊆E,(F.image q).card≤C*(F.image s).card) :
    (E.image (fun z => (p z,q z))).card≤C*(E.image (fun z => (p z,s z))).card := by
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images E
    (fun z => (p z,q z)) (fun z => (p z,s z)) (C:ℝ) (by
      intro v _hv
      let F := E.filter (fun z => (p z,s z)=v)
      have hp : ∀z∈F,p z=v.1 := by
        intro z hz
        exact congrArg Prod.fst (mem_filter.mp hz).2
      have hs : F.image s⊆{v.2} := by
        intro w hw
        obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
        exact mem_singleton.mpr (congrArg Prod.snd (mem_filter.mp hz).2)
      have hc : (F.image s).card≤1 := by
        simpa only [card_singleton] using card_le_card hs
      have hf : (F.image (fun z => (p z,q z))).card≤C := by
        rw [pair_image_card_of_constant F p q v.1 hp]
        exact (H F (filter_subset _ _)).trans (by simpa only [mul_one] using Nat.mul_le_mul_left C hc)
      exact_mod_cast hf)
  exact_mod_cast hh

/-- Both occupied pair images of any unchanged original incidence subset
are comparable, using the SAME original R and its fixed representatives. -/
theorem same_R_pair_image_card_comparison {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : f≤level) :
    (E.image (actualPair h R a level f)).card≤2401*(E.image (rawPair D a f)).card ∧
    (E.image (rawPair D a f)).card≤2051^4*(E.image (actualPair h R a level f)).card := by
  let q := pointLabel D a (2^f) (NativeCoarseDyadicShading.block level f)
    (NativeCoarseDirectionThinning.representative h R a (2^f))
  have H (F : Finset (Fin n × Index)) (hF : F⊆E) :
      (F.image q).card≤2401*(F.image (fun z => spatialLabel D (2^f) z.2)).card ∧
      (F.image (fun z => spatialLabel D (2^f) z.2)).card≤2051^4*(F.image q).card :=
    same_R_point_image_card_comparison h original horiginal ha R F (hF.trans hE)
      (fun z hz => hR z (hF hz)) level f hdy hf
  constructor
  · exact pair_image_card_le_of_point_comparison E (fun z => parentLabel D a (2^f) z.1)
      q (fun z => spatialLabel D (2^f) z.2) 2401 (fun F hF => (H F hF).1)
  · exact pair_image_card_le_of_point_comparison E (fun z => parentLabel D a (2^f) z.1)
      (fun z => spatialLabel D (2^f) z.2) q (2051^4) (fun F hF => (H F hF).2)

/-- Numerator and support comparisons combine multiplicatively. Empty
underlying incidence sets give zero multiplicity on both sides. -/
theorem image_multiplicity_le_of_card_bounds {X P Q S T : Type*}
    [DecidableEq P] [DecidableEq Q] [DecidableEq S] [DecidableEq T]
    (E : Finset X) (u : X → P × Q) (v : X → S × T) (A B : ℕ)
    (hpair : (E.image u).card≤A*(E.image v).card)
    (hpoint : (E.image (fun z => (v z).2)).card≤B*(E.image (fun z => (u z).2)).card) :
    NativeIncidenceMultiplicityTower.multiplicity (E.image u)≤
      (A:ℝ)*(B:ℝ)*NativeIncidenceMultiplicityTower.multiplicity (E.image v) := by
  have hcard : ((E.image u).card:ℝ)≤(A:ℝ)*((E.image v).card:ℝ) := by exact_mod_cast hpair
  have hsupp : ((E.image (fun z => (v z).2)).card:ℝ)≤
      (B:ℝ)*((E.image (fun z => (u z).2)).card:ℝ) := by exact_mod_cast hpoint
  by_cases hEn : E.Nonempty
  · have hu : (0:ℝ)<(E.image (fun z => (u z).2)).card := by
      exact_mod_cast card_pos.mpr (hEn.image _)
    have hv : (0:ℝ)<(E.image (fun z => (v z).2)).card := by
      exact_mod_cast card_pos.mpr (hEn.image _)
    simp only [NativeIncidenceMultiplicityTower.multiplicity,image_image,Function.comp_def]
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hu hv).mpr
    calc
      _ ≤ ((A:ℝ)*((E.image v).card:ℝ))*((E.image (fun z => (v z).2)).card:ℝ) :=
        mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
      _ ≤ ((A:ℝ)*((E.image v).card:ℝ))*
          ((B:ℝ)*((E.image (fun z => (u z).2)).card:ℝ)) :=
        mul_le_mul_of_nonneg_left hsupp (by positivity)
      _ = _ := by ring
  · rw [not_nonempty_iff_eq_empty.mp hEn]
    simp [NativeIncidenceMultiplicityTower.multiplicity]

/-- Raw and actual multiplicities of the SAME original incidences differ
by at most the universal product2401*2051^4, including the empty case. -/
theorem same_R_multiplicity_comparison {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : f≤level) :
    NativeIncidenceMultiplicityTower.multiplicity (E.image (actualPair h R a level f))≤
      ((2401:ℝ)*2051^4)*NativeIncidenceMultiplicityTower.multiplicity (E.image (rawPair D a f)) ∧
    NativeIncidenceMultiplicityTower.multiplicity (E.image (rawPair D a f))≤
      ((2401:ℝ)*2051^4)*NativeIncidenceMultiplicityTower.multiplicity (E.image (actualPair h R a level f)) := by
  have hp := same_R_pair_image_card_comparison h original horiginal ha R E hE hR level f hdy hf
  have hq := same_R_point_image_card_comparison h original horiginal ha R E hE hR level f hdy hf
  constructor
  · have hh := image_multiplicity_le_of_card_bounds E (actualPair h R a level f)
      (rawPair D a f) 2401 (2051^4) hp.1 hq.2
    simpa only [Nat.cast_ofNat,Nat.cast_pow] using hh
  · have hh := image_multiplicity_le_of_card_bounds E (rawPair D a f)
      (actualPair h R a level f) (2051^4) 2401 hp.2 hq.1
    simpa only [Nat.cast_ofNat,Nat.cast_pow,mul_comm] using hh

/-- Exact original-global fullSource readback. In particular, E may itself
be an outer parentEdges subset; D, h, R and the global representatives stay
unchanged and no locally normalized parent source is substituted. -/
theorem same_R_full_source_multiplicity_comparison {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : f≤level) :
    (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level f E)).toReal≤
      ((2401:ℝ)*2051^4)*NativeIncidenceMultiplicityTower.multiplicity (E.image (rawPair D a f)) ∧
    NativeIncidenceMultiplicityTower.multiplicity (E.image (rawPair D a f))≤
      ((2401:ℝ)*2051^4)*
        (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level f E)).toReal := by
  rw [full_source_multiplicity_real h R a level f E hR]
  exact same_R_multiplicity_comparison h original horiginal ha R E hE hR level f hdy hf

end NativeRawShadowPairComparison
