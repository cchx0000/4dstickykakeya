import Theorems.Thm_StickyKakeya4_native_two_axis_power_interpolation
import Theorems.Thm_StickyKakeya4_native_conditional_parent_boundary
import Theorems.Thm_StickyKakeya4_native_coarse_scale_reverse

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeHereditaryConditionalUpper
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeDyadicParentCells NativeJointUniformCoarseRelations
open NativeIncidenceMultiplicityTower NativeConditionalCoarseInterpolation NativeConditionedPairMenu
open NativeTwoAxisPowerInterpolation NativeConditionalParentBoundary NativeEndpointParentBounds

/-- The literal selected parent is a subset of the reference ancestor.
Neither the reference backbone nor its representatives are selected again. -/
lemma parent_subset_reference_ancestor {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (E F : Finset (Fin n × Index)) (hFE : F ⊆ E) {c m : ℕ} (hcm : c ≤ m) (p : Parent) :
    parentEdges D a (2^m) F p ⊆ parentEdges D a (2^c) E (ancestor m c p) := by
  have hh : parentEdges D a (2^m) F p ⊆ parentEdges D a (2^m) E p :=
    filter_subset_filter _ hFE
  exact hh.trans (NativeLocalMenuInterpolation.parentEdges_subset_ancestor D a E hcm p)

lemma active_parent_upper_all {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level c b : ℕ) (U : ℝ) (hU : 0 ≤ U)
    (H : ∀q,(parentEdges D a (2^c) E q).Nonempty →
      multiplicity ((parentEdges D a (2^c) E q).image (physicalPair h R a level b)) ≤ U)
    (q : Parent) :
    multiplicity ((parentEdges D a (2^c) E q).image (physicalPair h R a level b)) ≤ U := by
  by_cases hq : (parentEdges D a (2^c) E q).Nonempty
  · exact H q hq
  · rw [not_nonempty_iff_eq_empty.mp hq]
    simpa only [image_empty,NativeIncidenceMultiplicityTower.multiplicity,card_empty,
      Nat.cast_zero,div_zero] using hU

/-- Both uniformity hypotheses concern the reference E, never its selected
subset F. The output includes empty selected parents. -/
theorem subset_outer_parent_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E F : Finset (Fin n × Index)) (hFE : F ⊆ E) (a : ℝ) (level c m b rad : ℕ)
    (hcm : c ≤ m)
    (hG : HasUniformFibers E rad (conditionedGlobalPair h R a level c b))
    (hX : HasUniformFibers E rad (conditionedGlobalPoint h R a level c b)) (p : Parent) :
    multiplicity ((parentEdges D a (2^m) F p).image (physicalPair h R a level b)) ≤
      (rad:ℝ)^4*multiplicity
        ((parentEdges D a (2^c) E (ancestor m c p)).image (physicalPair h R a level b)) := by
  have hPair : HasUniformFibers (parentEdges D a (2^c) E (ancestor m c p)) rad
      (physicalPair h R a level b) := conditioned_uniformity E
    (fun z => parentLabel D a (2^c) z.1) (physicalPair h R a level b) rad hG _
  have hPoint : HasUniformFibers (parentEdges D a (2^c) E (ancestor m c p)) rad
      (fun z => (physicalPair h R a level b z).2) := conditioned_uniformity E
    (fun z => parentLabel D a (2^c) z.1) (physicalPoint h R a level b) rad hX _
  exact subset_image_multiplicity _ _
    (parent_subset_reference_ancestor D a E F hFE hcm p) _ rad hPair hPoint

/-- Hereditary far-pair upper interpolation on the one reference incidence
set. Physical reversal is applied to the selected F-parent, and the reference
menu image controls it through the installed reference uniformity. -/
theorem far_pair_upper {n : ℕ} {D : FiniteScaleSource n} {eta a loss s kappa : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E F : Finset (Fin n × Index)) (hFE : F ⊆ E)
    (hE : E ⊆ NativeCubicalIncidenceCounts.incidences original) (hER : ∀z∈E,z.1∈R)
    (level c m b f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hcm : c ≤ m) (hbf : b ≤ f) (hfl : f ≤ level)
    (hgapC : ((m-c:ℕ):ℝ) ≤ s*level) (hgapF : ((f-b:ℕ):ℝ) ≤ s*level)
    (hk : 0 ≤ kappa) (rad : ℕ)
    (hG : HasUniformFibers E rad (conditionedGlobalPair h R a level c b))
    (hX : HasUniformFibers E rad (conditionedGlobalPoint h R a level c b))
    (hcostQ : (729:ℝ)*(rad:ℝ)^4 ≤ D.thickness^(-loss))
    (HM : ∀q,(parentEdges D a (2^c) E q).Nonempty →
      multiplicity ((parentEdges D a (2^c) E q).image (physicalPair h R a level b)) ≤
        D.thickness^(-loss)*depthPower kappa c b) (p : Parent) :
    multiplicity ((parentEdges D a (2^m) F p).image (physicalPair h R a level f)) ≤
      D.thickness^(-(2*loss+s*(10+kappa)))*depthPower kappa m f := by
  let Fp := parentEdges D a (2^m) F p
  let r := ((2^(f-b):ℕ):ℝ)
  have hd := h.1.2.1
  have hFp : Fp ⊆ NativeCubicalIncidenceCounts.incidences original :=
    (filter_subset _ _).trans (hFE.trans hE)
  have hFpR : ∀z∈Fp,z.1∈R := fun z hz => hER z (hFE (mem_filter.mp hz).1)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hratio : r ≤ D.thickness^(-s) := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgapF
  have hOuter := subset_outer_parent_upper h R E F hFE a level c m b rad hcm hG hX p
  have hReverse := NativeCoarseScaleReverse.actual_multiplicity_le h original horiginal ha
    R Fp hFp hFpR level b f hdy hbf hfl
  have hTransfer : multiplicity (Fp.image (physicalPair h R a level f)) ≤
      ((729:ℝ)*(rad:ℝ)^4)*r^10*
        multiplicity ((parentEdges D a (2^c) E (ancestor m c p)).image (physicalPair h R a level b)) := by
    calc
      _ ≤ 729*r^10*multiplicity (Fp.image (physicalPair h R a level b)) := hReverse
      _ ≤ 729*r^10*((rad:ℝ)^4*multiplicity
          ((parentEdges D a (2^c) E (ancestor m c p)).image (physicalPair h R a level b))) :=
        mul_le_mul_of_nonneg_left hOuter (by positivity)
      _ = _ := by ring
  exact upper_transfer hd hr hratio (by positivity) hcostQ (depthPower_pos _ _ _).le
    (upper_menu_power hdy hk hcm hbf hgapC)
    (active_parent_upper_all h R E a level c b _
      (mul_nonneg (Real.rpow_pos_of_pos hd _).le (depthPower_pos _ _ _).le) HM _) hTransfer

/-- The exact six-dimensional upper is valid without nonemptiness or
uniformity, including every literal restriction of a reference core. -/
theorem conditional_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (F : Finset (Fin n × Index)) (a : ℝ) (level m f : ℕ) (hmf : m ≤ f) (p : Parent) :
    multiplicity ((parentEdges D a (2^m) F p).image (physicalPair h R a level f)) ≤
      (((2^(f-m):ℕ):ℝ)^6) := by
  have hcard := active_descendants_card_le D a F hmf p
  have he : ((parentEdges D a (2^m) F p).image (physicalPair h R a level f)).image Prod.fst =
      (parentEdges D a (2^m) F p).image (fun z => parentLabel D a (2^f) z.1) := by
    simp only [image_image,Function.comp_def,physicalPair_parent]
  have hu := multiplicity_le_tube_card
    ((parentEdges D a (2^m) F p).image (physicalPair h R a level f))
  rw [he] at hu
  exact hu.trans (by exact_mod_cast hcard)

theorem short_gap_upper {n : ℕ} {D : FiniteScaleSource n} {eta s kappa : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (F : Finset (Fin n × Index)) (a : ℝ) (level m f : ℕ) (hmf : m ≤ f)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hk : 0 ≤ kappa)
    (hgap : ((f-m:ℕ):ℝ) ≤ s*level) (p : Parent) :
    multiplicity ((parentEdges D a (2^m) F p).image (physicalPair h R a level f)) ≤
      D.thickness^(-6*s)*depthPower kappa m f := by
  let r := ((2^(f-m):ℕ):ℝ)
  have hr : 1 ≤ r := by
    dsimp [r]
    exact_mod_cast Nat.one_le_pow (f-m) 2 (by norm_num)
  have hgapR : r ≤ D.thickness^(-s) := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgap
  have hpow := nat_power_cost h.1.2.1 (zero_le_one.trans hr) hgapR 6
  have hkr : 1 ≤ r^kappa := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hr hk
  rw [depthPower_eq_nat hmf]
  calc
    _ ≤ r^6 := conditional_upper h R F a level m f hmf p
    _ ≤ D.thickness^(-6*s) := by
      simpa only [Nat.cast_ofNat,show -s*(6:ℝ) = -6*s by ring] using hpow
    _ ≤ _ := le_mul_of_one_le_right (Real.rpow_pos_of_pos h.1.2.1 _).le hkr

lemma depthPower_mono {kappa : ℝ} (hk : 0 ≤ kappa) {m d b f : ℕ}
    (hmd : m ≤ d) (hbf : b ≤ f) : depthPower kappa d b ≤ depthPower kappa m f := by
  unfold depthPower
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  have hmdR : (m:ℝ) ≤ d := by exact_mod_cast hmd
  have hbfR : (b:ℝ) ≤ f := by exact_mod_cast hbf
  nlinarith

/-- Boundary upper propagation is performed on the selected set F itself.
The supplied child bounds can be the hereditary middle bounds derived from
the one reference core. Empty parents need no separate branch. -/
theorem boundary_pair_upper {n : ℕ} {D : FiniteScaleSource n} {eta a loss s kappa : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (F : Finset (Fin n × Index))
    (hF : F ⊆ NativeCubicalIncidenceCounts.incidences original) (hFR : ∀z∈F,z.1∈R)
    (level m d b f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hmd : m ≤ d) (hdb : d ≤ b) (hbf : b ≤ f) (hfl : f ≤ level)
    (hgapD : ((d-m:ℕ):ℝ) ≤ s*level) (hgapF : ((f-b:ℕ):ℝ) ≤ s*level)
    (hk : 0 ≤ kappa) (hconstant : (729:ℝ) ≤ D.thickness^(-loss))
    (HM : ∀q,multiplicity ((parentEdges D a (2^d) F q).image (physicalPair h R a level b)) ≤
      D.thickness^(-loss)*depthPower kappa d b) (p : Parent) :
    multiplicity ((parentEdges D a (2^m) F p).image (physicalPair h R a level f)) ≤
      D.thickness^(-(2*loss+16*s))*depthPower kappa m f := by
  have hd := h.1.2.1
  let rD := ((2^(d-m):ℕ):ℝ)
  let rF := ((2^(f-b):ℕ):ℝ)
  have hrD : 0 ≤ rD := by dsimp [rD]; positivity
  have hrF : 0 ≤ rF := by dsimp [rF]; positivity
  have hratioD : rD ≤ D.thickness^(-s) := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgapD
  have hratioF : rF ≤ D.thickness^(-s) := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgapF
  have hpowD := nat_power_cost hd hrD hratioD 6
  have hpowF := nat_power_cost hd hrF hratioF 10
  have hPower := depthPower_mono hk hmd hbf
  let Fp := parentEdges D a (2^m) F p
  have hFp : Fp ⊆ NativeCubicalIncidenceCounts.incidences original := (filter_subset _ _).trans hF
  have hFpR : ∀z∈Fp,z.1∈R := fun z hz => hFR z (mem_filter.mp hz).1
  have hP := (depthPower_pos kappa m f).le
  have hUpper := coarser_outer_parent_upper h R F a level m d b hmd hdb
    (D.thickness^(-loss)*depthPower kappa d b)
    (mul_nonneg (Real.rpow_pos_of_pos hd _).le (depthPower_pos _ _ _).le) (fun q _hq => HM q) p
  have hReverse := NativeCoarseScaleReverse.actual_multiplicity_le h original horiginal ha
    R Fp hFp hFpR level b f hdy hbf hfl
  have hCost : (729:ℝ)*rF^10*rD^6 ≤ D.thickness^(-(loss+16*s)) := by
    calc
      _ ≤ (D.thickness^(-loss)*D.thickness^(-s*(10:ℝ)))*D.thickness^(-s*(6:ℝ)) :=
        mul_le_mul (mul_le_mul hconstant hpowF (pow_nonneg hrF 10)
          (Real.rpow_pos_of_pos hd _).le) hpowD (pow_nonneg hrD 6) (by positivity)
      _ = _ := by rw [←Real.rpow_add hd,←Real.rpow_add hd]; congr 1; ring
  calc
    _ ≤ 729*rF^10*multiplicity (Fp.image (physicalPair h R a level b)) := hReverse
    _ ≤ 729*rF^10*(rD^6*(D.thickness^(-loss)*depthPower kappa d b)) :=
      mul_le_mul_of_nonneg_left hUpper (by positivity)
    _ ≤ 729*rF^10*(rD^6*(D.thickness^(-loss)*depthPower kappa m f)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPower (by positivity))
          (pow_nonneg hrD 6)) (by positivity)
    _ = (729*rF^10*rD^6)*(D.thickness^(-loss)*depthPower kappa m f) := by ring
    _ ≤ D.thickness^(-(loss+16*s))*(D.thickness^(-loss)*depthPower kappa m f) :=
      mul_le_mul_of_nonneg_right hCost (mul_nonneg (Real.rpow_pos_of_pos hd _).le hP)
    _ = _ := by rw [←mul_assoc,←Real.rpow_add hd]; congr 2; ring

end NativeHereditaryConditionalUpper
