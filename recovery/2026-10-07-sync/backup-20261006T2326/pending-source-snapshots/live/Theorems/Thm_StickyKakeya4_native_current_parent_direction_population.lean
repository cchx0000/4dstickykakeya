/- UNVERIFIED actual conditional parent-direction reader. All labels are
on the unchanged original source. No common tangent-Phi premise is used. -/
import Theorems.Thm_StickyKakeya4_native_joint_cell_phase_population

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeCurrentParentDirectionPopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeGenericReferenceData NativeExtraQueriedRankConfiguration NativeConditionalReferenceMenu
open NativeSourceCoherenceEngine NativePaidMeshAngularUpper NativePaidMeshAngularBounds
open NativeFixedCompactKakeyaExponent NativeLocalParentSource NativeOriginalParentDensityCore
open NativeMiddleGrainParentBudget NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu
open NativeActualAngularParentCount NativeRelativeParentLabels NativeLocalParentGeometry

/-- A literal relative phase class lies in a slope ball. The estimate
comes from its actual three floor coordinates, with no direction certificate. -/
theorem same_relative_parent_ball {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N M : ℕ) (hM : 0 < M) (p : Parent) (i j : Fin n)
    (heq : relativeLabel D a N p M i = relativeLabel D a N p M j) :
    dist (localSlope D N p i) (localSlope D N p j) ≤ 64 / (M : ℝ) := by
  have hcoord (v : Fin 3) : |localSlope D N p i v - localSlope D N p j v| ≤ 1/(M:ℝ) := by
    apply NativeNormalizedParentCarrierMetric.same_floor_mul_close _ _ M hM
    have hv := congrFun (congrArg Prod.fst heq) v
    simpa only [relativeLabel, slope_line] using hv
  let w := localSlope D N p i - localSlope D N p j
  have hs (v : Fin 3) : (localSlope D N p i v - localSlope D N p j v)^2 ≤ (1/(M:ℝ))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcoord v) 2
  have hsq : ‖w‖^2 ≤ 3*(1/(M:ℝ))^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [w, PiLp.sub_apply, Fin.sum_univ_three]
    linarith only [hs 0, hs 1, hs 2]
  have hnonneg : 0 ≤ 1/(M:ℝ) := by positivity
  have hw := norm_nonneg w
  rw [dist_eq_norm]
  change ‖w‖ ≤ 64/(M:ℝ)
  rw [show (64:ℝ)/(M:ℝ)=64*(1/(M:ℝ)) by ring]
  nlinarith only [hsq, hnonneg, hw, sq_nonneg (1/(M:ℝ))]

lemma dyadic_radius_antitone {a b : ℕ} (hab : a ≤ b) :
    (64 : ℝ)/((2^b : ℕ) : ℝ) ≤ 64/((2^a : ℕ) : ℝ) := by
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hab

/-- The radius clipped to the fine query pays no extra power at the
bottom endpoint: tau is at least the actual final tube thickness. -/
lemma clipped_radius_ratio (s u : ℕ) (hsu : s ≤ u+3) :
    ((64 : ℝ)/((2^(min (s+9) (u+9)) : ℕ) : ℝ)) /
        (64/((2^(u+9) : ℕ) : ℝ)) ≤
      (64/((2^(s+9) : ℕ) : ℝ)) / (64/((2^(u+12) : ℕ) : ℝ)) := by
  by_cases hsu' : s ≤ u
  · rw [min_eq_left (by omega : s+9 ≤ u+9)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (dyadic_radius_antitone (by omega : u+9 ≤ u+12))
  · rw [min_eq_right (by omega : u+9 ≤ s+9), div_self (by positivity)]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [one_mul] using dyadic_radius_antitone (by omega : s+9 ≤ u+12)

/-- Count final phase parents inside ONE actual coarser tube parent and
ONE fine spatial query cell. The fine query has angular side Delta and
physical radius 8Delta. The coarser-parent ball is derived internally. -/
theorem from_reference (K : ℕ) (amin loss seedCap deltaUpper : ℝ)
    (Hupper : HasUpperEngine K amin loss seedCap deltaUpper)
    {n : ℕ} (D : FiniteScaleSource n) (eta zeta seed tau e : ℝ)
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau) (L g : ℕ)
    (heta : 0 ≤ eta) (hzeta : 0 ≤ zeta) (hetaSeed : eta ≤ seed/8)
    (hzseed : zeta ≤ seed/256) (hseed : seed ≤ seedCap) (hsmall : D.thickness ≤ deltaUpper)
    (ref : Reference h tau htau seed e zeta L g)
    (Hcaller : HasCallerUniformities ref (factory g K))
    (i : Fin (g+1)) (hstop : 6 ≤ (ref.schedule i).val)
    (m : ℕ) (hm : m = middleDepth (ref.schedule i).val)
    (u s : ℕ) (_hs : 6 ≤ s) (hsu : s ≤ u+3) (hum : u+9 ≤ m+6)
    (r power : ℝ) (hr : 0 < r) (hrscale : r ≤ D.thickness^power) (hpower : amin ≤ power)
    (hdelta : 64*D.thickness ≤ r^2) (hMiddle : 3072*r ≤ (64/((2^m:ℕ):ℝ))^2)
    (p q : Parent) (E : Finset (Fin n × Index)) (hE : E ⊆ ref.E1)
    (hParent : ∀ z ∈ E, parentLabel D ref.a (2^m) z.1 = p)
    (hCoarse : ∀ z ∈ E, relativeLabel D ref.a (2^m) p (2^(s+9)) z.1 = q)
    (cell : Index) (hCell : ∀ z ∈ E, physicalCell D ref.a (2^m) (2^(u+9)) p z.2 = cell)
    (localEta profile : ℝ)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h ref.R ref.E1 ref.a m p) localEta)
    (hbudget : (64 : ℝ)^3 * (source h ref.R ref.E1 ref.a m p).thickness ^ profile ≤ D.thickness ^ zeta)
    (hmb : m + (u+12) ≤ ref.level) :
    ((E.image (fun z => relativeLabel D ref.a (2^m) p (2^(u+12)) z.1)).card : ℝ) ≤
      ((5832*130^3) * meshAngularConstant *
        (source h ref.R ref.E1 ref.a m p).thickness ^ (-profile) * r^(-loss)) *
        ((64/((2^(s+9):ℕ):ℝ))/(64/((2^(u+12):ℕ):ℝ)))^extremalExponent := by
  by_cases hEn : E.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hEn]
    simp only [image_empty, card_empty, Nat.cast_zero]
    have heps := hReferenceNative.1.2.1
    have hMC : 0 ≤ meshAngularConstant := by
      norm_num [meshAngularConstant, NativeSameSourceConditionalAngularUpper.conditionalConstant]
    positivity
  obtain ⟨z0, hz0⟩ := hEn
  let center := localSlope D (2^m) p z0.1
  let t := min (s+9) (u+9)
  have ht : 6 ≤ t := by dsimp only [t]; omega
  have htf : t ≤ u+9 := min_le_right _ _
  have hBall (z : Fin n × Index) (hz : z ∈ E) :
      dist (localSlope D (2^m) p z.1) center ≤ 64/((2^t:ℕ):ℝ) := by
    exact (same_relative_parent_ball D ref.a (2^m) (2^(s+9)) (by positivity) p z.1 z0.1
      ((hCoarse z hz).trans (hCoarse z0 hz0).symm)).trans
        (dyadic_radius_antitone (min_le_left _ _))
  have hBallEq : ballEdges D (2^m) p E center (64/((2^t:ℕ):ℝ)) = E := by
    exact filter_eq_self.mpr hBall
  let I := E.image Prod.fst
  have hI : I ⊆ parentLabels D ref.R ref.a (2^m) p := by
    intro j hj
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hj
    have hR := ((retained_spec ref.original ref.R z).mp (ref.core.1 (hE hz))).1
    exact (mem_parentLabels D ref.R ref.a (2^m) p z.1).mpr ⟨hR, hParent z hz⟩
  have hphase := same_original_parent_count h ref.original ref.R ref.level ref.backbone ref.E1
    m u hmb p hReferenceNative hbudget I hI
  simp only [I, image_image, Function.comp_apply] at hphase
  have H := Hupper n D eta zeta seed tau e h htau L g heta hzeta hetaSeed hzseed hseed hsmall
    ref Hcaller i hstop
  rw [← hm] at H
  have hupper := (H (u+9) (by omega) hum r power hr hrscale hpower hdelta hMiddle
    p E hE hParent cell hCell).2 t ht htf center
  rw [hBallEq] at hupper
  have hratio := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤
      (64/((2^t:ℕ):ℝ))/(64/((2^(u+9):ℕ):ℝ)))
    (clipped_radius_ratio s u hsu) extremalExponent_nonneg
  have hMC : 0 ≤ meshAngularConstant := by
    norm_num [meshAngularConstant, NativeSameSourceConditionalAngularUpper.conditionalConstant]
  have heps := hReferenceNative.1.2.1
  calc
    _ ≤ (5832*130^3 : ℝ) * (source h ref.R ref.E1 ref.a m p).thickness ^ (-profile) *
        (E.image (fun z => angularCell D (2^m) (2^(u+9)) p z.1)).card := hphase
    _ ≤ (5832*130^3 : ℝ) * (source h ref.R ref.E1 ref.a m p).thickness ^ (-profile) *
        (meshAngularConstant*r^(-loss)*
          ((64/((2^t:ℕ):ℝ))/(64/((2^(u+9):ℕ):ℝ)))^extremalExponent) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ ≤ (5832*130^3 : ℝ) * (source h ref.R ref.E1 ref.a m p).thickness ^ (-profile) *
        (meshAngularConstant*r^(-loss)*
          ((64/((2^(s+9):ℕ):ℝ))/(64/((2^(u+12):ℕ):ℝ)))^extremalExponent) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hratio (mul_nonneg hMC (by positivity))) (by positivity)
    _ = _ := by ring

/-- A prepared base cell meets at most8^4 fine query cells. This gives
the conditional direction population for an entire merged point fiber
once its actual pre-third base-cell support readback is applied. -/
theorem from_reference_base_cell (K : ℕ) (amin loss seedCap deltaUpper : ℝ)
    (Hupper : HasUpperEngine K amin loss seedCap deltaUpper)
    {n : ℕ} (D : FiniteScaleSource n) (eta zeta seed tau e : ℝ)
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau) (L g : ℕ)
    (heta : 0 ≤ eta) (hzeta : 0 ≤ zeta) (hetaSeed : eta ≤ seed/8)
    (hzseed : zeta ≤ seed/256) (hseed : seed ≤ seedCap) (hsmall : D.thickness ≤ deltaUpper)
    (ref : Reference h tau htau seed e zeta L g)
    (Hcaller : HasCallerUniformities ref (factory g K))
    (i : Fin (g+1)) (hstop : 6 ≤ (ref.schedule i).val)
    (m : ℕ) (hm : m = middleDepth (ref.schedule i).val)
    (u s : ℕ) (hs : 6 ≤ s) (hsu : s ≤ u+3) (hum : u+9 ≤ m+6)
    (r power : ℝ) (hr : 0 < r) (hrscale : r ≤ D.thickness^power) (hpower : amin ≤ power)
    (hdelta : 64*D.thickness ≤ r^2) (hMiddle : 3072*r ≤ (64/((2^m:ℕ):ℝ))^2)
    (p q : Parent) (E : Finset (Fin n × Index)) (hE : E ⊆ ref.E1)
    (hParent : ∀ z ∈ E, parentLabel D ref.a (2^m) z.1 = p)
    (hCoarse : ∀ z ∈ E, relativeLabel D ref.a (2^m) p (2^(s+9)) z.1 = q)
    (baseCell : Index)
    (hBase : ∀ z ∈ E, physicalCell D ref.a (2^m) (2^(u+6)) p z.2 = baseCell)
    (localEta profile : ℝ)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h ref.R ref.E1 ref.a m p) localEta)
    (hbudget : (64 : ℝ)^3 * (source h ref.R ref.E1 ref.a m p).thickness ^ profile ≤ D.thickness ^ zeta)
    (hmb : m + (u+12) ≤ ref.level) :
    ((E.image (fun z => relativeLabel D ref.a (2^m) p (2^(u+12)) z.1)).card : ℝ) ≤
      ((8:ℝ)^4 * (5832*130^3) * meshAngularConstant *
        (source h ref.R ref.E1 ref.a m p).thickness ^ (-profile) * r^(-loss)) *
        ((64/((2^(s+9):ℕ):ℝ))/(64/((2^(u+12):ℕ):ℝ)))^extremalExponent := by
  let B : ℝ := ((5832*130^3) * meshAngularConstant *
      (source h ref.R ref.E1 ref.a m p).thickness ^ (-profile) * r^(-loss)) *
      ((64/((2^(s+9):ℕ):ℝ))/(64/((2^(u+12):ℕ):ℝ)))^extremalExponent
  let cellMap := fun z : Fin n × Index => physicalCell D ref.a (2^m) (2^(u+9)) p z.2
  have hcount := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images E
    (fun z => relativeLabel D ref.a (2^m) p (2^(u+12)) z.1) cellMap B (by
      intro cell _hcell
      exact from_reference K amin loss seedCap deltaUpper Hupper D eta zeta seed tau e h htau L g
        heta hzeta hetaSeed hzseed hseed hsmall ref Hcaller i hstop m hm u s hs hsu hum
        r power hr hrscale hpower hdelta hMiddle p q (E.filter (fun z => cellMap z=cell))
        ((filter_subset _ _).trans hE)
        (fun z hz => hParent z (mem_filter.mp hz).1)
        (fun z hz => hCoarse z (mem_filter.mp hz).1) cell
        (fun _ hz => (mem_filter.mp hz).2) localEta profile hReferenceNative hbudget hmb)
  have hlabels := physicalCell_refinement_card D ref.a (2^m) (2^(u+6)) (by positivity) p
    (E.image Prod.snd) baseCell (by
      intro k hk
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
      exact hBase z hz)
  have he : (8:ℕ)*2^(u+6)=2^(u+9) := by
    rw [show u+9=(u+6)+3 by omega, pow_add]
    norm_num [Nat.mul_comm]
  rw [he] at hlabels
  simp only [image_image, Function.comp_apply] at hlabels
  have hlabelsR : ((E.image cellMap).card : ℝ) ≤ (8:ℝ)^4 := by exact_mod_cast hlabels
  have heps := hReferenceNative.1.2.1
  have hMC : 0 ≤ meshAngularConstant := by
    norm_num [meshAngularConstant, NativeSameSourceConditionalAngularUpper.conditionalConstant]
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  calc
    _ ≤ B * (E.image cellMap).card := hcount
    _ ≤ B * (8:ℝ)^4 := mul_le_mul_of_nonneg_left hlabelsR hB
    _ = _ := by dsimp only [B]; ring

end NativeCurrentParentDirectionPopulation
