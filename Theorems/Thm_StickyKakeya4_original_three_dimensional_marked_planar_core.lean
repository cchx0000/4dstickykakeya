import Theorems.Thm_StickyKakeya4_original_three_dimensional_regularized_marked_slice
import Theorems.Thm_StickyKakeya4_original_three_dimensional_unit_normals
import Theorems.Thm_StickyKakeya4_original_three_dimensional_planar_box_projection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalMarkedPlanarCore
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalDirectionGrid OriginalThreeDimensionalHeavySliceGraph
open OriginalThreeDimensionalUnitSlabs OriginalThreeDimensionalUnitNormals
open OriginalThreeDimensionalSliceMaximizer OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalPairEnergy OriginalThreeDimensionalExpandedSliceMultiplicity
open NativeOriginalConcentratedPairGraph OriginalThreeDimensionalMarkedSliceIncidences
open OriginalThreeDimensionalRegularizedMarkedSlice OriginalThreeDimensionalLiteralSlabCover
open OriginalThreeDimensionalSlabProjection OriginalThreeDimensionalProjectionCells
open OriginalThreeDimensionalWeightedPlanarProjection OriginalThreeDimensionalPlanarBoxProjection
open OriginalFiniteCellWeights PlanarStripIntersection

def profileCoefficient (P : Finset Point3) (G : Finset Pair3)
    (rho Delta K degree : ℝ) (N : ℕ) : ℝ :=
  8*energyBudget P rho Delta K N/(degree*G.card)

def densityCoefficient (P : Finset Point3) (G : Finset Pair3)
    (rho Delta K degree : ℝ) (N : ℕ) : ℝ :=
  (degree*G.card)/(8*energyBudget P rho Delta K N)

def selectedOffset (rho : ℝ) (s : SliceLabel) : ℝ := rho*s.2/normalLength rho s.1

lemma original_slice_energyBudget_pos (P : Finset Point3) (rho Delta K : ℝ) (N : ℕ)
    (hP : P.Nonempty) (hrho : 0<rho) (hDelta : 0<Delta) (hK : 0<K) :
    0<energyBudget P rho Delta K N := by
  have hp : (0:ℝ)<P.card := by exact_mod_cast hP.card_pos
  unfold energyBudget
  positivity

lemma original_profile_coefficient_formula (P : Finset Point3) (G : Finset Pair3)
    (rho Delta K degree : ℝ) (N : ℕ) :
    profileCoefficient P G rho Delta K degree N=
      23040000*Delta^2*((N:ℝ)+1)*K*(P.card : ℝ)^2/(rho^3*(degree*G.card)) := by
  simp only [profileCoefficient,energyBudget,div_eq_mul_inv,mul_inv_rev]
  ring

lemma original_enlarged_slice_unit_slab (P : Finset Point3) (rho Delta : ℝ)
    (s : SliceLabel) (x : Point3) (hx : x∈enlargedSlice P rho s.1 s.2 Delta) :
    |(∑ j,unitNormal rho s.1 j*x j)-selectedOffset rho s| ≤ Delta := by
  rw [original_unit_normal_dot]
  exact (Finset.mem_filter.mp hx).2

lemma same_floor_strict_difference (Delta x y : ℝ) (hDelta : 0<Delta)
    (hfloor : ⌊x/Delta⌋=⌊y/Delta⌋) : |x-y|<Delta := by
  have hx0 := (le_div_iff₀ hDelta).mp (Int.floor_le (x/Delta))
  have hx1 := (div_lt_iff₀ hDelta).mp (Int.lt_floor_add_one (x/Delta))
  have hy0 := (le_div_iff₀ hDelta).mp (Int.floor_le (y/Delta))
  have hy1 := (div_lt_iff₀ hDelta).mp (Int.lt_floor_add_one (y/Delta))
  rw [← hfloor] at hy0 hy1
  apply abs_lt.mpr
  constructor <;> nlinarith

/-- Literal half-open cells have strict coordinate diameter Delta. -/
theorem same_cell_projected_box_distance_lt (b : Frame3) (Delta : ℝ)
    (hDelta : 0<Delta) (x y : Point3) (hcell : cellCode b Delta x=cellCode b Delta y) :
    boxDistance (project b x) (project b y)<Delta := by
  have h0 := congrArg Prod.fst hcell
  have h1 := congrArg Prod.snd hcell
  have hx := same_floor_strict_difference Delta (project b x).1 (project b y).1 hDelta h0
  have hy := same_floor_strict_difference Delta (project b x).2 (project b y).2 hDelta h1
  simpa only [boxDistance,abs_sub_comm] using max_lt hx hy

/-- An originally separated pair in the actual slab keeps two distinct
cell labels. The quotient still carries its full original pair weight. -/
theorem original_slab_pair_cell_labels_distinct (b : Frame3) (c Delta r : ℝ)
    (hDelta : 0<Delta) (x y : Point3)
    (hx : |frameCoordinate b 2 x-c| ≤ Delta)
    (hy : |frameCoordinate b 2 y-c| ≤ Delta)
    (hscale : 4*Delta ≤ r) (hsep : r ≤ distance3 x y) :
    cellCode b Delta x≠cellCode b Delta y := by
  intro hcell
  have hlo := original_projected_pair_separation b c Delta r x y hx hy hscale hsep
  have hhi := same_cell_projected_box_distance_lt b Delta hDelta x y hcell
  linarith


/-- The actual marked original source constructs its own regular core,
unit-normal slab, orthogonal frame and weighted planar quotient. Neither
selected one-Frostman regularity nor a supplied unit slab is an input. -/
theorem exists_original_marked_weighted_planar_core
    (P : Finset Point3) (G : Finset Pair3) (F : Pair3 → Finset DirectionLabel)
    (delta rho Delta K H degree r : ℝ) (N : ℕ)
    (hd : 0<delta) (hdrho : delta ≤ rho) (hrho1 : rho ≤ 1)
    (hwidth : 3*rho ≤ Delta) (hDelta1 : Delta ≤ 1) (hK : 1 ≤ K)
    (hP : P.Nonempty) (hG : G.Nonempty) (hdegree : 0<degree)
    (hrows : ∀ z∈G,degree ≤ (F z).card)
    (hF : ∀ z∈G,F z⊆goodDirections P rho H z)
    (hbox : ∀ p∈P,∀ j,|p j| ≤ 1)
    (hterminal : 1 ≤ 2*dyadicRadius Delta N)
    (hfrostman : ∀ p∈P,∀ R : ℝ,delta ≤ R → R ≤ 1 →
      ((P.filter (fun q => distance3 p q ≤ R)).card : ℝ) ≤ K*R^2*P.card)
    (hDeltaSep : 4*Delta ≤ r) (hsep : ∀ z∈G,r ≤ distance3 z.1 z.2) :
    ∃ s∈markedSlabs P G rho H F,∃ S : Finset Point3,∃ GP : Finset Pair3,∃ b : Frame3,
      s.1∈normalGrid rho ∧ S⊆enlargedSlice P rho s.1 s.2 Delta ∧
      S.Nonempty ∧ GP.Nonempty ∧
      GP=(markedGraph P G rho H F s).filter (fun z => z.1∈S ∧ z.2∈S) ∧
      GP⊆S.product S ∧
      (∀ z∈GP,z∈G ∧ s.1∈F z ∧ chosenHeavySlabCode P rho H z s.1=s.2) ∧
      3*((enlargedSlice P rho s.1 s.2 Delta).card : ℝ) ≤ 4*S.card ∧
      ((markedGraph P G rho H F s).card : ℝ) ≤ 2*GP.card ∧
      (∑ j,(unitNormal rho s.1 j)^2)=1 ∧
      (∀ x,frameCoordinate b 2 x=unitValue rho s.1 x) ∧
      (∀ x∈S,|frameCoordinate b 2 x-selectedOffset rho s| ≤ Delta) ∧
      (∀ x∈S,|(project b x).1| ≤ 3 ∧ |(project b x).2| ≤ 3) ∧
      (∀ p∈S,∀ R : ℝ,Delta ≤ R →
        ((S.filter (fun q => distance3 p q ≤ R)).card : ℝ) ≤
          profileCoefficient P G rho Delta K degree N*R*S.card) ∧
      (∑ k∈occupied S (cellCode b Delta),pointWeight S (cellCode b Delta) k=(S.card : ℝ)) ∧
      (∑ z∈occupied GP (pairCode (cellCode b Delta)),pairWeight GP (cellCode b Delta) z=(GP.card : ℝ)) ∧
      (densityCoefficient P G rho Delta K degree N*
        (∑ k∈occupied S (cellCode b Delta),pointWeight S (cellCode b Delta) k)^2 ≤
          ∑ z∈occupied GP (pairCode (cellCode b Delta)),pairWeight GP (cellCode b Delta) z) ∧
      (∀ z,pairWeight GP (cellCode b Delta) z ≤
        pointWeight S (cellCode b Delta) z.1*pointWeight S (cellCode b Delta) z.2) ∧
      (∀ a R,∑ k∈boxBallCells S b Delta a R,pointWeight S (cellCode b Delta) k ≤
        16*profileCoefficient P G rho Delta K degree N*max R Delta*S.card) ∧
      (∀ z∈GP,r/4 ≤ boxDistance (project b z.1) (project b z.2)) ∧
      (∀ z∈GP,cellCode b Delta z.1≠cellCode b Delta z.2) := by
  have hrho := hd.trans_le hdrho
  have hDelta : 0<Delta := by linarith only [hrho,hwidth]
  have hE := original_slice_energyBudget_pos P rho Delta K N hP hrho hDelta (zero_lt_one.trans_le hK)
  have hgc : (0:ℝ)<G.card := by exact_mod_cast hG.card_pos
  have hL : 0<degree*(G.card : ℝ) := mul_pos hdegree hgc
  have hC : 0<profileCoefficient P G rho Delta K degree N := div_pos (by positivity) hL
  obtain ⟨s,hs,S,GP,hSQ,hGP,hGPeq,hmarks,hkeep,hpairs,hdense,hprofile⟩ :=
    exists_original_regularized_marked_slice P G F delta rho Delta K H degree N hd hdrho hrho1
      hwidth hDelta1 hK hP hG hdegree hrows hF hbox hterminal hfrostman
  have hGS : GP⊆S.product S := by
    intro z hz
    rw [hGPeq] at hz
    exact Finset.mem_product.mpr (Finset.mem_filter.mp hz).2
  have hS : S.Nonempty := by
    obtain ⟨z,hz⟩ := hGP
    exact ⟨z.1,(Finset.mem_product.mp (hGS hz)).1⟩
  have hSbox (x : Point3) (hx : x∈S) : ∀ j,|x j| ≤ 1 :=
    hbox x (Finset.mem_filter.mp (hSQ hx)).1
  have hSslab (x : Point3) (hx : x∈S) :
      |(∑ j,unitNormal rho s.1 j*x j)-selectedOffset rho s| ≤ Delta :=
    original_enlarged_slice_unit_slab P rho Delta s x (hSQ hx)
  have hdensity : densityCoefficient P G rho Delta K degree N*(S.card : ℝ)^2 ≤ GP.card := by
    unfold densityCoefficient
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0<8*energyBudget P rho Delta K N by positivity)).mpr
    nlinarith only [hdense]
  obtain ⟨b,hb,hcoord,_hfoot,_hdistance,hpointmass,hpairmass,hedge,hweightdense,_hweightfr⟩ :=
    exists_original_weighted_planar_projection S GP (unitNormal rho s.1) (selectedOffset rho s)
      Delta (profileCoefficient P G rho Delta K degree N) (densityCoefficient P G rho Delta K degree N)
      (original_unit_normal_square rho s.1) hDelta hC.le hSbox hSslab hGS hdensity hprofile
  have hbvalue (x : Point3) : frameCoordinate b 2 x=unitValue rho s.1 x := by
    rw [hb,original_unit_normal_dot]
  have hslab (x : Point3) (hx : x∈S) : |frameCoordinate b 2 x-selectedOffset rho s| ≤ Delta := by
    rw [hb]
    exact hSslab x hx
  have hgrid := (original_marked_slice_geometry P G rho Delta H F hrho.le hwidth hF).1 s hs
  refine ⟨s,hs,S,GP,b,hgrid,hSQ,hS,hGP,hGPeq,hGS,hmarks,hkeep,hpairs,
    original_unit_normal_square rho s.1,hbvalue,hslab,hcoord,hprofile,hpointmass,hpairmass,
    hweightdense,hedge,?_,?_,?_⟩
  · exact original_cell_weighted_box_frostman S b (selectedOffset rho s) Delta
      (profileCoefficient P G rho Delta K degree N) hDelta hC.le hslab hprofile
  · intro z hz
    obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp (hGS hz)
    exact original_projected_pair_separation b (selectedOffset rho s) Delta r z.1 z.2
      (hslab z.1 hz1) (hslab z.2 hz2) hDeltaSep (hsep z (hmarks z hz).1)

  · intro z hz
    obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp (hGS hz)
    exact original_slab_pair_cell_labels_distinct b (selectedOffset rho s) Delta r hDelta z.1 z.2
      (hslab z.1 hz1) (hslab z.2 hz2) hDeltaSep (hsep z (hmarks z hz).1)

end OriginalThreeDimensionalMarkedPlanarCore
