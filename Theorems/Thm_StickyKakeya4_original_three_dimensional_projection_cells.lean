import Theorems.Thm_StickyKakeya4_original_three_dimensional_slab_projection
import Theorems.Thm_StickyKakeya4_original_finite_cell_weights
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalProjectionCells
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalFiniteCellWeights

abbrev Cell := ℤ × ℤ

def cellCode (b : Frame3) (Delta : ℝ) (x : Point3) : Cell :=
  (⌊(project b x).1/Delta⌋,⌊(project b x).2/Delta⌋)

def cellAnchor (Delta : ℝ) (k : Cell) : Point2 := (Delta*k.1,Delta*k.2)

def ballCells (P : Finset Point3) (b : Frame3) (Delta : ℝ) (a : Point2) (r : ℝ) : Finset Cell :=
  (occupied P (cellCode b Delta)).filter (fun k => distance2 (cellAnchor Delta k) a ≤ r)

lemma distance2_triangle (x y z : Point2) : distance2 x z ≤ distance2 x y+distance2 y z :=
  dist_triangle _ _ _

lemma distance2_comm (x y : Point2) : distance2 x y=distance2 y x := dist_comm _ _

lemma distance2_le_abs_add (x y : Point2) :
    distance2 x y ≤ |x.1-y.1|+|x.2-y.2| := by
  have h := distance2_squared x y
  have h0 : 0 ≤ distance2 x y := dist_nonneg
  nlinarith only [h,h0,abs_nonneg (x.1-y.1),abs_nonneg (x.2-y.2),
    sq_abs (x.1-y.1),sq_abs (x.2-y.2),
    mul_nonneg (abs_nonneg (x.1-y.1)) (abs_nonneg (x.2-y.2))]

lemma abs_coordinate_le_distance2 (x y : Point2) :
    |x.1-y.1| ≤ distance2 x y ∧ |x.2-y.2| ≤ distance2 x y := by
  have h := distance2_squared x y
  have hd : 0 ≤ distance2 x y := dist_nonneg
  constructor <;> nlinarith only [h,hd,sq_nonneg (x.1-y.1),sq_nonneg (x.2-y.2),
    abs_nonneg (x.1-y.1),abs_nonneg (x.2-y.2),sq_abs (x.1-y.1),sq_abs (x.2-y.2)]

lemma floor_anchor_error (Delta t : ℝ) (hDelta : 0<Delta) :
    |t-Delta*(⌊t/Delta⌋ : ℝ)| ≤ Delta := by
  have hlo := (le_div_iff₀ hDelta).mp (Int.floor_le (t/Delta))
  have hhi := (div_lt_iff₀ hDelta).mp (Int.lt_floor_add_one (t/Delta))
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The grid anchor is separate from the actual projected endpoint,
with its displacement proved from the literal floor cell. -/
theorem original_projected_cell_error (b : Frame3) (Delta : ℝ) (hDelta : 0<Delta)
    (x : Point3) : distance2 (project b x) (cellAnchor Delta (cellCode b Delta x)) ≤ 2*Delta := by
  have h := distance2_le_abs_add (project b x) (cellAnchor Delta (cellCode b Delta x))
  have hx := floor_anchor_error Delta (project b x).1 hDelta
  have hy := floor_anchor_error Delta (project b x).2 hDelta
  change distance2 _ _ ≤ |(project b x).1-Delta*(⌊(project b x).1/Delta⌋ : ℝ)|+
    |(project b x).2-Delta*(⌊(project b x).2/Delta⌋ : ℝ)| at h
  linarith

theorem original_cell_anchor_bounds (b : Frame3) (Delta : ℝ) (hDelta : 0<Delta)
    (x : Point3) (hx : ∀ j,|x j| ≤ 1) :
    |(cellAnchor Delta (cellCode b Delta x)).1| ≤ 3+Delta ∧
    |(cellAnchor Delta (cellCode b Delta x)).2| ≤ 3+Delta := by
  have hb := original_projected_coordinate_bounds b x hx
  have h0 := floor_anchor_error Delta (project b x).1 hDelta
  have h1 := floor_anchor_error Delta (project b x).2 hDelta
  have ha0 := abs_sub_le (0:ℝ) (project b x).1 (Delta*(⌊(project b x).1/Delta⌋ : ℝ))
  have ha1 := abs_sub_le (0:ℝ) (project b x).2 (Delta*(⌊(project b x).2/Delta⌋ : ℝ))
  simp only [zero_sub,abs_neg] at ha0 ha1
  constructor <;> dsimp [cellAnchor,cellCode] <;> linarith

/-- Distinct lattice anchors are separated; their mass is still the full
original cell weight, and they are not asserted to be original points. -/
theorem cellAnchor_separated (Delta : ℝ) (hDelta : 0<Delta) (k l : Cell)
    (hkl : k≠l) : Delta ≤ distance2 (cellAnchor Delta k) (cellAnchor Delta l) := by
  have hcoord := abs_coordinate_le_distance2 (cellAnchor Delta k) (cellAnchor Delta l)
  by_cases h1 : k.1=l.1
  · have h2 : k.2≠l.2 := fun h => hkl (Prod.ext h1 h)
    have hi : (1:ℝ) ≤ |(k.2:ℝ)-(l.2:ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h2)
    have hh := hcoord.2
    change |Delta*(k.2:ℝ)-Delta*(l.2:ℝ)| ≤ _ at hh
    rw [← mul_sub,abs_mul,abs_of_pos hDelta] at hh
    nlinarith
  · have hi : (1:ℝ) ≤ |(k.1:ℝ)-(l.1:ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h1)
    have hh := hcoord.1
    change |Delta*(k.1:ℝ)-Delta*(l.1:ℝ)| ≤ _ at hh
    rw [← mul_sub,abs_mul,abs_of_pos hDelta] at hh
    nlinarith

lemma project_linePoint (b : Frame3) (x y : Point3) (t : ℝ) :
    project b (linePoint3 x y t)=
      OriginalPairStripGeometry.linePoint (project b x,project b y) t := by
  have hc (j : Fin 3) : frameCoordinate b j (linePoint3 x y t)=
      frameCoordinate b j x+t*(frameCoordinate b j y-frameCoordinate b j x) := by
    simp only [frameCoordinate,linePoint3,Fin.sum_univ_three]
    ring
  ext <;> simp [project,OriginalPairStripGeometry.linePoint,hc]

/-- The original all-radius-above-Delta Frostman law pushes to a genuine
weighted planar cell law at every radius. Small radii retain the atomic
Delta floor, and the weights are literal original point cardinalities. -/
theorem original_cell_weighted_frostman (P : Finset Point3) (b : Frame3)
    (c Delta K : ℝ) (hDelta : 0<Delta) (hK : 0 ≤ K)
    (hslab : ∀ x∈P,|frameCoordinate b 2 x-c| ≤ Delta)
    (hfr : ∀ p∈P,∀ R : ℝ,Delta ≤ R →
      ((P.filter (fun q => distance3 p q ≤ R)).card : ℝ) ≤ K*R*P.card)
    (a : Point2) (r : ℝ) :
    ∑ k∈ballCells P b Delta a r,pointWeight P (cellCode b Delta) k ≤
      8*K*max r Delta*P.card := by
  rw [point_subset_mass_readback]
  let T := P.filter (fun x => cellCode b Delta x∈ballCells P b Delta a r)
  change (T.card : ℝ) ≤ _
  by_cases hT : T.Nonempty
  · obtain ⟨p,hp⟩ := hT
    obtain ⟨hpP,hpcell⟩ := Finset.mem_filter.mp hp
    have hpa := (Finset.mem_filter.mp hpcell).2
    let R := 8*max r Delta
    have hR : Delta ≤ R := by dsimp [R]; linarith [le_max_right r Delta]
    have hsub : T⊆P.filter (fun q => distance3 p q ≤ R) := by
      intro q hq
      obtain ⟨hqP,hqcell⟩ := Finset.mem_filter.mp hq
      have hqa := (Finset.mem_filter.mp hqcell).2
      have hproj : distance2 (project b p) (project b q) ≤ 2*r+4*Delta := by
        have h1 := distance2_triangle (project b p) (cellAnchor Delta (cellCode b Delta p)) (project b q)
        have h2 := distance2_triangle (cellAnchor Delta (cellCode b Delta p)) a (project b q)
        have h3 := distance2_triangle a (cellAnchor Delta (cellCode b Delta q)) (project b q)
        have hpE := original_projected_cell_error b Delta hDelta p
        have hqE := original_projected_cell_error b Delta hDelta q
        rw [distance2_comm a (cellAnchor Delta (cellCode b Delta q))] at h3
        rw [distance2_comm (cellAnchor Delta (cellCode b Delta q)) (project b q)] at h3
        linarith
      have hamb := original_slab_distance_comparison b c Delta p q (hslab p hpP) (hslab q hqP)
      refine Finset.mem_filter.mpr ⟨hqP,?_⟩
      dsimp [R]
      linarith [le_max_left r Delta,le_max_right r Delta]
    have hc := (Nat.cast_le.mpr (Finset.card_le_card hsub) : (T.card : ℝ) ≤ _)
    have hf := hfr p hpP R hR
    dsimp [R] at hf
    nlinarith only [hc,hf]
  · have he : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    rw [he,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK)
      (hDelta.le.trans (le_max_right r Delta))) (Nat.cast_nonneg _)

end OriginalThreeDimensionalProjectionCells
