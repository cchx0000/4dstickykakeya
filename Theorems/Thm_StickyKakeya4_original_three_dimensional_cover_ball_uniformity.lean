import Theorems.Thm_StickyKakeya4_original_three_dimensional_slab_projection
import Theorems.Thm_StickyKakeya4_packing_reference_overlap
import Theorems.Thm_StickyKakeya4_dimension_witness_extraction

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

noncomputable section
open scoped BigOperators ENNReal
namespace OriginalThreeDimensionalCoverBallUniformity
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSlabProjection StickyKakeya4

abbrev E3 := EuclideanSpace ℝ (Fin 3)
def point (x : Point3) : E3 := WithLp.toLp 2 x
def meshCover (P : Finset Point3) (delta : ℝ) : ℝ≥0∞ :=
  coveringNumber (↑(P.image point) : Set E3) delta

def originalOpenBall (P : Finset Point3) (a : Point3) (R : ℝ) : Finset Point3 :=
  P.filter (fun x => distance3 a x < R)

/-- The original metric-ball covering-number uniformity, with its original
fine mesh. This is pairwise comparability of the literal ball populations. -/
def OriginalCoverUniform (P : Finset Point3) (delta K : ℝ) : Prop :=
  ∀ a∈P, ∀ b∈P, ∀ R : ℝ, delta ≤ R → R ≤ 1 →
    meshCover (originalOpenBall P a R) delta ≤
      ENNReal.ofReal K*meshCover (originalOpenBall P b R) delta

def packingConstant : ℕ := max 1
  (Classical.choose (exists_uniform_separated_ball_card_bound E3))

private lemma packingConstant_pos : 0 < packingConstant :=
  lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)
private lemma point_injective : Function.Injective point := WithLp.toLp_injective 2

/-- Actual original fine separation compares cardinality with the literal
Euclidean covering number, using a fixed dimensional packing constant. -/
theorem original_cardinal_mesh_cover_bounds (P : Finset Point3) (delta : ℝ)
    (hd : 0 < delta)
    (hsep : ∀ x∈P, ∀ y∈P, x≠y → delta ≤ distance3 x y) :
    meshCover P delta ≤ (P.card : ℝ≥0∞) ∧
      (P.card : ℝ≥0∞) ≤ (packingConstant : ℝ≥0∞)*meshCover P delta := by
  let Q := P.image point
  have hcard : Q.card=P.card := Finset.card_image_of_injective _ point_injective
  have hcoverSelf : coversAtRadius (↑Q : Set E3) delta Q := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,by simpa only [Metric.mem_ball,dist_self] using hd⟩⟩
  have hupper := coveringNumber_le_card_of_coversAtRadius (↑Q : Set E3) delta Q hcoverSelf
  have hcapacity (c : E3) : (Q.filter (fun x => dist x c < delta)).card ≤ packingConstant := by
    have hK := Classical.choose_spec (exists_uniform_separated_ball_card_bound E3)
    apply (hK delta hd c (Q.filter (fun x => dist x c < delta)) ?_ ?_).trans (le_max_right _ _)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2.le
    · intro x hx y hy hxy
      obtain ⟨px,hpx,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hx).1
      obtain ⟨py,hpy,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
      have hpne : px≠py := fun he => hxy (congrArg point he)
      have hs := hsep px hpx py hpy hpne
      rw [distance3_eq_euclidean] at hs
      exact (by linarith only [hd] : delta/2 ≤ delta).trans hs
  have hfinite (C : Finset E3) (hC : coversAtRadius (↑Q : Set E3) delta C) :
      Q.card ≤ packingConstant*C.card := by
    have hsub : Q⊆C.biUnion (fun c => Q.filter (fun x => dist x c < delta)) := by
      intro x hx
      obtain ⟨c,hc⟩ := Set.mem_iUnion.mp (hC hx)
      obtain ⟨hcC,hxc⟩ := Set.mem_iUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨c,hcC,Finset.mem_filter.mpr ⟨hx,hxc⟩⟩
    calc
      _ ≤ (C.biUnion (fun c => Q.filter (fun x => dist x c < delta))).card := Finset.card_le_card hsub
      _ ≤ ∑ c∈C,(Q.filter (fun x => dist x c < delta)).card := Finset.card_biUnion_le
      _ ≤ ∑ _c∈C,packingConstant := Finset.sum_le_sum (fun c _hc => hcapacity c)
      _ = _ := by simp [Nat.mul_comm]
  have hk0 : (packingConstant : ℝ≥0∞)≠0 := by exact_mod_cast (ne_of_gt packingConstant_pos)
  have hkinfty : (packingConstant : ℝ≥0∞)≠⊤ := by simp
  have hlower : (Q.card : ℝ≥0∞)/(packingConstant : ℝ≥0∞) ≤ coveringNumber (↑Q : Set E3) delta := by
    unfold coveringNumber
    apply le_sInf
    rintro m ⟨C,hC,rfl⟩
    apply (ENNReal.div_le_iff' hk0 hkinfty).mpr
    exact_mod_cast hfinite C hC
  have hh := (ENNReal.div_le_iff' hk0 hkinfty).mp hlower
  rw [hcard] at hupper hh
  exact ⟨hupper,hh⟩

/-- Literal original covering-number ball uniformity yields original POINT
population comparability. It does not assert uniform restricted cell fibers. -/
theorem original_cover_uniform_cardinal_ball_comparison
    (P : Finset Point3) (delta K : ℝ) (hd : 0 < delta) (hK : 0 ≤ K)
    (hsep : ∀ x∈P, ∀ y∈P, x≠y → delta ≤ distance3 x y)
    (huniform : OriginalCoverUniform P delta K) :
    ∀ a∈P, ∀ b∈P, ∀ R : ℝ, delta ≤ R → R ≤ 1 →
      ((originalOpenBall P a R).card : ℝ) ≤
        (packingConstant : ℝ)*K*(originalOpenBall P b R).card := by
  intro a ha b hb R hR hR1
  have hsepA (x : Point3) (hx : x∈originalOpenBall P a R) (y : Point3)
      (hy : y∈originalOpenBall P a R) (hne : x≠y) :=
    hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne
  have hsepB (x : Point3) (hx : x∈originalOpenBall P b R) (y : Point3)
      (hy : y∈originalOpenBall P b R) (hne : x≠y) :=
    hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne
  have hA := (original_cardinal_mesh_cover_bounds (originalOpenBall P a R) delta hd hsepA).2
  have hB := (original_cardinal_mesh_cover_bounds (originalOpenBall P b R) delta hd hsepB).1
  have hN := huniform a ha b hb R hR hR1
  have hresult : ((originalOpenBall P a R).card : ℝ≥0∞) ≤
      (packingConstant : ℝ≥0∞)*ENNReal.ofReal K*(originalOpenBall P b R).card := by
    calc
      _ ≤ (packingConstant : ℝ≥0∞)*meshCover (originalOpenBall P a R) delta := hA
      _ ≤ (packingConstant : ℝ≥0∞)*(ENNReal.ofReal K*meshCover (originalOpenBall P b R) delta) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      _ ≤ (packingConstant : ℝ≥0∞)*(ENNReal.ofReal K*(originalOpenBall P b R).card) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB (by positivity)) (by positivity)
      _ = _ := by ring
  have hfinite : (packingConstant : ℝ≥0∞)*ENNReal.ofReal K*(originalOpenBall P b R).card≠⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (by simp)
  have hh := ENNReal.toReal_mono hfinite hresult
  simpa only [ENNReal.toReal_natCast,ENNReal.toReal_mul,ENNReal.toReal_ofReal hK] using hh

end OriginalThreeDimensionalCoverBallUniformity
