import Theorems.Thm_StickyKakeya4_original_three_dimensional_band_geometry
import Theorems.Thm_StickyKakeya4_finite_transverse_menu_growth

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalLiteralSlabCover
open Classical OriginalThreeDimensionalBandGeometry

abbrev Frame3 := OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))

def frameCoordinate (b : Frame3) (j : Fin 3) (x : Point3) : ℝ :=
  ∑ k,b j k*x k

/-- Literal finite oriented rectangle, with tangential side lengths one
and normal half-width r. The frame is genuinely orthonormal. -/
def rectangle (b : Frame3) (c r : ℝ) (k : ℤ×ℤ) : Set Point3 :=
  {x | |frameCoordinate b 2 x-c| ≤ r ∧
    (k.1:ℝ) ≤ frameCoordinate b 0 x ∧ frameCoordinate b 0 x ≤ (k.1:ℝ)+1 ∧
    (k.2:ℝ) ≤ frameCoordinate b 1 x ∧ frameCoordinate b 1 x ≤ (k.2:ℝ)+1}

/-- A genuine unit normal extends to a real orthonormal rectangle frame. -/
theorem exists_original_normal_frame (n : Point3) (hn : ∑ j,n j^2=1) :
    ∃ b : Frame3,∀ x,frameCoordinate b 2 x=∑ j,n j*x j := by
  let v : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 n
  have hvnorm : ‖v‖=1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [v,Real.norm_eq_abs,sq_abs,hn,Real.sqrt_one]
  have hv : Orthonormal ℝ (({2} : Set (Fin 3)).domRestrict (fun _ => v)) := by
    rw [orthonormal_subsingleton_iff]
    intro j
    exact hvnorm
  obtain ⟨b,hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨b,?_⟩
  intro x
  have he : b 2=v := hb 2 (by simp)
  simp only [frameCoordinate,he,v,PiLp.toLp_apply]

/-- Every actual bounded source point has all frame coordinates bounded
by three, uniformly over the chosen orientation. -/
theorem original_frame_coordinate_bound (b : Frame3) (x : Point3)
    (hx : ∀ j,|x j| ≤ 1) (j : Fin 3) : |frameCoordinate b j x| ≤ 3 := by
  have hc (k : Fin 3) : |b j k| ≤ 1 := by
    have h := PiLp.norm_apply_le (b j) k
    simpa only [Real.norm_eq_abs,b.norm_eq_one] using h
  unfold frameCoordinate
  calc
    _ ≤ ∑ k,|b j k*x k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 3,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [abs_mul]
      exact (mul_le_mul (hc k) (hx k) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    _ = 3 := by norm_num

/-- The original bounded source in any unit-normal slab is covered by
49 literal unit-tangential rectangles. This pays the finite-window cost
in the printed A4 slab hypothesis, without assuming an infinite-slab cap. -/
theorem original_unit_slab_from_literal_rectangles (P : Finset Point3)
    (r M : ℝ) (hbox : ∀ x∈P,∀ j,|x j| ≤ 1)
    (hrect : ∀ b : Frame3,∀ c : ℝ,∀ k : ℤ×ℤ,
      ((P.filter (fun x => x∈rectangle b c r k)).card : ℝ) ≤ M)
    (n : Point3) (hn : ∑ j,n j^2=1) (c : ℝ) :
    ((P.filter (fun x => |(∑ j,n j*x j)-c| ≤ r)).card : ℝ) ≤ 49*M := by
  obtain ⟨b,hb⟩ := exists_original_normal_frame n hn
  let Q := P.filter (fun x => |(∑ j,n j*x j)-c| ≤ r)
  let code : Point3 → ℤ×ℤ := fun x => (⌊frameCoordinate b 0 x⌋,⌊frameCoordinate b 1 x⌋)
  let J : Finset (ℤ×ℤ) := (Finset.Icc (-3:ℤ) 3).product (Finset.Icc (-3:ℤ) 3)
  have hmem (x : Point3) (hx : x∈Q) : code x∈J := by
    have hh (j : Fin 3) := abs_le.mp (original_frame_coordinate_bound b x (hbox x (Finset.mem_filter.mp hx).1) j)
    have hf (j : Fin 3) : (-3:ℤ) ≤ ⌊frameCoordinate b j x⌋ ∧ ⌊frameCoordinate b j x⌋ ≤ (3:ℤ) := by
      constructor
      · exact Int.le_floor.mpr (by exact_mod_cast (hh j).1)
      · simpa using Int.floor_mono (hh j).2
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hf 0),Finset.mem_Icc.mpr (hf 1)⟩
  have hc := FiniteTransverseMenuGrowth.card_le_real_mul_of_fibers Q J code M hmem (by
    intro k _hk
    have hsub : Q.filter (fun x => code x=k)⊆P.filter (fun x => x∈rectangle b c r k) := by
      intro x hx
      obtain ⟨hxQ,hcode⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxP,hslab⟩ := Finset.mem_filter.mp hxQ
      have he0 : ⌊frameCoordinate b 0 x⌋=k.1 := congrArg Prod.fst hcode
      have he1 : ⌊frameCoordinate b 1 x⌋=k.2 := congrArg Prod.snd hcode
      refine Finset.mem_filter.mpr ⟨hxP,?_,?_,?_,?_,?_⟩
      · change |frameCoordinate b 2 x-c| ≤ r
        rwa [hb]
      · simpa only [he0] using Int.floor_le (frameCoordinate b 0 x)
      · simpa only [he0] using (Int.lt_floor_add_one (frameCoordinate b 0 x)).le
      · simpa only [he1] using Int.floor_le (frameCoordinate b 1 x)
      · simpa only [he1] using (Int.lt_floor_add_one (frameCoordinate b 1 x)).le
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hrect b c k))
  have hcard : (J.card : ℝ)=49 := by norm_num [J,Int.toNat]
  rw [hcard] at hc
  exact hc

end OriginalThreeDimensionalLiteralSlabCover
