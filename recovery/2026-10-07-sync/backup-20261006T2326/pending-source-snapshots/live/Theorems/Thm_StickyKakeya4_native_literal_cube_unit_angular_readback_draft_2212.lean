import Theorems.Thm_StickyKakeya4_native_literal_reference_angular_cube_transfer_draft_2204
import Theorems.Thm_StickyKakeya4_native_angular_dyadic_interpolation
import Theorems.Thm_StickyKakeya4_native_unit_parent_directions

/- UNVERIFIED source-facing readers for the literal Reference cube estimate.
Actual unit-direction balls replace a supplied coordinate slope-bin bound.
The existing angularCell at N=1,p=0 is only a query on the original slopes.
Its exact dyadic descendants account for every omitted fine query depth.
No native source, point alphabet, or incidence graph is changed.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeLiteralCubeUnitAngularReadbackDraft2212
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeGenericReferenceData NativeOriginalParentDensityCore
open NativeLiteralCubeAnglePhaseMenuDraft2159 NativeNormalizedCellAngularMenu
open NativeAngularDyadicInterpolation NativeLocalParentGeometry

/-- The angular query at N=1 and zero parent is the actual original slope
grid, coarsened by eight. This identity makes no parent-membership claim. -/
lemma literal_angular_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (M : ℕ) (i : Fin n) :
    angularCell D 1 M (0,0) i=(fun v => (parentLabel D a M i).1 v/8) := by
  funext v
  change ⌊((M:ℝ)*((1:ℝ)*slope (D.line i) v-(0:ℝ)))/8⌋=
    ⌊(M:ℝ)*slope (D.line i) v⌋/8
  simp only [one_mul,sub_zero]
  have hh := Int.floor_div_natCast ((M:ℝ)*slope (D.line i) v) 8
  norm_num only [Nat.cast_ofNat] at hh
  exact hh

/-- Angular labels are an exact image of the occupied full original
parameter labels, so their count needs no extra source or geometric loss. -/
lemma literal_angular_count_le {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (M : ℕ) (E : Finset (Fin n × Index)) :
    (E.image (fun z => angularCell D 1 M (0,0) z.1)).card ≤
      (E.image (fun z => parentLabel D a M z.1)).card := by
  have he : E.image (fun z => angularCell D 1 M (0,0) z.1)=
      (E.image (fun z => parentLabel D a M z.1)).image (fun p => fun v => p.1 v/8) := by
    rw [image_image]
    congr 1
    funext z
    exact literal_angular_readback D a M z.1
  rw [he]
  exact card_image_le

/-- A physical source cube and a genuine ambient unit-direction ball give
the prepared-scale count. The arbitrary ball center is removed using one
occupied witness; native direction-to-slope control gives the fixed768
coordinate margin, hence1537^3 coarse angular cells. -/
theorem reference_native_cube_unit_ball_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (i j : Fin (g+1)) (hij : (ref.schedule i).val ≤ (ref.schedule j).val)
    (E : Finset (Fin n × Index)) (hE : E⊆ref.E1) (center directionCenter : E4)
    (hBall : ∀z∈E,dist (cellCenter (mesh D) z.2) center ≤
      128/((2^(ref.schedule j).val:ℕ):ℝ))
    (hAngle : ∀z∈E,dist (direction (D.line z.1)) directionCenter ≤
      64/((2^(ref.schedule i).val:ℕ):ℝ)) :
    ((E.image (fun z => parentLabel D ref.a (2^(ref.schedule j).val) z.1)).card:ℝ) ≤
      (625*((393^3:ℕ):ℝ)*((1537^3:ℕ):ℝ))*(coreRadix ref.original ref.R L:ℝ)^4*
        D.thickness^(-tau)*
        ((64/((2^(ref.schedule j).val:ℕ):ℝ))/(64/((2^(ref.schedule i).val:ℕ):ℝ)))^
          (-NativeFixedCompactKakeyaExponent.extremalExponent) := by
  have hd := h.1.2.1
  by_cases hEn : E.Nonempty
  · obtain ⟨z0,hz0⟩ := hEn
    let N : ℕ := 2^(ref.schedule i).val
    have hNr : (0:ℝ)<N := by dsimp only [N]; positivity
    have hSlope : ∀z∈E,∀v : Fin 3,
        |(N:ℝ)*slope (D.line z.1) v-(N:ℝ)*slope (D.line z0.1) v| ≤ (768:ℕ) := by
      intro z hz v
      have hdist : dist (direction (D.line z.1)) (direction (D.line z0.1)) ≤
          2*(64/(N:ℝ)) := by
        calc
          _ ≤ dist (direction (D.line z.1)) directionCenter+
              dist directionCenter (direction (D.line z0.1)) := dist_triangle _ _ _
          _ ≤ 64/(N:ℝ)+64/(N:ℝ) :=
            add_le_add (hAngle z hz) (by simpa only [dist_comm] using hAngle z0 hz0)
          _ = _ := by ring
      have hs := (NativeUnitParentDirections.slope_sub_le_direction_dist
        (D.line z.1) (D.line z0.1) (h.1.2.2.2.2.1 z0.1) (h.2.1.1 z.1) (h.2.1.1 z0.1) v).trans
          (mul_le_mul_of_nonneg_left hdist (by norm_num))
      calc
        _ = (N:ℝ)*|slope (D.line z.1) v-slope (D.line z0.1) v| := by
          rw [←mul_sub,abs_mul,abs_of_pos hNr]
        _ ≤ (N:ℝ)*(6*(2*(64/(N:ℝ)))) := mul_le_mul_of_nonneg_left hs hNr.le
        _ = _ := by field_simp; ring
    have hh := reference_native_cube_angle_upper ref i j hij E hE center hBall
      (fun v => (N:ℝ)*slope (D.line z0.1) v) 768 hSlope
    norm_num only [Nat.reduceMul,Nat.reduceAdd] at hh
    exact hh
  · rw [not_nonempty_iff_eq_empty.mp hEn,image_empty,card_empty,Nat.cast_zero]
    positivity

/-- Every finer dyadic angular query is read from the same prepared cube
estimate with its exact3-dimensional descendant cost. Source cube centers
and unit directions remain literal; sigma is still D.thickness. -/
theorem reference_off_menu_cube_angular_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (i j : Fin (g+1)) (hij : (ref.schedule i).val ≤ (ref.schedule j).val)
    (s : ℕ) (hjs : (ref.schedule j).val ≤ s)
    (E : Finset (Fin n × Index)) (hE : E⊆ref.E1) (center directionCenter : E4)
    (hBall : ∀z∈E,dist (cellCenter (mesh D) z.2) center ≤ 128/((2^s:ℕ):ℝ))
    (hAngle : ∀z∈E,dist (direction (D.line z.1)) directionCenter ≤
      64/((2^(ref.schedule i).val:ℕ):ℝ)) :
    ((E.image (fun z => angularCell D 1 (2^s) (0,0) z.1)).card:ℝ) ≤
      (((2^(s-(ref.schedule j).val))^3:ℕ):ℝ)*
        (625*((393^3:ℕ):ℝ)*((1537^3:ℕ):ℝ))*(coreRadix ref.original ref.R L:ℝ)^4*
          D.thickness^(-tau)*
          ((64/((2^(ref.schedule j).val:ℕ):ℝ))/(64/((2^(ref.schedule i).val:ℕ):ℝ)))^
            (-NativeFixedCompactKakeyaExponent.extremalExponent) := by
  have hScale : 128/((2^s:ℕ):ℝ) ≤ 128/((2^(ref.schedule j).val:ℕ):ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ)) hjs
  have hParent := reference_native_cube_unit_ball_upper ref i j hij E hE center directionCenter
    (fun z hz => (hBall z hz).trans hScale) hAngle
  have hAngular : ((E.image (fun z => angularCell D 1 (2^(ref.schedule j).val) (0,0) z.1)).card:ℝ) ≤
      ((E.image (fun z => parentLabel D ref.a (2^(ref.schedule j).val) z.1)).card:ℝ) := by
    exact_mod_cast literal_angular_count_le D ref.a (2^(ref.schedule j).val) E
  have hInterp := angular_image_interpolation D 1 (0,0) E hjs
  exact hInterp.trans ((mul_le_mul_of_nonneg_left (hAngular.trans hParent)
    (Nat.cast_nonneg _)).trans_eq (by ring))

end NativeLiteralCubeUnitAngularReadbackDraft2212
