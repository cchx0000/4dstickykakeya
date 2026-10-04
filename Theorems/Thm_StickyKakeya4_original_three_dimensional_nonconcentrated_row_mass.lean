import Theorems.Thm_StickyKakeya4_original_three_dimensional_expanded_band_count
import Theorems.Thm_StickyKakeya4_original_three_dimensional_separated_normals
import Theorems.Thm_StickyKakeya4_original_three_dimensional_annular_slab_charge
import Mathlib.Combinatorics.Enumerative.DoubleCounting

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

noncomputable section
open scoped Matrix BigOperators
namespace OriginalThreeDimensionalNonconcentratedRowMass
open Classical Matrix OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalUnitSlabs OriginalThreeDimensionalUnitNormals
open OriginalThreeDimensionalSliceMaximizer OriginalThreeDimensionalCrossGeometry
open OriginalThreeDimensionalNarrowSlabOverlap OriginalThreeDimensionalSeparatedNormals
open OriginalThreeDimensionalExpandedBandCount

def outsideSlice (P : Finset Point3) (rho Delta q : ℝ) (z : Pair3)
    (d : DirectionLabel) (k : ℤ) : Finset Point3 :=
  enlargedSlice P rho d k Delta\physicalPairTube3 (enlargedSlice P rho d k Delta) q z

private lemma original_row_normal_close (P : Finset Point3) (z : Pair3) (x : Point3)
    (rho Delta r q : ℝ) (d e : DirectionLabel) (kd ke : ℤ)
    (hrho : 0 ≤ rho) (hDelta : 0 < Delta) (hr : 0 < r) (hq : 0 < q)
    (hwidth : 3*rho ≤ Delta) (hscale : 54*rho ≤ Delta*r)
    (hbox : ∀ p∈P, ∀ i, |p i| ≤ 1) (hsep : r ≤ distance3 z.1 z.2)
    (hd : z.1∈slabPoints P rho d kd ∧ z.2∈slabPoints P rho d kd)
    (he : z.1∈slabPoints P rho e ke ∧ z.2∈slabPoints P rho e ke)
    (hxd : x∈outsideSlice P rho Delta q z d kd)
    (hxe : x∈outsideSlice P rho Delta q z e ke) :
    min (distance3 (unitNormal rho d) (unitNormal rho e))
      (distance3 (unitNormal rho d) (-unitNormal rho e)) < 30*Delta/q := by
  have hxQd := (Finset.mem_sdiff.mp hxd).1
  have hxQe := (Finset.mem_sdiff.mp hxe).1
  have hxP := (Finset.mem_filter.mp hxQd).1
  have hn (u : DirectionLabel) : normSq3 (unitNormal rho u)=1 := by
    simpa only [normSq3,dotProduct,pow_two] using original_unit_normal_square rho u
  have hnp (u : DirectionLabel) (k : ℤ) (p : Point3) (hp : p∈slabPoints P rho u k) :
      |unitNormal rho u ⬝ᵥ p-rho*k/normalLength rho u| ≤ 3*rho := by
    rw [dotProduct,original_unit_normal_dot]
    exact original_slab_in_unit_slab P rho u k hrho p hp
  have hnx (u : DirectionLabel) (k : ℤ) (hx : x∈enlargedSlice P rho u k Delta) :
      |unitNormal rho u ⬝ᵥ x-rho*k/normalLength rho u| ≤ Delta := by
    rw [dotProduct,original_unit_normal_dot]
    exact (Finset.mem_filter.mp hx).2
  have hout : x∉physicalTube3 z.1 z.2 q := by
    intro hx
    exact (Finset.mem_sdiff.mp hxd).2 (Finset.mem_filter.mpr ⟨hxQd,hx⟩)
  exact original_shared_narrow_slab_point_forces_close_normals z.1 z.2 x
    (unitNormal rho d) (unitNormal rho e) (rho*kd/normalLength rho d) (rho*ke/normalLength rho e)
    rho Delta r q hrho hDelta hr hq hwidth hscale (hn d) (hn e)
    (hbox z.1 (Finset.mem_filter.mp hd.1).1) (hbox x hxP) hsep
    (hnp d kd z.1 hd.1) (hnp d kd z.2 hd.2) (hnx d kd hxQd)
    (hnp e ke z.1 he.1) (hnp e ke z.2 he.2) (hnx e ke hxQe) hout

/-- At any original point away from the pair tube, the actual row labels
lie in two genuine normal caps. The large-cap branch uses the full actual
band count, retaining its inverse-r loss instead of extrapolating a cap law. -/
theorem original_outside_row_label_count (P : Finset Point3) (z : Pair3)
    (F : Finset DirectionLabel) (k : DirectionLabel → ℤ) (rho Delta r q : ℝ) (x : Point3)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hr : 0 < r) (hq : 0 < q) (hq1 : q ≤ 1)
    (hwidth : 3*rho ≤ Delta) (hscale : 54*rho ≤ Delta*r)
    (hzP : z∈P.product P) (hbox : ∀ p∈P, ∀ i, |p i| ≤ 1)
    (hsep : r ≤ distance3 z.1 z.2) (hF : F⊆pairBand rho z.1 z.2)
    (hslabs : ∀ d∈F, z.1∈slabPoints P rho d (k d) ∧ z.2∈slabPoints P rho d (k d)) :
    ((F.filter (fun d => x∈outsideSlice P rho Delta q z d (k d))).card : ℝ)*rho*r*q ≤
      21600000*Delta := by
  let X := F.filter (fun d => x∈outsideSlice P rho Delta q z d (k d))
  let w := 30*Delta/q
  have hDelta : 0 < Delta := by linarith only [hrho,hwidth]
  have hw : 0 < w := by dsimp [w]; positivity
  have hX : X⊆F := Finset.filter_subset _ _
  obtain ⟨hpP,hqP⟩ := Finset.mem_product.mp hzP
  have hcount : (X.card : ℝ) ≤ F.card := Nat.cast_le.mpr (Finset.card_le_card hX)
  change (X.card : ℝ)*rho*r*q ≤ 21600000*Delta
  by_cases hwsmall : w ≤ 1/10
  · by_cases hne : X.Nonempty
    · obtain ⟨d₀,hd₀⟩ := hne
      have hsub : X⊆doubleCap F rho w (unitNormal rho d₀) := by
        intro d hd
        have hc := original_row_normal_close P z x rho Delta r q d d₀ (k d) (k d₀)
          hrho.le hDelta hr hq hwidth hscale hbox hsep (hslabs d (hX hd)) (hslabs d₀ (hX hd₀))
          (Finset.mem_filter.mp hd).2 (Finset.mem_filter.mp hd₀).2
        exact Finset.mem_filter.mpr ⟨hX hd,(min_lt_iff.mp hc).imp le_of_lt le_of_lt⟩
      have hrhow : rho ≤ w := by
        apply (le_div_iff₀ hq).mpr
        have hh := mul_le_mul_of_nonneg_left hq1 hrho.le
        nlinarith only [hh,hwidth,hrho]
      have hc := original_double_cap_count F rho w r z.1 z.2 (unitNormal rho d₀)
        hrho hrhow hwsmall hr hsep (hbox _ hpP) (hbox _ hqP) (original_unit_normal_square rho d₀) hF
      have hc' := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub))
        (show 0 ≤ rho*r by positivity)
      have hm := mul_le_mul_of_nonneg_right
        (show (X.card : ℝ)*rho*r ≤ 720000*w by nlinarith only [hc,hc']) hq.le
      have he : 720000*w*q=21600000*Delta := by dsimp [w]; field_simp; norm_num
      change (X.card : ℝ)*rho*r*q ≤ _
      exact hm.trans_eq he
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
      simp only [zero_mul]
      positivity
  · have hband := original_expanded_normal_band_count F rho rho z.1 z.2 hrho hrho1 le_rfl
      (hbox _ hpP) (hbox _ hqP) (fun d hd => (Finset.mem_filter.mp (hF hd)).1) (by
        intro d hd
        have hh := (Finset.mem_filter.mp (hF hd)).2
        linarith only [hh,hrho])
    have hsep' := hsep.trans (le_max_left (distance3 z.1 z.2) rho)
    have hm := mul_le_mul_of_nonneg_left hsep' (show 0 ≤ (F.card : ℝ)*rho^2 by positivity)
    have htotal : (F.card : ℝ)*rho*r ≤ 60000 := by
      apply (mul_le_mul_iff_of_pos_right hrho).mp
      nlinarith only [hm,hband]
    have hXtotal : (X.card : ℝ)*rho*r ≤ 60000 := by
      calc
        _ ≤ (F.card : ℝ)*rho*r := by
          nlinarith only [mul_le_mul_of_nonneg_right hcount (show 0 ≤ rho*r by positivity)]
        _ ≤ _ := htotal
    have hlarge : q < 300*Delta := by
      have hh : (1/10:ℝ) < 30*Delta/q := lt_of_not_ge hwsmall
      have hh' := (lt_div_iff₀ hq).mp hh
      linarith only [hh']
    have hh := mul_le_mul_of_nonneg_right hXtotal hq.le
    change (X.card : ℝ)*rho*r*q ≤ _
    nlinarith only [hh,hlarge,hDelta]

/-- Nonconcentration and the actual row overlap bound pay the sum of all
original enlarged-slice populations. No common population bin is supplied. -/
theorem original_nonconcentrated_row_mass (P : Finset Point3) (z : Pair3)
    (F : Finset DirectionLabel) (k : DirectionLabel → ℤ) (rho Delta r q theta : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hr : 0 < r) (hq : 0 < q) (hq1 : q ≤ 1)
    (hwidth : 3*rho ≤ Delta) (hscale : 54*rho ≤ Delta*r) (htheta : theta ≤ 1/2)
    (hzP : z∈P.product P) (hbox : ∀ p∈P, ∀ i, |p i| ≤ 1)
    (hsep : r ≤ distance3 z.1 z.2) (hF : F⊆pairBand rho z.1 z.2)
    (hslabs : ∀ d∈F, z.1∈slabPoints P rho d (k d) ∧ z.2∈slabPoints P rho d (k d))
    (hnoncon : ∀ d∈F,
      ((physicalPairTube3 (enlargedSlice P rho d (k d) Delta) q z).card : ℝ) ≤
        theta*(enlargedSlice P rho d (k d) Delta).card) :
    (∑ d∈F, ((enlargedSlice P rho d (k d) Delta).card : ℝ))*rho*r*q ≤
      43200000*Delta*P.card := by
  let O := fun d => outsideSlice P rho Delta q z d (k d)
  have hOP (d : DirectionLabel) : O d⊆P :=
    Finset.sdiff_subset.trans (Finset.filter_subset _ _)
  have hhalf (d : DirectionLabel) (hd : d∈F) :
      ((enlargedSlice P rho d (k d) Delta).card : ℝ) ≤ 2*(O d).card := by
    have he := Finset.card_sdiff_add_card_eq_card
      (Finset.filter_subset (fun x => x∈physicalTube3 z.1 z.2 q) (enlargedSlice P rho d (k d) Delta))
    have he' : ((O d).card : ℝ)+(physicalPairTube3 (enlargedSlice P rho d (k d) Delta) q z).card=
        (enlargedSlice P rho d (k d) Delta).card := by exact_mod_cast he
    have hh := mul_le_mul_of_nonneg_right htheta
      (Nat.cast_nonneg (enlargedSlice P rho d (k d) Delta).card)
    linarith only [he',hh,hnoncon d hd]
  have hsum : (∑ d∈F, ((O d).card : ℝ))=
      ∑ x∈P, ((F.filter (fun d => x∈O d)).card : ℝ) := by
    have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s:=F) (t:=P) (fun d x => x∈O d)
    have hfull (d : DirectionLabel) : P.bipartiteAbove (fun d x => x∈O d) d=O d := by
      ext x
      simp only [Finset.mem_bipartiteAbove]
      exact ⟨And.right,fun hx => ⟨hOP d hx,hx⟩⟩
    simp only [hfull,Finset.bipartiteBelow] at hh
    exact_mod_cast hh
  have hout : (∑ d∈F, ((O d).card : ℝ))*rho*r*q ≤ 21600000*Delta*P.card := by
    rw [hsum]
    calc
      _ = ∑ x∈P, ((F.filter (fun d => x∈O d)).card : ℝ)*rho*r*q := by
        rw [Finset.sum_mul,Finset.sum_mul,Finset.sum_mul]
      _ ≤ ∑ _x∈P, 21600000*Delta := Finset.sum_le_sum (fun x _hx =>
        original_outside_row_label_count P z F k rho Delta r q x hrho hrho1 hr hq hq1
          hwidth hscale hzP hbox hsep hF hslabs)
      _ = _ := by simp; ring
  have hm : (∑ d∈F, ((enlargedSlice P rho d (k d) Delta).card : ℝ)) ≤
      2*∑ d∈F, ((O d).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hhalf
  have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ rho*r*q by positivity)
  nlinarith only [hh,hout]

def sliceMassCeiling (P : Finset Point3) (Delta r q : ℝ) : ℝ :=
  345600000*Delta*P.card/(r*q)

def smallSliceDirections (P : Finset Point3) (F : Finset DirectionLabel)
    (k : DirectionLabel → ℤ) (rho Delta r q : ℝ) : Finset DirectionLabel :=
  F.filter (fun d => ((enlargedSlice P rho d (k d) Delta).card : ℝ) ≤ sliceMassCeiling P Delta r q)

/-- Removing globally oversized original slices preserves at least half
of the actual nonconcentrated marks on EVERY original pair. The original
pair graph itself is unchanged, and no comparable-mass premise is needed. -/
theorem original_small_slice_row_population (P : Finset Point3) (z : Pair3)
    (F : Finset DirectionLabel) (k : DirectionLabel → ℤ) (rho Delta r q theta : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hr : 0 < r) (hq : 0 < q) (hq1 : q ≤ 1)
    (hwidth : 3*rho ≤ Delta) (hscale : 54*rho ≤ Delta*r) (htheta : theta ≤ 1/2)
    (hzP : z∈P.product P) (hbox : ∀ p∈P, ∀ i, |p i| ≤ 1)
    (hsep : r ≤ distance3 z.1 z.2) (hF : F⊆pairBand rho z.1 z.2)
    (hslabs : ∀ d∈F, z.1∈slabPoints P rho d (k d) ∧ z.2∈slabPoints P rho d (k d))
    (hnoncon : ∀ d∈F,
      ((physicalPairTube3 (enlargedSlice P rho d (k d) Delta) q z).card : ℝ) ≤
        theta*(enlargedSlice P rho d (k d) Delta).card)
    (hdegree : 1 ≤ 4*rho*F.card) :
    smallSliceDirections P F k rho Delta r q⊆F ∧
      1 ≤ 8*rho*(smallSliceDirections P F k rho Delta r q).card ∧
      ∀ d∈smallSliceDirections P F k rho Delta r q,
        ((enlargedSlice P rho d (k d) Delta).card : ℝ) ≤ sliceMassCeiling P Delta r q := by
  let S := smallSliceDirections P F k rho Delta r q
  let B := F\S
  let M := sliceMassCeiling P Delta r q
  have hS : S⊆F := Finset.filter_subset _ _
  have hB : B⊆F := Finset.sdiff_subset
  have hDelta : 0 < Delta := by linarith only [hrho,hwidth]
  have hP : 0 < (P.card : ℝ) := by
    have hpne : P.Nonempty := ⟨z.1,(Finset.mem_product.mp hzP).1⟩
    exact_mod_cast hpne.card_pos
  have hM : M*r*q=345600000*Delta*P.card := by dsimp [M,sliceMassCeiling]; field_simp
  have hbig (d : DirectionLabel) (hd : d∈B) : M ≤ ((enlargedSlice P rho d (k d) Delta).card : ℝ) := by
    obtain ⟨hdF,hdnot⟩ := Finset.mem_sdiff.mp hd
    exact (lt_of_not_ge (fun hh => hdnot (Finset.mem_filter.mpr ⟨hdF,hh⟩))).le
  have hmass : M*B.card ≤ ∑ d∈F, ((enlargedSlice P rho d (k d) Delta).card : ℝ) := by
    calc
      _ = ∑ _d∈B, M := by simp [mul_comm]
      _ ≤ ∑ d∈B, ((enlargedSlice P rho d (k d) Delta).card : ℝ) := Finset.sum_le_sum hbig
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hB (fun _ _ _ => by positivity)
  have hsum := original_nonconcentrated_row_mass P z F k rho Delta r q theta
    hrho hrho1 hr hq hq1 hwidth hscale htheta hzP hbox hsep hF hslabs hnoncon
  have hm := mul_le_mul_of_nonneg_right hmass (show 0 ≤ rho*r*q by positivity)
  have he : (M*(B.card : ℝ))*(rho*r*q)=345600000*Delta*P.card*(rho*B.card) := by
    calc
      _ = (M*r*q)*(rho*B.card) := by ring
      _ = _ := by rw [hM]
  rw [he] at hm
  have hb : 8*rho*B.card ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_left (show 0 < 43200000*Delta*P.card by positivity)).mp
    nlinarith only [hm,hsum]
  have hpartition : (S.card : ℝ)+B.card=F.card := by
    have hh := Finset.card_sdiff_add_card_eq_card hS
    exact_mod_cast (by simpa only [Nat.add_comm] using hh)
  have hp := congrArg (fun t : ℝ => rho*t) hpartition
  refine ⟨hS,?_,?_⟩
  · change 1 ≤ 8*rho*S.card
    nlinarith only [hp,hb,hdegree]
  · intro d hd
    exact (Finset.mem_filter.mp hd).2

end OriginalThreeDimensionalNonconcentratedRowMass
