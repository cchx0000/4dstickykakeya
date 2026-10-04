import Theorems.Thm_StickyKakeya4_original_three_dimensional_common_pair_radius
import Theorems.Thm_StickyKakeya4_original_three_dimensional_heavy_slice_graph
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3400000

noncomputable section
namespace NativeOriginalConcentratedPairGraph
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalHeavySliceGraph
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalSliceMaximizer
open OriginalThreeDimensionalCommonSliceRadius OriginalThreeDimensionalCommonPairRadius
open OriginalPhysicalTubeScaleSelection

/-- Choose a literal ORIGINAL heavy slab code, rather than a supplied
slab or a new direction. -/
def chosenHeavySlabCode (P : Finset Point3) (rho H : ℝ) (z : Pair3) (d : DirectionLabel) : ℤ :=
  if h : heavyWitness P rho H d z then Classical.choose h else 0

theorem chosen_heavy_slab_code_spec (P : Finset Point3) (rho H : ℝ) (z : Pair3) (d : DirectionLabel)
    (hd : d∈goodDirections P rho H z) :
    chosenHeavySlabCode P rho H z d∈P.image (slabCode rho d) ∧
      H ≤ ((slabPoints P rho d (chosenHeavySlabCode P rho H z d)).card : ℝ) ∧
      z.1∈slabPoints P rho d (chosenHeavySlabCode P rho H z d) ∧
      z.2∈slabPoints P rho d (chosenHeavySlabCode P rho H z d) := by
  have hh := (Finset.mem_filter.mp hd).2
  unfold chosenHeavySlabCode
  rw [dif_pos hh]
  exact Classical.choose_spec hh

/-- Concentration is tested on actual original points of the chosen
original heavy slab enlargement. -/
def concentratedDirections (P : Finset Point3) (rho r eta1 e1 e2 : ℝ) (z : Pair3) : Finset DirectionLabel :=
  let H := rho^(1+eta1)*(P.card : ℝ)
  let D := 54*rho/r
  (goodDirections P rho H z).filter (fun d =>
    let Q := enlargedSlice P rho d (chosenHeavySlabCode P rho H z d) D
    D^e2*(Q.card : ℝ) < (physicalPairTube3 Q (D^e1) z).card)

def concentratedPairGraph (P : Finset Point3) (G : Finset Pair3)
    (rho r eta1 e1 e2 b : ℝ) : Finset Pair3 :=
  G.filter (fun z => b ≤ rho*((concentratedDirections P rho r eta1 e1 e2 z).card : ℝ))

/-- The same actual selected source maximum supplies the upper scale in
(251), including the fixed factor from upward dyadic rounding. -/
theorem original_selected_concentrated_radius_upper
    (P : Finset Point3) (z : Pair3) (rho r eta1 e1 e2 : ℝ) (n j : ℕ) (d : DirectionLabel)
    (hrho : 0 < rho) (hr : 0 < r) (hr1 : r ≤ 1) (he1 : 0 < e1) (he11 : e1 ≤ 1) (he2 : 0 < e2)
    (hmesh : rho=dyadicRadius n) (hDelta : 54*rho/r ≤ 1)
    (hd : d∈concentratedDirections P rho r eta1 e1 e2 z)
    (hchosen : chosenSliceIndex P z (chosenHeavySlabCode P rho (rho^(1+eta1)*P.card) z)
      rho (54*rho/r) (200*e2/e1) n d=j) :
    dyadicRadius j ≤ 2*(54*rho/r)^((199/200:ℝ)*e1) := by
  let D := 54*rho/r
  let alpha := 200*e2/e1
  let kd := chosenHeavySlabCode P rho (rho^(1+eta1)*P.card) z d
  let Q := enlargedSlice P rho d kd D
  have hD : 0 < D := by dsimp [D]; positivity
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hDr : D*r=54*rho := by dsimp [D]; field_simp
  have hwidth : 3*rho ≤ D := by nlinarith only [hDr,mul_le_mul_of_nonneg_left hr1 hD.le,hrho.le]
  have hdgood := (Finset.mem_filter.mp hd).1
  have hcode := chosen_heavy_slab_code_spec P rho (rho^(1+eta1)*P.card) z d hdgood
  have hpQ : z.1∈Q := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hcode.2.2.1).1,
    (OriginalThreeDimensionalUnitSlabs.original_slab_in_unit_slab P rho d kd hrho.le z.1 hcode.2.2.1).trans hwidth⟩
  have hQ : 0 < (Q.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨z.1,hpQ⟩
  have hconc : D^e2*(Q.card : ℝ) ≤ (physicalPairTube3 Q (D^e1) z).card := (Finset.mem_filter.mp hd).2.le
  have hq : 0 < D^e1 := Real.rpow_pos_of_pos hD e1
  have hq1 : D^e1 ≤ 1 := Real.rpow_le_one hD.le hDelta he1.le
  have hDq : D ≤ D^e1 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hD hDelta he11
  obtain ⟨j0,hj0,hqj0,hj0q⟩ := dyadic_radius_cover n (D^e1)
    (by rw [← hmesh]; linarith only [hwidth,hDq,hq.le]) hq1
  have hp (i : ℕ) : 0 < dyadicRadius i := by dsimp [dyadicRadius]; positivity
  have hmax := (chosen_slice_index_spec P z (chosenHeavySlabCode P rho (rho^(1+eta1)*P.card) z)
    rho D alpha n d).2 j0 hj0
  rw [hchosen] at hmax
  have hconc' := hconc.trans (Nat.cast_le.mpr (Finset.card_le_card (original_physical_tube3_mono Q z hqj0)))
  have hcross := (div_le_div_iff₀ (Real.rpow_pos_of_pos (hp j0) alpha)
    (Real.rpow_pos_of_pos (hp j) alpha)).mp hmax
  have hpop := mul_le_mul_of_nonneg_right hconc' (Real.rpow_nonneg (hp j).le alpha)
  have htotal : ((physicalPairTube3 Q (dyadicRadius j) z).card : ℝ) ≤ Q.card :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  have hcount := hpop.trans (hcross.trans (mul_le_mul_of_nonneg_right htotal (Real.rpow_nonneg (hp j0).le alpha)))
  have hpower : D^e2*(dyadicRadius j)^alpha ≤ (2*D^e1)^alpha := by
    have hh : D^e2*(dyadicRadius j)^alpha ≤ (dyadicRadius j0)^alpha := by
      apply (mul_le_mul_iff_of_pos_right hQ).mp
      nlinarith only [hcount]
    exact hh.trans (Real.rpow_le_rpow (hp j0).le hj0q ha.le)
  have hidentity : D^e2*(2*D^((199/200:ℝ)*e1))^alpha=(2*D^e1)^alpha := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hD.le ((199/200:ℝ)*e1)),
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hD.le e1)]
    simp only [← Real.rpow_mul hD.le]
    calc
      _ = 2^alpha*(D^e2*D^(((199/200:ℝ)*e1)*alpha)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hD]
        congr 2
        dsimp [alpha]
        field_simp
        ring
  apply (Real.rpow_le_rpow_iff (hp j).le (show 0 ≤ 2*D^((199/200:ℝ)*e1) by positivity) ha).mp
  apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos hD e2)).mp
  rw [hidentity]
  exact hpower

/-- The actual concentrated-pair graph is constructed here. If it is
nonempty, genuine direction and pair radius pigeonholes produce an
original rich-tube graph with explicit menu losses and actual witnesses.
No discarded-graph bound, witness family or hairbrush gain is supplied. -/
theorem original_concentrated_graph_rich_radius
    (P : Finset Point3) (G : Finset Pair3) (rho r eta1 e1 e2 b : ℝ) (n M : ℕ)
    (hrho : 0 < rho) (hr : 0 < r) (hr1 : r ≤ 1) (he1 : 0 < e1) (he11 : e1 ≤ 1)
    (he2 : 0 < e2) (halpha : 200*e2/e1 ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hmesh : rho=dyadicRadius n) (hcontract : (dyadicRadius M)^(200*e2/e1) ≤ 1/2)
    (hDelta : 54*rho/r ≤ 1) (hGP : G⊆P.product P)
    (hbox : ∀ p∈P, ∀ i, |p i| ≤ 1) (hsep : ∀ z∈G, r ≤ distance3 z.1 z.2) :
    let C := concentratedPairGraph P G rho r eta1 e1 e2 b
    let F := concentratedDirections P rho r eta1 e1 e2
    let k := chosenHeavySlabCode P rho (rho^(1+eta1)*P.card)
    let D := 54*rho/r
    let alpha := 200*e2/e1
    let nu := b/((n:ℝ)+1)*(dyadicRadius M*r^2/4665600000*rho^eta1*D^(e2+alpha*(1-e1)))
    C=∅ ∨ (0 < nu ∧ ∃ j : ℕ, j ≤ n ∧
      dyadicRadius j ≤ 2*D^((199/200:ℝ)*e1) ∧ ∃ H : Finset Pair3,
      H⊆C ∧ H.Nonempty ∧ C.card ≤ (n+1)*H.card ∧
      ∀ z∈H, nu*dyadicRadius j*P.card ≤ (physicalPairTube3 P (dyadicRadius j) z).card ∧
        ∃ S : Finset DirectionLabel,
          S=(F z).filter (fun d => chosenSliceIndex P z (k z) rho D alpha n d=j) ∧
          S⊆F z ∧ S.Nonempty ∧ (F z).card ≤ (n+1)*S.card) := by
  let C := concentratedPairGraph P G rho r eta1 e1 e2 b
  let F := concentratedDirections P rho r eta1 e1 e2
  let k := chosenHeavySlabCode P rho (rho^(1+eta1)*P.card)
  let D := 54*rho/r
  let alpha := 200*e2/e1
  by_cases hC : C.Nonempty
  · right
    have hCG : C⊆G := Finset.filter_subset _ _
    have hFgood (z : Pair3) (d : DirectionLabel) (hd : d∈F z) :
        d∈goodDirections P rho (rho^(1+eta1)*P.card) z := (Finset.mem_filter.mp hd).1
    have hcodes (z : Pair3) (d : DirectionLabel) (hd : d∈F z) :=
      chosen_heavy_slab_code_spec P rho (rho^(1+eta1)*P.card) z d (hFgood z d hd)
    obtain ⟨hnu,j,hj,H,hHC,hHn,hHmass,hdata⟩ := exists_original_common_rich_pair_radius P C F k rho r eta1 e1 e2 b n M
      hrho hr hr1 he1 he11 he2 halpha hb hb1 hmesh hcontract hDelta hC (hCG.trans hGP)
      hbox (fun z hz => hsep z (hCG hz))
      (fun _ hz => (Finset.mem_filter.mp hz).2)
      (fun z _hz d hd => (Finset.mem_filter.mp (hFgood z d hd)).1)
      (fun z _hz d hd => (hcodes z d hd).2.2)
      (fun z _hz d hd => (hcodes z d hd).2.1)
      (fun _ _hz _ hd => (Finset.mem_filter.mp hd).2.le)
    let z0 := hHn.choose
    have hz0 : z0∈H := hHn.choose_spec
    obtain ⟨_hpop,S,hSeq,hSF,hSn,_hSmass⟩ := hdata z0 hz0
    let d := hSn.choose
    have hdS : d∈S := hSn.choose_spec
    have hdChosen : d∈(F z0).filter (fun d => chosenSliceIndex P z0 (k z0) rho D alpha n d=j) := by
      rw [← hSeq]
      exact hdS
    have hupper := original_selected_concentrated_radius_upper P z0 rho r eta1 e1 e2 n j d
      hrho hr hr1 he1 he11 he2 hmesh hDelta (hSF hdS) (Finset.mem_filter.mp hdChosen).2
    exact ⟨hnu,j,hj,hupper,H,hHC,hHn,hHmass,hdata⟩
  · left
    exact Finset.not_nonempty_iff_eq_empty.mp hC

/-- The actual complement retains many actual original heavy slabs with
the desired nonconcentration count. The only missing global input is an
upper bound for the constructed concentrated-pair graph itself. -/
theorem retained_unconcentrated_direction_population
    (P : Finset Point3) (G : Finset Pair3) (rho r eta1 e1 e2 : ℝ) (z : Pair3)
    (hz : z∈retainedPairs P G rho (rho^(1+eta1)*P.card))
    (hnot : z∉concentratedPairGraph P (retainedPairs P G rho (rho^(1+eta1)*P.card)) rho r eta1 e1 e2 (1/4)) :
    let F := concentratedDirections P rho r eta1 e1 e2 z
    let U := goodDirections P rho (rho^(1+eta1)*P.card) z\F
    let k := chosenHeavySlabCode P rho (rho^(1+eta1)*P.card) z
    let D := 54*rho/r
    1 ≤ 4*rho*(U.card : ℝ) ∧
      ∀ d∈U, k d∈P.image (slabCode rho d) ∧
        rho^(1+eta1)*(P.card : ℝ) ≤ (slabPoints P rho d (k d)).card ∧
        z.1∈slabPoints P rho d (k d) ∧ z.2∈slabPoints P rho d (k d) ∧
        ((physicalPairTube3 (enlargedSlice P rho d (k d) D) (D^e1) z).card : ℝ) ≤
          D^e2*(enlargedSlice P rho d (k d) D).card := by
  let F := concentratedDirections P rho r eta1 e1 e2 z
  let B := goodDirections P rho (rho^(1+eta1)*P.card) z
  let U := B\F
  have hFB : F⊆B := Finset.filter_subset _ _
  have hgood : 1 ≤ 2*rho*(B.card : ℝ) := (Finset.mem_filter.mp hz).2
  have hsmall : rho*(F.card : ℝ) < 1/4 := by
    by_contra hh
    exact hnot (Finset.mem_filter.mpr ⟨hz,le_of_not_gt hh⟩)
  have hpart := Finset.card_sdiff_add_card_eq_card hFB
  have hpartR : (U.card : ℝ)+F.card=B.card := by exact_mod_cast hpart
  have hpartRho := congrArg (fun x : ℝ => rho*x) hpartR
  refine ⟨by nlinarith only [hgood,hsmall,hpartRho],?_⟩
  intro d hd
  obtain ⟨hdB,hdnot⟩ := Finset.mem_sdiff.mp hd
  obtain ⟨hk,hmass,hp,hq⟩ := chosen_heavy_slab_code_spec P rho (rho^(1+eta1)*P.card) z d hdB
  refine ⟨hk,hmass,hp,hq,?_⟩
  apply le_of_not_gt
  intro hc
  exact hdnot (Finset.mem_filter.mpr ⟨hdB,hc⟩)

end NativeOriginalConcentratedPairGraph
