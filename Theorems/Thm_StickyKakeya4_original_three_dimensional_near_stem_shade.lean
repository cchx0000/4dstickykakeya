import Theorems.Thm_StickyKakeya4_original_three_dimensional_shade_local_count
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
namespace OriginalThreeDimensionalNearStemShade
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTubeCells OriginalThreeDimensionalShadeLocalCount

/-- A transverse actual brush tube meets the stem neighborhood only in a
short axial interval. Its actual cube-injective shade supplies the count. -/
theorem original_shade_near_stem_count (Y : Finset Point3) (z stem : Pair3)
    (i j : Fin 3) (rho s theta : ℝ) (hrho : 0<rho) (hrs : rho ≤ s)
    (htheta : 0<theta) (htheta1 : theta ≤ 1)
    (hz : z.2 i-z.1 i ≠ 0) (hs : stem.2 i-stem.1 i ≠ 0)
    (hzmax : ∀ k, |z.2 k-z.1 k| ≤ |z.2 i-z.1 i|)
    (hsmax : ∀ k, |stem.2 k-stem.1 k| ≤ |stem.2 i-stem.1 i|)
    (hgap : theta ≤ |slope z i j-slope stem i j|)
    (hinj : Set.InjOn (cell rho) Y)
    (hshade : ∀ x∈Y,x∈physicalTube3 z.1 z.2 (4*rho)) :
    ((Y.filter (fun x => x∈physicalTube3 stem.1 stem.2 s)).card : ℝ)*rho ≤ 24000*s/theta := by
  let B := Y.filter (fun x => x∈physicalTube3 stem.1 stem.2 s)
  let A := slope z i j-slope stem i j
  let D := offset z i j-offset stem i j
  have hspos : 0<s := hrho.trans_le hrs
  have hA : 0 < |A| := htheta.trans_le hgap
  have hAne : A ≠ 0 := abs_pos.mp hA
  have hinterval (x : Point3) (hx : x∈B) :
      -D/A-10*s/theta ≤ x i ∧ x i ≤ (-D/A-10*s/theta)+20*s/theta := by
    obtain ⟨hxY,hxstem⟩ := Finset.mem_filter.mp hx
    have hzres := original_tube_graph_residual z i x (4*rho) hz hzmax (hshade x hxY) j
    have hsres := original_tube_graph_residual stem i x s hs hsmax hxstem j
    have ht := abs_sub (x j-(slope stem i j*x i+offset stem i j))
      (x j-(slope z i j*x i+offset z i j))
    have he : (x j-(slope stem i j*x i+offset stem i j))-
        (x j-(slope z i j*x i+offset z i j))=A*x i+D := by dsimp [A,D]; ring
    rw [he] at ht
    have hnum : |A*x i+D| ≤ 10*s := by linarith only [ht,hzres,hsres,hrs]
    have heq : x i+D/A=(A*x i+D)/A := by field_simp
    have hv : |x i+D/A| ≤ 10*s/theta := by
      rw [heq,abs_div]
      exact (div_le_div_of_nonneg_right hnum hA.le).trans
        (div_le_div_of_nonneg_left (by positivity) htheta hgap)
    have hlo := (abs_le.mp hv).1
    have hhi := (abs_le.mp hv).2
    ring_nf at hlo hhi ⊢
    constructor <;> linarith only [hlo,hhi]
  have hlen : rho ≤ 20*s/theta := by
    apply (le_div_iff₀ htheta).mpr
    have hm := mul_le_mul_of_nonneg_left htheta1 hrho.le
    nlinarith only [hm,hrs,hspos]
  have hc := original_shade_interval_count B z i rho (-D/A-10*s/theta) (20*s/theta)
    hrho hlen hz hzmax (hinj.mono (Finset.filter_subset _ _))
    (fun x hx => hshade x (Finset.mem_filter.mp hx).1) hinterval
  dsimp [B] at hc
  convert hc using 1; ring

/-- Delete the actual near-stem part while retaining at least half the
original shade population; the discarded bound is derived above. -/
theorem original_shade_outside_stem_mass (Y : Finset Point3) (z stem : Pair3)
    (i j : Fin 3) (rho s theta beta : ℝ) (hrho : 0<rho) (hrs : rho ≤ s)
    (htheta : 0<theta) (htheta1 : theta ≤ 1) (hbeta : 0 ≤ beta)
    (hbudget : 96000*s ≤ beta*theta)
    (hz : z.2 i-z.1 i ≠ 0) (hs : stem.2 i-stem.1 i ≠ 0)
    (hzmax : ∀ k, |z.2 k-z.1 k| ≤ |z.2 i-z.1 i|)
    (hsmax : ∀ k, |stem.2 k-stem.1 k| ≤ |stem.2 i-stem.1 i|)
    (hgap : theta ≤ |slope z i j-slope stem i j|)
    (hinj : Set.InjOn (cell rho) Y)
    (hshade : ∀ x∈Y,x∈physicalTube3 z.1 z.2 (4*rho))
    (hmass : beta ≤ rho*Y.card) :
    beta/2 ≤ rho*((Y.filter (fun x => x∉physicalTube3 stem.1 stem.2 s)).card : ℝ) := by
  have hc := original_shade_near_stem_count Y z stem i j rho s theta hrho hrs htheta htheta1
    hz hs hzmax hsmax hgap hinj hshade
  have hsmall : 24000*s/theta ≤ beta/4 := by
    apply (div_le_iff₀ htheta).mpr
    nlinarith only [hbudget]
  have hp := Finset.card_filter_add_card_filter_not (s:=Y)
    (fun x => x∈physicalTube3 stem.1 stem.2 s)
  have hpR : ((Y.filter (fun x => x∈physicalTube3 stem.1 stem.2 s)).card : ℝ)+
      ((Y.filter (fun x => x∉physicalTube3 stem.1 stem.2 s)).card : ℝ)=Y.card := by exact_mod_cast hp
  have he := congrArg (fun t : ℝ => rho*t) hpR
  nlinarith only [hc,hsmall,he,hmass,hbeta]

end OriginalThreeDimensionalNearStemShade
