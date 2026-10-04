import Theorems.Thm_StickyKakeya4_original_three_dimensional_heavy_slabs
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalHeavySliceGraph
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs

def goodDirections (P : Finset Point3) (rho H : ℝ) (z : Pair3) : Finset DirectionLabel :=
  (pairBand rho z.1 z.2).filter (fun d => heavyWitness P rho H d z)
def badDirections (P : Finset Point3) (rho H : ℝ) (z : Pair3) : Finset DirectionLabel :=
  (pairBand rho z.1 z.2).filter (fun d => ¬heavyWitness P rho H d z)
def retainedPairs (P : Finset Point3) (G : Finset Pair3) (rho H : ℝ) : Finset Pair3 :=
  G.filter (fun z => (1:ℝ)≤2*rho*(goodDirections P rho H z).card)

lemma original_bad_incidence_double_count (P : Finset Point3) (G : Finset Pair3) (rho H : ℝ) :
    ∑ z∈G, (badDirections P rho H z).card=
      ∑ d∈normalGrid rho, (badDirectionPairs G P rho H d).card := by
  have he (z : Pair3) : badDirections P rho H z=
      (normalGrid rho).filter (fun d => d∈pairBand rho z.1 z.2 ∧ ¬heavyWitness P rho H d z) := by
    ext d
    simp only [badDirections,pairBand,Finset.mem_filter]
    tauto
  simp_rw [he,badDirectionPairs,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]

lemma original_bad_incidence_bound (P : Finset Point3) (G : Finset Pair3) (rho H : ℝ)
    (hrho : 0<rho) (hH : 0≤H) (hG : G⊆P.product P) :
    (∑ z∈G, ((badDirections P rho H z).card : ℝ))≤
      (normalGrid rho).card*(P.card*H) := by
  have he := original_bad_incidence_double_count P G rho H
  have heR : (∑ z∈G, ((badDirections P rho H z).card : ℝ))=
      ∑ d∈normalGrid rho, ((badDirectionPairs G P rho H d).card : ℝ) := by exact_mod_cast he
  rw [heR]
  calc
    _ ≤ ∑ _d∈normalGrid rho, ((P.card : ℝ)*H) :=
      Finset.sum_le_sum (fun d _hd => original_nonheavy_pair_bound P G rho H d hrho hH hG)
    _ = _ := by simp

/-- The actual shared direction grid and literal heavy slabs retain most
of the ORIGINAL ordered graph. Every surviving pair belongs to many real
heavy slices; neither a spherical incidence estimate nor a row cap is assumed. -/
theorem original_heavy_slice_graph (P : Finset Point3) (G : Finset Pair3) (rho H : ℝ)
    (hrho : 0<rho) (hrho1 : rho≤1) (hH : 0≤H) (hG : G⊆P.product P)
    (hbox : ∀ p∈P, ∀ i, |p i|≤1) (hdistinct : ∀ z∈G, z.1≠z.2) :
    retainedPairs P G rho H⊆G ∧
    (G.card : ℝ)≤(retainedPairs P G rho H).card+216*H*(P.card : ℝ)/rho ∧
    ∀ z∈retainedPairs P G rho H,
      1≤2*rho*(goodDirections P rho H z).card := by
  let B := G.filter (fun z => ¬(1:ℝ)≤2*rho*(goodDirections P rho H z).card)
  have hBG : B⊆G := Finset.filter_subset _ _
  have hone : ∀ z∈B, (1:ℝ)≤2*rho*(badDirections P rho H z).card := by
    intro z hz
    obtain ⟨hzG,hbad⟩ := Finset.mem_filter.mp hz
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp (hG hzG)
    have hband := original_pair_band_mass rho z.1 z.2 hrho hrho1 (hdistinct z hzG)
      (hbox z.1 hp) (hbox z.2 hq)
    have hpart := Finset.card_filter_add_card_filter_not
      (s:=pairBand rho z.1 z.2) (fun d => heavyWitness P rho H d z)
    have hpartR : ((goodDirections P rho H z).card : ℝ)+(badDirections P rho H z).card=
        (pairBand rho z.1 z.2).card := by exact_mod_cast hpart
    have hsmall := lt_of_not_ge hbad
    have hpm := congrArg (fun x : ℝ => rho*x) hpartR
    nlinarith only [hband,hpm,hsmall]
  have hsum : (B.card : ℝ)≤2*rho*∑ z∈G, ((badDirections P rho H z).card : ℝ) := by
    calc
      _ = ∑ _z∈B, (1:ℝ) := by simp
      _ ≤ ∑ z∈B, 2*rho*((badDirections P rho H z).card : ℝ) := Finset.sum_le_sum hone
      _ = 2*rho*∑ z∈B, ((badDirections P rho H z).card : ℝ) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hBG (fun _ _ _ => by positivity)) (by positivity)
  have hcount := original_bad_incidence_bound P G rho H hrho hH hG
  have hupper := hsum.trans (mul_le_mul_of_nonneg_left hcount (by positivity : (0:ℝ)≤2*rho))
  have hgrid := normal_grid_card rho hrho hrho1
  have hsmallB : (B.card : ℝ)≤216*H*(P.card : ℝ)/rho := by
    apply (le_div_iff₀ hrho).mpr
    have hh := mul_le_mul_of_nonneg_right hupper hrho.le
    have hc := mul_le_mul_of_nonneg_right hgrid
      (show (0:ℝ)≤2*H*P.card by positivity)
    nlinarith only [hh,hc]
  have hpartition := Finset.card_filter_add_card_filter_not (s:=G)
    (fun z => (1:ℝ)≤2*rho*(goodDirections P rho H z).card)
  have hpartitionR : ((retainedPairs P G rho H).card : ℝ)+B.card=G.card := by exact_mod_cast hpartition
  refine ⟨Finset.filter_subset _ _,by linarith only [hsmallB,hpartitionR],?_⟩
  intro z hz
  exact (Finset.mem_filter.mp hz).2

/-- The source-scale choice H=rho^(1+eta)|P| yields the exact small
original-pair error used in the three-dimensional radial proof's Step1. -/
theorem original_power_heavy_slice_graph (P : Finset Point3) (G : Finset Pair3) (rho eta : ℝ)
    (hrho : 0<rho) (hrho1 : rho≤1) (hG : G⊆P.product P)
    (hbox : ∀ p∈P, ∀ i, |p i|≤1) (hdistinct : ∀ z∈G, z.1≠z.2) :
    ∃ G' : Finset Pair3, G'⊆G ∧
      (G.card : ℝ)≤G'.card+216*rho^eta*(P.card : ℝ)^2 ∧
      ∀ z∈G', 1≤2*rho*(goodDirections P rho (rho^(1+eta)*P.card) z).card := by
  have hH : 0≤rho^(1+eta)*(P.card : ℝ) := by positivity
  obtain ⟨hsub,hcount,hgood⟩ := original_heavy_slice_graph P G rho (rho^(1+eta)*P.card)
    hrho hrho1 hH hG hbox hdistinct
  have he : 216*(rho^(1+eta)*(P.card : ℝ))*P.card/rho=
      216*rho^eta*(P.card : ℝ)^2 := by
    rw [Real.rpow_add hrho,Real.rpow_one]
    field_simp
  rw [he] at hcount
  exact ⟨retainedPairs P G rho (rho^(1+eta)*P.card),hsub,hcount,hgood⟩

end OriginalThreeDimensionalHeavySliceGraph
