import Theorems.Thm_StickyKakeya4_original_three_dimensional_nonconcentrated_row_mass
import Theorems.Thm_StickyKakeya4_native_original_concentrated_slice_closure
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3800000

noncomputable section
namespace OriginalThreeDimensionalChosenSliceTube
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalUnitSlabs OriginalThreeDimensionalSliceMaximizer
open OriginalThreeDimensionalNonconcentratedRowMass
open OriginalThreeDimensionalSliceParameterChoice OriginalThreeDimensionalNativeSliceScale
open NativeQuarterScaleParameters

/-- The chosen original slab code, not a new existential slab, contains
the entire bounded original tube after the actual enlargement. -/
theorem original_chosen_slice_contains_tube (P : Finset Point3) (z : Pair3)
    (rho Delta r : ℝ) (d : DirectionLabel) (k : ℤ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hscale : 54*rho ≤ Delta*r) (hbox : ∀ x∈P, ∀ j, |x j| ≤ 1)
    (hsep : r ≤ distance3 z.1 z.2)
    (hslab : z.1∈slabPoints P rho d k ∧ z.2∈slabPoints P rho d k) :
    physicalPairTube3 (enlargedSlice P rho d k Delta) rho z=physicalPairTube3 P rho z := by
  have he (x : Point3) : chartValue d.1 (rho*d.2.1/normalLength rho d)
      (rho*d.2.2/normalLength rho d) (1/normalLength rho d) x=unitValue rho d x := by
    dsimp [chartValue,unitValue,value,projection]
    ring
  have hmem : physicalPairTube3 P rho z⊆enlargedSlice P rho d k Delta := by
    intro x hx
    obtain ⟨hxP,hxt⟩ := Finset.mem_filter.mp hx
    have hh := original_physical_tube_in_unit_slab z.1 z.2 x d.1
      (rho*d.2.1/normalLength rho d) (rho*d.2.2/normalLength rho d)
      (1/normalLength rho d) (rho*k/normalLength rho d) rho r hrho hrho1 hr hr1
      (original_normal_coefficients_unit rho d)
      (hbox _ (Finset.mem_filter.mp hslab.1).1)
      (fun j => (hbox x hxP j).trans (by norm_num)) hsep
      (by simpa only [he] using original_slab_in_unit_slab P rho d k hrho.le z.1 hslab.1)
      (by simpa only [he] using original_slab_in_unit_slab P rho d k hrho.le z.2 hslab.2) hxt
    have hupper : 54*rho/r ≤ Delta := (div_le_iff₀ hr).mpr hscale
    have hh' : |unitValue rho d x-rho*k/normalLength rho d| ≤ 54*rho/r := by
      simpa only [he] using hh
    exact Finset.mem_filter.mpr ⟨hxP,hh'.trans hupper⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hxQ,hxt⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxQ).1,hxt⟩
  · intro hx
    exact Finset.mem_filter.mpr ⟨hmem hx,(Finset.mem_filter.mp hx).2⟩

/-- The exact global slice ceiling retains both inverse-r factors. -/
lemma original_slice_ceiling_identity (P : Finset Point3) (rho r q : ℝ)
    (hr : 0 < r) (hq : 0 < q) :
    sliceMassCeiling P (54*rho/r) r q=
      18662400000*rho*P.card/(r^2*q) := by
  unfold sliceMassCeiling
  field_simp
  ring

/-- A true cutoff converts the actual global slice ceiling to the paper's
original-source mass bound. The coefficient and the two r powers are paid,
with q=delta^((51/50)epsilon) and r=delta^(2eta). -/
theorem exists_original_slice_mass_power_cutoff (zeta epsilon eta : ℝ)
    (hzeta : 0 < zeta) (_hepsilon : 0 < epsilon) (hepsmall : epsilon ≤ zeta/100)
    (_heta : 0 < eta) (hetasmall : eta ≤ zeta/100) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 → ∀ rho : ℝ, 0 ≤ rho →
        ∀ P : Finset Point3,
          sliceMassCeiling P (54*rho/delta^(2*eta)) (delta^(2*eta))
            (delta^((51/50:ℝ)*epsilon)) ≤ delta^(-zeta/10)*rho*P.card := by
  let a := (51/50:ℝ)*epsilon
  let b := zeta/10-4*eta-a
  have hb : 0 < b := by dsimp [b,a]; linarith only [hzeta,hepsmall,hetasmall]
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_small_power_cutoff hb
    (by norm_num : (0:ℝ) < 1/18662400000)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall rho hrho P
  rw [original_slice_ceiling_identity P rho (delta^(2*eta)) (delta^a) (by positivity) (by positivity)]
  have hrpow : (delta^(2*eta))^2*delta^a=delta^(4*eta+a) := by
    rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_add hd]
    congr 1
    ring
  rw [hrpow]
  have hc : 18662400000*delta^b ≤ 1 := by
    have hh := hcut delta hd hsmall
    linarith only [hh]
  have he : delta^b*delta^(-zeta/10)=delta^(-(4*eta+a)) := by
    rw [← Real.rpow_add hd]
    congr 1
    dsimp [b]
    ring
  have hcoeff := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hd.le (-zeta/10))
  have hcoeff' : 18662400000*delta^(-(4*eta+a)) ≤ delta^(-zeta/10) := by
    rw [mul_assoc,he] at hcoeff
    simpa only [one_mul] using hcoeff
  have hscaled := mul_le_mul_of_nonneg_right hcoeff' (show 0 ≤ rho*P.card by positivity)
  rw [Real.rpow_neg hd.le] at hscaled
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hscaled

/-- Once the actual original slice ceiling is known, the original rich
pair input strengthens to a relative ORIGINAL-Q tube population. No points
of the tube are moved or silently replaced by the regularized core. -/
theorem original_chosen_slice_relative_tube_gain (P : Finset Point3) (z : Pair3)
    (delta rho r zeta A : ℝ) (d : DirectionLabel) (k : ℤ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hzeta : 0 < zeta) (hA : 0 < A)
    (hbox : ∀ x∈P, ∀ j, |x j| ≤ 1) (hsep : r ≤ distance3 z.1 z.2)
    (hslab : z.1∈slabPoints P rho d k ∧ z.2∈slabPoints P rho d k)
    (hgain : delta^(-(zeta-zeta/100))*rho^(2-zeta/100)*P.card ≤
      A*(physicalPairTube3 P rho z).card)
    (hcut : A*delta^(zeta/2) ≤ 1)
    (hmass : ((enlargedSlice P rho d k (54*rho/r)).card : ℝ) ≤ delta^(-zeta/10)*rho*P.card) :
    delta^(-zeta/3)*rho*(enlargedSlice P rho d k (54*rho/r)).card ≤
      (physicalPairTube3 (enlargedSlice P rho d k (54*rho/r)) rho z).card := by
  rw [original_chosen_slice_contains_tube P z rho (54*rho/r) r d k hrho hrho1 hr hr1
    (by field_simp; norm_num) hbox hsep hslab]
  have hrpow : rho^2 ≤ rho^(2-zeta/100) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hrho hrho1
      (show 2-zeta/100 ≤ (2:ℝ) by linarith only [hzeta])
  have habs : delta^(-(zeta-zeta/100))*rho^2*P.card ≤ A*(physicalPairTube3 P rho z).card := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrpow (Real.rpow_nonneg hd.le (-(zeta-zeta/100))))
      (Nat.cast_nonneg P.card)
    exact hh.trans hgain
  have hpower : delta^((zeta-zeta/100)-((zeta/3)+(zeta/10))) ≤ delta^(zeta/2) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith only [hzeta])
  have hscalar := (mul_le_mul_of_nonneg_left hpower hA.le).trans hcut
  have hid : delta^((zeta-zeta/100)-((zeta/3)+(zeta/10)))*delta^(-(zeta-zeta/100))=
      delta^(-zeta/3)*delta^(-zeta/10) := by
    rw [← Real.rpow_add hd,← Real.rpow_add hd]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_right hscalar (Real.rpow_nonneg hd.le (-(zeta-zeta/100)))
  have hcoeff : A*(delta^(-zeta/3)*delta^(-zeta/10)) ≤ delta^(-(zeta-zeta/100)) := by
    rw [mul_assoc,hid] at hh
    simpa only [one_mul] using hh
  apply (mul_le_mul_iff_of_pos_left hA).mp
  have h1 := mul_le_mul_of_nonneg_left hmass (show 0 ≤ A*delta^(-zeta/3)*rho by positivity)
  have h2 := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ rho^2*P.card by positivity)
  nlinarith only [h1,h2,habs]

end OriginalThreeDimensionalChosenSliceTube
