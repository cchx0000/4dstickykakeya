import Theorems.Thm_StickyKakeya4_original_coefficient_radius
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical

namespace OriginalCoefficientDensityProfile
open OriginalCoefficientRadius GKZOriginalGapEnergy

/-- Maximal density charges EVERY actual original window, regardless of
where any original weak profile began. -/
theorem original_maximal_window (D S : Finset ℝ) {delta kappa : ℝ}
    (hdelta : 0 < delta) (hkappa : 0 ≤ kappa) (hkappa1 : kappa ≤ 1) (hSD : S⊆D)
    (hmax : ∀ T : Finset ℝ, T⊆D →
      (T.card:ℝ)/(radius T delta)^kappa ≤ (S.card:ℝ)/(radius S delta)^kappa)
    (c r : ℝ) (hr : delta ≤ r) :
    ((S.filter (fun x => |x-c| ≤ r)).card:ℝ) ≤
      2*(r/radius S delta)^kappa*S.card := by
  let T := S.filter (fun x => |x-c| ≤ r)
  have hT : T⊆D := (Finset.filter_subset _ _).trans hSD
  have hR : 0 < radius S delta := hdelta.trans_le (mesh_le_radius S delta)
  have hRt : 0 < radius T delta := hdelta.trans_le (mesh_le_radius T delta)
  have hrpos : 0 < r := hdelta.trans_le hr
  have hrad : radius T delta ≤ 2*r := by
    apply radius_le T (by linarith only [hr,hrpos])
    intro x hx y hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    have hab := abs_sub_le x c y
    rw [abs_sub_comm c y] at hab
    linarith only [hx',hy',hab]
  have hclear := (div_le_div_iff₀ (Real.rpow_pos_of_pos hRt kappa)
    (Real.rpow_pos_of_pos hR kappa)).mp (hmax T hT)
  have hpow := Real.rpow_le_rpow hRt.le hrad hkappa
  have h2 : (2:ℝ)^kappa ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ)≤2) hkappa1
  have hp : (radius T delta)^kappa ≤ 2*r^kappa := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hrpos.le] at hpow
    exact hpow.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hrpos.le kappa))
  have hh := mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤S.card from Nat.cast_nonneg _)
  have hfinal : (T.card:ℝ)*(radius S delta)^kappa ≤ 2*r^kappa*S.card := by
    nlinarith only [hclear,hh]
  rw [Real.div_rpow hrpos.le hR.le]
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hR kappa)).mp
  have he : (2*(r^kappa/(radius S delta)^kappa)*(S.card:ℝ))*(radius S delta)^kappa =
      2*r^kappa*S.card := by
    field_simp
  rw [he]
  exact hfinal

/-- Affine normalization is injective on the ACTUAL retained coefficient
points, so the normalized carrier preserves their exact cardinality. -/
lemma original_normalization_injective {R c : ℝ} (hR : 0 < R) :
    Function.Injective (fun x : ℝ => (x-c)/R) := by
  intro x y h
  have he := (div_left_inj' hR.ne').mp h
  linarith only [he]

/-- The normalized maximal-density original source has absolute full
Frostman constant 2 at its true rescaled mesh delta/R. -/
theorem original_normalized_profile (D S : Finset ℝ) {delta kappa : ℝ}
    (hdelta : 0 < delta) (hkappa : 0 ≤ kappa) (hkappa1 : kappa ≤ 1) (hSD : S⊆D)
    (hmax : ∀ T : Finset ℝ, T⊆D →
      (T.card:ℝ)/(radius T delta)^kappa ≤ (S.card:ℝ)/(radius S delta)^kappa)
    (c : ℝ) :
    ScalarFrostman (S.image (fun x => (x-c)/radius S delta))
      (delta/radius S delta) 2 kappa := by
  let R := radius S delta
  have hR : 0 < R := hdelta.trans_le (mesh_le_radius S delta)
  have hinj := original_normalization_injective (c:=c) hR
  intro center r hr _hr1
  have hrr : delta ≤ R*r := by
    have hh := (div_le_iff₀ hR).mp hr
    nlinarith only [hh]
  have hwindow := original_maximal_window D S hdelta hkappa hkappa1 hSD hmax
    (c+R*center) (R*r) hrr
  have hpred : ∀ x : ℝ, |(x-c)/R-center| ≤ r ↔ |x-(c+R*center)| ≤ R*r := by
    intro x
    have he : (x-c)/R-center=(x-(c+R*center))/R := by field_simp; ring
    rw [he,abs_div,abs_of_pos hR]
    constructor
    · intro hh
      have hh' := (div_le_iff₀ hR).mp hh
      nlinarith only [hh']
    · intro hh
      apply (div_le_iff₀ hR).mpr
      nlinarith only [hh]
  have heq : (S.image (fun x => (x-c)/R)).filter (fun x => |x-center| ≤ r)=
      (S.filter (fun x => |x-(c+R*center)| ≤ R*r)).image (fun x => (x-c)/R) := by
    rw [Finset.filter_image]
    congr 1
    ext x
    simp only [Finset.mem_filter,hpred]
  rw [heq,Finset.card_image_of_injective _ hinj,Finset.card_image_of_injective _ hinj]
  have hratio : R*r/R=r := by field_simp
  simpa only [R,hratio] using hwindow

/-- The selected original mass is bounded below by its actual radius,
relative to the original carrier's stated radius upper bound. -/
theorem original_retained_mass (D S : Finset ℝ) {delta kappa B : ℝ}
    (hdelta : 0 < delta) (hkappa : 0 ≤ kappa) (hB : radius D delta ≤ B)
    (hmax : ∀ T : Finset ℝ, T⊆D →
      (T.card:ℝ)/(radius T delta)^kappa ≤ (S.card:ℝ)/(radius S delta)^kappa) :
    (D.card:ℝ)*(radius S delta)^kappa ≤ B^kappa*S.card := by
  have hRD := hdelta.trans_le (mesh_le_radius D delta)
  have hRS := hdelta.trans_le (mesh_le_radius S delta)
  have hh := (div_le_div_iff₀ (Real.rpow_pos_of_pos hRD kappa)
    (Real.rpow_pos_of_pos hRS kappa)).mp (hmax D Finset.Subset.rfl)
  have hpow := Real.rpow_le_rpow hRD.le hB hkappa
  have hm := mul_le_mul_of_nonneg_left hpow (show (0:ℝ)≤S.card from Nat.cast_nonneg _)
  nlinarith only [hh,hm]

/-- Packing and actual maximal-density retention force a quantitative
original radius. This is the input that keeps the normalized mesh fine. -/
theorem original_radius_lower (D S : Finset ℝ) {delta kappa B : ℝ}
    (hdelta : 0 < delta) (hkappa : 0 ≤ kappa) (hS : S.Nonempty)
    (hB : radius D delta ≤ B)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → delta ≤ |x-y|)
    (hmax : ∀ T : Finset ℝ, T⊆D →
      (T.card:ℝ)/(radius T delta)^kappa ≤ (S.card:ℝ)/(radius S delta)^kappa) :
    delta*D.card ≤ 4*B^kappa*(radius S delta)^(1-kappa) := by
  have hR := hdelta.trans_le (mesh_le_radius S delta)
  have hBp := (hdelta.trans_le (mesh_le_radius D delta)).trans_le hB
  have hmass := original_retained_mass D S hdelta hkappa hB hmax
  have hpack := (le_div_iff₀ hdelta).mp (original_radius_packing S hdelta hS hsep)
  have h1 := mul_le_mul_of_nonneg_left hmass hdelta.le
  have h2 := mul_le_mul_of_nonneg_left hpack (Real.rpow_nonneg hBp.le kappa)
  have hid : (radius S delta)^kappa*(radius S delta)^(1-kappa)=radius S delta := by
    rw [← Real.rpow_add hR]
    have he : kappa+(1-kappa)=1 := by ring
    rw [he,Real.rpow_one]
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hR kappa)).mp
  calc
    _ ≤ 4*B^kappa*radius S delta := by nlinarith only [h1,h2]
    _ = 4*B^kappa*((radius S delta)^kappa*(radius S delta)^(1-kappa)) :=
      congrArg (fun z : ℝ => 4*B^kappa*z) hid.symm
    _ = _ := by ring

end OriginalCoefficientDensityProfile
