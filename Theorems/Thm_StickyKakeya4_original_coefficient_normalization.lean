import Theorems.Thm_StickyKakeya4_original_coefficient_density_profile
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical

namespace OriginalCoefficientNormalization
open OriginalCoefficientRadius OriginalCoefficientDensityProfile GKZOriginalGapEnergy

/-- Original separation and a quantified original cardinality bound force
an explicitly fine normalized mesh. The exponent is not inferred from a
profile at unavailable scales. -/
theorem original_normalized_mesh_bound {delta R B kappa b N : ℝ}
    (hdelta : 0 < delta) (hR : 0 < R) (hB : 0 < B) (hkappa : kappa < 1)
    (hradius : delta*N ≤ 4*B^kappa*R^(1-kappa))
    (hmass : 4*B^kappa*delta^(b*(1-kappa)) ≤ delta*N) :
    delta^b ≤ R ∧ delta/R ≤ delta^(1-b) := by
  have hfactor : 0 < 4*B^kappa := by positivity
  have hp : delta^(b*(1-kappa)) ≤ R^(1-kappa) :=
    (mul_le_mul_iff_right₀ hfactor).mp (hmass.trans hradius)
  have hpow : (delta^b)^(1-kappa) ≤ R^(1-kappa) := by
    simpa only [← Real.rpow_mul hdelta.le] using hp
  have hsmall : delta^b ≤ R := (Real.rpow_le_rpow_iff
    (Real.rpow_nonneg hdelta.le b) hR.le (by linarith only [hkappa])).mp hpow
  refine ⟨hsmall,?_⟩
  calc
    delta/R ≤ delta/delta^b := div_le_div_of_nonneg_left hdelta.le
      (Real.rpow_pos_of_pos hdelta b) hsmall
    _ = delta^(1-b) := by rw [Real.rpow_sub hdelta,Real.rpow_one]

/-- A genuine original-source normalization. It retains actual points and
exact cardinality, constructs the full absolute profile at the true mesh,
and records both retained mass and the original radius lower bound. -/
theorem exists_original_normalized_coefficients (D : Finset ℝ)
    {delta kappa B : ℝ} (hD : D.Nonempty) (hdelta : 0 < delta)
    (hkappa : 0 ≤ kappa) (hkappa1 : kappa ≤ 1) (hdB : delta ≤ B)
    (hbox : ∀ x∈D, ∀ y∈D, |x-y| ≤ B)
    (hsep : ∀ x∈D, ∀ y∈D, x≠y → delta ≤ |x-y|) :
    ∃ (S : Finset ℝ) (c R : ℝ), S⊆D ∧ c∈S ∧ delta ≤ R ∧ R ≤ B ∧
      (S.image (fun x => (x-c)/R)).card=S.card ∧
      (∀ z∈S.image (fun x => (x-c)/R), |z| ≤ 1) ∧
      ScalarFrostman (S.image (fun x => (x-c)/R)) (delta/R) 2 kappa ∧
      (D.card:ℝ)*R^kappa ≤ B^kappa*S.card ∧
      delta*D.card ≤ 4*B^kappa*R^(1-kappa) := by
  obtain ⟨S,hSD,hS,hmax⟩ := exists_original_maximal_density D hD hdelta (kappa:=kappa)
  obtain ⟨c,hc⟩ := hS
  let R := radius S delta
  have hR : 0 < R := hdelta.trans_le (mesh_le_radius S delta)
  have hDB : radius D delta ≤ B := radius_le D hdB hbox
  have hRB : R ≤ B := (radius_mono hSD).trans hDB
  refine ⟨S,c,R,hSD,hc,mesh_le_radius S delta,hRB,?_,?_,?_,?_,?_⟩
  · exact Finset.card_image_of_injective S (original_normalization_injective hR)
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    rw [abs_div,abs_of_pos hR]
    apply (div_le_one hR).mpr
    exact pair_le_radius S delta hx hc
  · exact original_normalized_profile D S hdelta hkappa hkappa1 hSD hmax c
  · exact original_retained_mass D S hdelta hkappa hDB hmax
  · exact original_radius_lower D S hdelta hkappa ⟨c,hc⟩ hDB
      (fun x hx y hy hxy => hsep x (hSD hx) y (hSD hy) hxy) hmax

/-- An absolute profile at an actually available scale forces two original
points a definite distance apart. This supplies the initial diameter for
the fixed-length polynomial recurrence. -/
theorem exists_original_profile_separated_pair (A : Finset ℝ)
    {delta kappa d : ℝ} (hA : A.Nonempty) (hdelta : delta ≤ d) (hd1 : d ≤ 1)
    (hsmall : 2*d^kappa < 1) (hprofile : ScalarFrostman A delta 2 kappa) :
    ∃ x∈A, ∃ y∈A, d < |x-y| := by
  obtain ⟨x,hx⟩ := hA
  by_contra h
  push Not at h
  have hnear : ∀ y∈A, |y-x| ≤ d := by
    intro y hy
    simpa only [abs_sub_comm] using h x hx y hy
  have he : A.filter (fun y => |y-x| ≤ d)=A := Finset.filter_eq_self.mpr hnear
  have hh := hprofile x d hdelta hd1
  rw [he] at hh
  have hN : (0:ℝ) < A.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x,hx⟩)
  have hlt := mul_lt_mul_of_pos_right hsmall hN
  nlinarith only [hh,hlt]


/-- A coarse original profile gives only the cardinality exponent visible
at its actual cutoff; no estimate below that cutoff is inferred. -/
theorem original_coarse_profile_cardinality (D : Finset ℝ)
    {cutoff K u : ℝ} (hD : D.Nonempty) (hcutoff : 0 ≤ cutoff)
    (hcutoff1 : cutoff ≤ 1) (hprofile : ScalarFrostman D cutoff K u) :
    1 ≤ K*cutoff^u*D.card := by
  obtain ⟨c,hc⟩ := hD
  have hmem : c∈D.filter (fun x => |x-c| ≤ cutoff) :=
    Finset.mem_filter.mpr ⟨hc,by simpa only [sub_self,abs_zero] using hcutoff⟩
  have hcard : (1:ℝ) ≤ (D.filter (fun x => |x-c| ≤ cutoff)).card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨c,hmem⟩)
  exact hcard.trans (hprofile c cutoff le_rfl hcutoff1)

/-- The fixed absolute-profile diameter threshold depends only on the
chosen exponent, before the original data or mesh. -/
lemma absolute_diameter_threshold {kappa : ℝ} (hkappa : 0 < kappa) :
    0 < (1/4:ℝ)^(1/kappa) ∧ (1/4:ℝ)^(1/kappa) ≤ 1 ∧
      2*((1/4:ℝ)^(1/kappa))^kappa < 1 := by
  have hp : 0 < (1/4:ℝ)^(1/kappa) := Real.rpow_pos_of_pos (by norm_num) _
  have hle : (1/4:ℝ)^(1/kappa) ≤ 1 := Real.rpow_le_one (by norm_num)
    (by norm_num) (by positivity)
  have hid : (1/kappa)*kappa=1 := by field_simp
  have he : ((1/4:ℝ)^(1/kappa))^kappa=(1/4:ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤1/4),hid,Real.rpow_one]
  refine ⟨hp,hle,?_⟩
  rw [he]
  norm_num

end OriginalCoefficientNormalization
