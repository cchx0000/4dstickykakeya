import Theorems.Thm_StickyKakeya4_native_original_macro_tube_count
import Theorems.Thm_StickyKakeya4_original_literal_angular_incidences
import Theorems.Thm_StickyKakeya4_original_height_vertex_density
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace OriginalMacroHeightIncidenceDensity
open Classical Finset TwoTubePathCollisionCount OriginalWWitnessCounts OriginalWCoarseEscapeMenus
variable {P T : Type*} [DecidableEq P] [DecidableEq T]
/-- The actual fine-angle degree supplier has its exact delta power removed;
 its coefficient is the original AD and angular-realization fiber loss. -/
theorem original_degree_power_mass (I : Finset (P × T)) {delta K kappa C : ℝ}
    (hd : 0 < delta)
    (hdegree : ∀ p ∈ points I, OriginalAngularSourcePopulation.degree delta K kappa C ≤
      ((tubesAt I p).card:ℝ)) :
    (1/(K*(2*C+2)))*(points I).card ≤ delta^kappa*(I.card:ℝ) := by
  have hh := mul_le_mul_of_nonneg_left
    (OriginalScalarCollisionMass.original_point_degrees_total I hdegree)
    (Real.rpow_pos_of_pos hd kappa).le
  have hcancel : delta^kappa*(1/delta)^kappa=1 := by
    rw [←Real.mul_rpow hd.le (one_div_nonneg.mpr hd.le)]
    simp [hd.ne']
  have he : delta^kappa*(OriginalAngularSourcePopulation.degree delta K kappa C*(points I).card)=
      (1/(K*(2*C+2)))*(points I).card := by
    unfold OriginalAngularSourcePopulation.degree
    calc
      _ = (delta^kappa*(1/delta)^kappa)*(1/(K*(2*C+2)))*(points I).card := by ring
      _ = _ := by rw [hcancel,one_mul]
  rwa [he] at hh
/-- The actual macro point/height count, actual angular degree, and actual
 native tube population imply Eq146 average height/tube density. The final
 density is proved here, rather than supplied as an input certificate. The
 original point/tube/height occupancy is consumed on the SAME incidence set. -/
theorem original_height_density_from_source_counts (I : Finset (P × T))
    (height : P → ℝ) (Z : Finset ℝ) {delta q kappa CP CT Cocc c : ℝ}
    (hd : 0 < delta) (hq : 0 < q) (hCP : 0 < CP) (hCT : 0 < CT)
    (hCocc : 0 < Cocc) (hc : 0 ≤ c)
    (hpoint : q^(3-kappa)*(Z.card:ℝ) ≤ CP*delta^(3-kappa)*(points I).card)
    (hdegree : c*(points I).card ≤ delta^kappa*(I.card:ℝ))
    (htubes : q^kappa*(tubes I).card ≤ CT*(q/delta)^3)
    (hocc : ∀ t z, ((pointsAt I height t z).card:ℝ) ≤ Cocc) :
    (c/(CP*CT*Cocc))*(Z.card:ℝ)*(tubes I).card ≤ (vertices I height).card := by
  have hdCancel : delta^(3-kappa)*delta^kappa=delta^3 := by
    rw [←Real.rpow_add hd,show (3-kappa)+kappa=(3:ℝ) by ring]
    norm_num
  have hqCancel : q^kappa*q^(3-kappa)=q^3 := by
    rw [←Real.rpow_add hq,show kappa+(3-kappa)=(3:ℝ) by ring]
    norm_num
  have hscale : (q/delta)^3*delta^3=q^3 := by field_simp
  have hpd : c*q^(3-kappa)*(Z.card:ℝ) ≤ CP*delta^3*(I.card:ℝ) := by
    calc
      _ = c*(q^(3-kappa)*(Z.card:ℝ)) := by ring
      _ ≤ c*(CP*delta^(3-kappa)*(points I).card) := mul_le_mul_of_nonneg_left hpoint hc
      _ = (CP*delta^(3-kappa))*(c*(points I).card) := by ring
      _ ≤ (CP*delta^(3-kappa))*(delta^kappa*(I.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hdegree (by positivity)
      _ = CP*(delta^(3-kappa)*delta^kappa)*(I.card:ℝ) := by ring
      _ = _ := by rw [hdCancel]
  have htr : delta^3*(tubes I).card ≤ CT*q^(3-kappa) := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hq kappa)).mp
    calc
      _ = (q^kappa*(tubes I).card)*delta^3 := by ring
      _ ≤ (CT*(q/delta)^3)*delta^3 := mul_le_mul_of_nonneg_right htubes (by positivity)
      _ = CT*((q/delta)^3*delta^3) := by ring
      _ = CT*q^3 := by rw [hscale]
      _ = q^kappa*(CT*q^(3-kappa)) := by rw [←hqCancel]; ring
  have hmass : c*(Z.card:ℝ)*(tubes I).card ≤ CP*CT*(I.card:ℝ) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hd 3)).mp
    calc
      _ = (c*(Z.card:ℝ))*(delta^3*(tubes I).card) := by ring
      _ ≤ (c*(Z.card:ℝ))*(CT*q^(3-kappa)) := mul_le_mul_of_nonneg_left htr (by positivity)
      _ = CT*(c*q^(3-kappa)*(Z.card:ℝ)) := by ring
      _ ≤ CT*(CP*delta^3*(I.card:ℝ)) := mul_le_mul_of_nonneg_left hpd hCT.le
      _ = _ := by ring
  have hcap := OriginalHeightVertexDensity.incidences_le_height_vertices I height hCocc.le hocc
  have hv : c*(Z.card:ℝ)*(tubes I).card ≤ (CP*CT*Cocc)*(vertices I height).card :=
    hmass.trans ((mul_le_mul_of_nonneg_left hcap (mul_pos hCP hCT).le).trans_eq (by ring))
  calc
    _ = (c*(Z.card:ℝ)*(tubes I).card)/(CP*CT*Cocc) := by ring
    _ ≤ (vertices I height).card :=
      (div_le_iff₀ (mul_pos (mul_pos hCP hCT) hCocc)).mpr (by simpa only [mul_comm] using hv)
end OriginalMacroHeightIncidenceDensity
