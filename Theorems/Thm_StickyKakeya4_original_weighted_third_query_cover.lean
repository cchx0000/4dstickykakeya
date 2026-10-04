import Theorems.Thm_StickyKakeya4_original_normalized_fractional_coefficient_profile
import Theorems.Thm_StickyKakeya4_original_two_projection_real_graph
import Theorems.Thm_StickyKakeya4_gkz_grid_code_perturbation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section
namespace OriginalWeightedThirdQueryCover
open Classical OriginalFractionalLinearCoefficientProfile OriginalNormalizedFractionalCoefficientProfile
open OriginalTwoProjectionCartesian OriginalTwoProjectionRealGraph ActualRoundedAdditiveEnergy
open GKZGridCodePerturbation

def weightedPoint (a b c0 : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (leftWeight a b c0*z.1,rightWeight a b c0*z.2)

/-- Two original transverse coordinates are normalized at one ACTUAL
third direction. Every later coefficient is still the original ratio of
that direction, and every edge keeps its original point label. -/
theorem original_weighted_query_identity (a b c0 c : ℝ) (z : ℝ × ℝ)
    (hab : b-a≠0) (hbc : b-c≠0) (hb0 : b-c0≠0) (h0a : c0-a≠0) :
    (weightedPoint a b c0 z).1+normalizedCoefficient a b c0 c*(weightedPoint a b c0 z).2=
      ((b-c0)/(b-c))*linearValue a b c z := by
  dsimp [weightedPoint,normalizedCoefficient,coefficient,linearValue,leftWeight,rightWeight]
  field_simp

lemma original_weighted_query_dilation (b c0 c h : ℝ) (hh : 0 < h)
    (hb : |b| ≤ 1) (hc0 : |c0| ≤ 1) (hbc : h ≤ |b-c|) :
    |(b-c0)/(b-c)| ≤ 2/h := by
  rw [abs_div]
  apply (div_le_div_iff₀ (hh.trans_le hbc) hh).mpr
  have hn : |b-c0| ≤ 2 := (abs_sub b c0).trans (by linarith only [hb,hc0])
  have hm := mul_le_mul_of_nonneg_right hn hh.le
  nlinarith only [hm,hbc]

/-- Exact scaling of literal floor codes, with both mesh sizes visible. -/
lemma original_changed_mesh_floor (delta sigma k x : ℝ) (hd : 0 < delta) (hs : 0 < sigma) :
    rounded sigma (k*x)=rounded delta ((delta/sigma*k)*x) := by
  unfold rounded
  congr 1
  field_simp

/-- Changing the scalar normalization and the mesh preserves ORIGINAL
query labels. At sigma=h*delta/64 the true cover loss is64/h^2+2. -/
theorem original_exact_weighted_query_cover (G : Finset (ℝ × ℝ))
    (a b c0 c h delta : ℝ) (hh : 0 < h) (hd : 0 < delta)
    (hab : b-a≠0) (hb0 : b-c0≠0) (h0a : c0-a≠0)
    (hb : |b| ≤ 1) (hc0 : |c0| ≤ 1) (hbc : h ≤ |b-c|) :
    ((G.image (fun z => rounded (h*delta/64)
      ((weightedPoint a b c0 z).1+normalizedCoefficient a b c0 c*(weightedPoint a b c0 z).2))).card : ℝ) ≤
      (64/h^2+2)*(G.image (fun z => rounded (delta/4) (linearValue a b c z))).card := by
  have hcne : b-c≠0 := abs_pos.mp (hh.trans_le hbc)
  let k := (b-c0)/(b-c)
  let factor := ((delta/4)/(h*delta/64))*k
  have hk := original_weighted_query_dilation b c0 c h hh hb hc0 hbc
  have hscale : (delta/4)/(h*delta/64)=16/h := by field_simp; ring
  have hf : |factor| ≤ 32/h^2 := by
    dsimp only [factor]
    rw [hscale,abs_mul,abs_of_pos (by positivity : 0 < (16:ℝ)/h)]
    calc
      (16/h)*|k| ≤ (16/h)*(2/h) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = 32/h^2 := by ring
  have him : G.image (fun z => rounded (h*delta/64)
      ((weightedPoint a b c0 z).1+normalizedCoefficient a b c0 c*(weightedPoint a b c0 z).2))=
      G.image (fun z => rounded (delta/4) (factor*linearValue a b c z)) := by
    apply Finset.image_congr
    intro z _hz
    dsimp only
    rw [original_weighted_query_identity a b c0 c z hab hcne hb0 h0a]
    exact original_changed_mesh_floor (delta/4) (h*delta/64) k (linearValue a b c z) (by positivity) (by positivity)
  rw [him]
  have hc := bounded_dilation_floor_image G (linearValue a b c)
    (delta:=delta/4) (a:=factor) (L:=32/h^2) (by positivity) (by positivity) hf
  convert hc using 1
  ring

end OriginalWeightedThirdQueryCover
