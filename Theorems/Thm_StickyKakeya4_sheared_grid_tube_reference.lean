import Theorems.Thm_StickyKakeya4_sheared_grid_ad_reference
import Theorems.Thm_StickyKakeya4_actual_tube_footprint_profiles

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace ShearedGridTubeReference

open ShearedGridADReference SmallFiberAlignment FractionalFiberAlignment
open ActualTubeFootprintProfiles (TubeData InTube)

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A bound on genuine tubes of one common ORIGINAL source. -/
def TraceBound (E : Finset Point) (ρ τ B : ℝ) : Prop :=
  ∀ T : TubeData 1,
    (((E.filter (fun p => InTube T ρ τ p)).image (ADGridCoverMenus.gridLabel ρ)).card : ℝ) ≤ B

/-- The supplied trace upper bound is literally inherited from the concrete
maximum over all genuine footprints on the finite original source subtype. -/
lemma traceBound_of_actual_profile (E : Finset Point) (ρ τ B : ℝ)
    (hprofile : (ActualTubeFootprintProfiles.coverProfile
      (fun p : E => (p : Point)) ρ τ Finset.univ : ℝ) ≤ B) : TraceBound E ρ τ B := by
  classical
  intro T
  let pos : E → Point := fun p => p.val
  have heq : (E.filter (fun p => InTube T ρ τ p)).image (ADGridCoverMenus.gridLabel ρ) =
      (Finset.univ ∩ ActualTubeFootprintProfiles.trace pos ρ τ T).image
        (ActualTubeFootprintProfiles.grid pos ρ) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ,
      ActualTubeFootprintProfiles.mem_trace, true_and]
    constructor
    · rintro ⟨p, ⟨hp, hT⟩, heq⟩
      exact ⟨⟨p, hp⟩, hT, heq⟩
    · rintro ⟨p, hT, heq⟩
      exact ⟨p.val, ⟨p.property, hT⟩, heq⟩
  have hmax : ((Finset.univ ∩ ActualTubeFootprintProfiles.trace pos ρ τ T).image
      (ActualTubeFootprintProfiles.grid pos ρ)).card ≤
      ActualTubeFootprintProfiles.coverProfile pos ρ τ Finset.univ := by
    unfold ActualTubeFootprintProfiles.coverProfile
    exact Finset.le_sup (f := fun W : Finset E =>
      ((Finset.univ ∩ W).image (ActualTubeFootprintProfiles.grid pos ρ)).card)
      (ActualTubeFootprintProfiles.trace_mem_footprints pos ρ τ T)
  rw [heq]
  have hmaxReal : (((Finset.univ ∩ ActualTubeFootprintProfiles.trace pos ρ τ T).image
      (ActualTubeFootprintProfiles.grid pos ρ)).card : ℝ) ≤
      (ActualTubeFootprintProfiles.coverProfile pos ρ τ Finset.univ : ℝ) := by exact_mod_cast hmax
  exact hmaxReal.trans hprofile

/-- The bounded-slope graph tube uses the unchanged x parameter. -/
def graphTube (α : ℝ) (hα : |α| ≤ 1) (xmid normal : ℝ) : TubeData 1 where
  center := ![xmid, normal + α * xmid]
  direction := ![1, α]
  unit := by
    constructor
    · intro i
      fin_cases i
      · norm_num
      · exact hα
    · exact ⟨0, by norm_num⟩

lemma in_graphTube_of_bounds (α : ℝ) (hα : |α| ≤ 1) (xmid normal ρ τ : ℝ)
    (hρ : 0 ≤ ρ) (p : Point)
    (hx : |p 0 - xmid| ≤ τ / 2) (hy : |p 1 - α * p 0 - normal| ≤ ρ) :
    InTube (graphTube α hα xmid normal) ρ τ p := by
  refine ⟨p 0 - xmid, hx, ?_⟩
  intro i
  fin_cases i
  · simpa [graphTube] using hρ
  · change |p 1 - (normal + α * xmid) - (p 0 - xmid) * α| ≤ ρ
    convert hy using 1; congr 1; ring

lemma normal_error (μ α : ℝ) (hμ : 0 < μ) (hα : |α| ≤ 1) (p : Point) :
    |p 1 - α * p 0 - μ * ((vertex μ α p).2 0 : ℝ)| ≤ 2 * μ := by
  have hm := coordinate_movement μ α hμ p
  change (0 ≤ p 0 - μ * ((vertex μ α p).1 : ℝ) ∧
      p 0 - μ * ((vertex μ α p).1 : ℝ) < μ) ∧
    (0 ≤ p 1 - (μ * ((vertex μ α p).2 0 : ℝ) + α * (μ * ((vertex μ α p).1 : ℝ))) ∧
      p 1 - (μ * ((vertex μ α p).2 0 : ℝ) + α * (μ * ((vertex μ α p).1 : ℝ))) < μ) at hm
  have hx : |p 0 - μ * ((vertex μ α p).1 : ℝ)| ≤ μ := by
    rw [abs_of_nonneg hm.1.1]
    exact hm.1.2.le
  have hy : |p 1 - (μ * ((vertex μ α p).2 0 : ℝ) + α * (μ * ((vertex μ α p).1 : ℝ)))| ≤ μ := by
    rw [abs_of_nonneg hm.2.1]
    exact hm.2.2.le
  have hs : |α * (p 0 - μ * ((vertex μ α p).1 : ℝ))| ≤ μ := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hα hx (abs_nonneg _) zero_le_one
  calc
    |p 1 - α * p 0 - μ * ((vertex μ α p).2 0 : ℝ)| =
      |(p 1 - (μ * ((vertex μ α p).2 0 : ℝ) + α * (μ * ((vertex μ α p).1 : ℝ)))) -
        α * (p 0 - μ * ((vertex μ α p).1 : ℝ))| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ 2 * μ := by linarith

lemma strip_normal_error (μ α : ℝ) (hμ : 0 < μ) (hα : |α| ≤ 1)
    (R : ℕ) (y : Normal 1) (p : Point) (hp : normalClose R (vertex μ α p).2 y) :
    |p 1 - α * p 0 - μ * (y 0 : ℝ)| ≤ μ * ((R : ℝ) + 2) := by
  have hn := normal_error μ α hμ hα p
  have hindex : |((vertex μ α p).2 0 : ℝ) - (y 0 : ℝ)| ≤ (R : ℝ) := by
    exact_mod_cast hp 0
  have hi : |μ * (((vertex μ α p).2 0 : ℝ) - (y 0 : ℝ))| ≤ μ * (R : ℝ) := by
    rw [abs_mul, abs_of_pos hμ]
    exact mul_le_mul_of_nonneg_left hindex hμ.le
  calc
    |p 1 - α * p 0 - μ * (y 0 : ℝ)| =
      |(p 1 - α * p 0 - μ * ((vertex μ α p).2 0 : ℝ)) +
        μ * (((vertex μ α p).2 0 : ℝ) - (y 0 : ℝ))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ μ * ((R : ℝ) + 2) := by nlinarith

lemma parent_time_bound (x₀ b : ℝ) (p : Point)
    (hp : x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b) : |p 0 - (x₀ + b / 2)| ≤ b / 2 := by
  exact abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩

def preimage (Ω : Finset Point) (μ α : ℝ) (φ : Vertex → Prop) : Finset Point := by
  classical
  exact Ω.filter (fun p => φ (vertex μ α p))

@[simp] lemma mem_preimage (Ω : Finset Point) (μ α : ℝ) (φ : Vertex → Prop) (p : Point) :
    p ∈ preimage Ω μ α φ ↔ p ∈ Ω ∧ φ (vertex μ α p) := by
  classical
  simp [preimage]

lemma preimage_image (Ω : Finset Point) (μ α : ℝ) (φ : Vertex → Prop) [DecidablePred φ] :
    (preimage Ω μ α φ).image (vertex μ α) = (Ω.image (vertex μ α)).filter φ := by
  classical
  ext k
  simp only [preimage, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hc⟩, rfl⟩
    exact ⟨⟨p, hp, rfl⟩, hc⟩
  · rintro ⟨⟨p, hp, rfl⟩, hc⟩
    exact ⟨p, ⟨hp, hc⟩, rfl⟩

lemma grid_card_le_traceBound (E S : Finset Point) {ρ τ B : ℝ}
    (hSE : S ⊆ E) (T : TubeData 1) (hT : ∀ p ∈ S, InTube T ρ τ p)
    (hbound : TraceBound E ρ τ B) :
    ((S.image (ADGridCoverMenus.gridLabel ρ)).card : ℝ) ≤ B := by
  classical
  apply le_trans ?_ (hbound T)
  exact_mod_cast Finset.card_le_card (Finset.image_subset_image (f := ADGridCoverMenus.gridLabel ρ)
    (show S ⊆ E.filter (fun p => InTube T ρ τ p) from
      fun p hp => Finset.mem_filter.mpr ⟨hSE hp, hT p hp⟩))

/-- The FULL strip, including every occupied longitudinal coordinate, lies
in a single genuine source tube. No per-fiber cover is summed. -/
lemma strip_preimage_in_tube (Ω : Finset Point) (μ α x₀ b : ℝ)
    (hμ : 0 < μ) (hα : |α| ≤ 1) {R : ℕ} (hR : 0 < R)
    (hparent : ∀ p ∈ Ω, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b) (y : Normal 1) :
    ∀ p ∈ preimage Ω μ α (fun k => normalClose R k.2 y),
      InTube (graphTube α hα (x₀ + b / 2) (μ * (y 0 : ℝ))) (64 * μ * (R : ℝ)) b p := by
  classical
  intro p hp
  obtain ⟨hpΩ, hpy⟩ := (mem_preimage Ω μ α _ p).mp hp
  apply in_graphTube_of_bounds α hα _ _ _ _ (by positivity) p
    (parent_time_bound x₀ b p (hparent p hpΩ))
  have he := strip_normal_error μ α hμ hα R y p hpy
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  nlinarith

/-- The small-width FULL-strip estimate queries precisely (64μR,b). -/
lemma strip_card_le_query (E Ω : Finset Point) (μ α x₀ b B : ℝ)
    (hΩ : Ω ⊆ E) (hμ : 0 < μ) (hα : |α| ≤ 1) {R : ℕ} (hR : 0 < R)
    (hparent : ∀ p ∈ Ω, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b)
    (hbound : TraceBound E (64 * μ * (R : ℝ)) b B) (y : Normal 1) :
    (((strip (Ω.image (vertex μ α)) R y).image (spatialCell R)).card : ℝ) ≤
      513 ^ 2 * B := by
  classical
  let S := preimage Ω μ α (fun k => normalClose R k.2 y)
  have himage : S.image (vertex μ α) = strip (Ω.image (vertex μ α)) R y :=
    preimage_image Ω μ α _
  have hS : S ⊆ E := fun p hp => hΩ ((mem_preimage Ω μ α _ p).mp hp).1
  have hgrid := grid_card_le_traceBound E S hS _
    (strip_preimage_in_tube Ω μ α x₀ b hμ hα hR hparent y) hbound
  have hcap := coarse_menu_card_le_grid μ α hμ hα hR S
  have hcap' : ((S.image (fun p => spatialCell R (vertex μ α p))).card : ℝ) ≤
      ((S.image (ADGridCoverMenus.gridLabel (64 * μ * (R : ℝ)))).card : ℝ) * 513 ^ 2 := by
    exact_mod_cast hcap
  rw [← himage, Finset.image_image]
  change ((S.image (fun p => spatialCell R (vertex μ α p))).card : ℝ) ≤ _
  nlinarith


lemma segment_preimage_in_tube (Ω : Finset Point) (μ α x₀ b : ℝ)
    (hμ : 0 < μ) (hα : |α| ≤ 1) {R : ℕ} (hR : 0 < R)
    (hparent : ∀ p ∈ Ω, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b) (k : Vertex) :
    ∃ T : TubeData 1,
      ∀ p ∈ preimage Ω μ α (fun q => q.2 = k.2 ∧ |q.1 - k.1| ≤ (R : ℤ)),
        InTube T (64 * μ) (min (64 * μ * (R : ℝ)) b) p := by
  classical
  have hnormal (p : Point) (heq : (vertex μ α p).2 = k.2) :
      |p 1 - α * p 0 - μ * (k.2 0 : ℝ)| ≤ 64 * μ := by
    have he := normal_error μ α hμ hα p
    rw [heq] at he
    linarith
  by_cases hc : 64 * μ * (R : ℝ) ≤ b
  · refine ⟨graphTube α hα (μ * (k.1 : ℝ)) (μ * (k.2 0 : ℝ)), ?_⟩
    intro p hp
    obtain ⟨_hpΩ, heq, htime⟩ := (mem_preimage Ω μ α _ p).mp hp
    rw [min_eq_left hc]
    apply in_graphTube_of_bounds α hα _ _ _ _ (by positivity) p ?_ (hnormal p heq)
    have hm := (coordinate_movement μ α hμ p).1
    change 0 ≤ p 0 - μ * ((vertex μ α p).1 : ℝ) ∧
      p 0 - μ * ((vertex μ α p).1 : ℝ) < μ at hm
    have ht : |((vertex μ α p).1 : ℝ) - (k.1 : ℝ)| ≤ (R : ℝ) := by exact_mod_cast htime
    have ht' := abs_le.mp ht
    have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
    apply abs_le.mpr
    constructor <;> nlinarith [ht'.1, ht'.2]
  · refine ⟨graphTube α hα (x₀ + b / 2) (μ * (k.2 0 : ℝ)), ?_⟩
    intro p hp
    obtain ⟨hpΩ, heq, _htime⟩ := (mem_preimage Ω μ α _ p).mp hp
    rw [min_eq_right (le_of_not_ge hc)]
    exact in_graphTube_of_bounds α hα _ _ _ _ (by positivity) p
      (parent_time_bound x₀ b p (hparent p hpΩ)) (hnormal p heq)

/-- Narrow-column segments use query width 64μ, never μ below the stopped range. -/
lemma segment_card_le_query (E Ω : Finset Point) (μ α x₀ b B : ℝ)
    (hΩ : Ω ⊆ E) (hμ : 0 < μ) (hα : |α| ≤ 1) {R : ℕ} (hR : 0 < R)
    (hparent : ∀ p ∈ Ω, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b)
    (hbound : TraceBound E (64 * μ) (min (64 * μ * (R : ℝ)) b) B) (k : Vertex) :
    ((fiberBall (Ω.image (vertex μ α)) R k).card : ℝ) ≤ 513 ^ 2 * B := by
  classical
  let S := preimage Ω μ α (fun q => q.2 = k.2 ∧ |q.1 - k.1| ≤ (R : ℤ))
  have himage : S.image (vertex μ α) = fiberBall (Ω.image (vertex μ α)) R k :=
    preimage_image Ω μ α _
  obtain ⟨T, hT⟩ := segment_preimage_in_tube Ω μ α x₀ b hμ hα hR hparent k
  have hS : S ⊆ E := fun p hp => hΩ ((mem_preimage Ω μ α _ p).mp hp).1
  have hgrid := grid_card_le_traceBound E S hS T hT hbound
  have hcap := vertex_image_card_le_grid μ α hμ hα S
  have hcap' : ((S.image (vertex μ α)).card : ℝ) ≤
      ((S.image (ADGridCoverMenus.gridLabel (64 * μ))).card : ℝ) * 513 ^ 2 := by
    exact_mod_cast hcap
  rw [← himage]
  nlinarith

/-- Above the parent x-span, a full strip meets a fixed literal integer-cell
menu. This endpoint requires no out-of-range tube query. -/
lemma strip_card_le_constant (Ω : Finset Point) (μ α x₀ b : ℝ)
    (hμ : 0 < μ) {R : ℕ} (hR : 0 < R) (hb : b ≤ 64 * μ * (R : ℝ))
    (hparent : ∀ p ∈ Ω, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b) (y : Normal 1) :
    ((strip (Ω.image (vertex μ α)) R y).image (spatialCell R)).card ≤ 513 ^ 2 := by
  classical
  let S := preimage Ω μ α (fun k => normalClose R k.2 y)
  have himage : S.image (vertex μ α) = strip (Ω.image (vertex μ α)) R y :=
    preimage_image Ω μ α _
  rw [← himage, Finset.image_image]
  change (S.image (fun p => spatialCell R (vertex μ α p))).card ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨q, hq⟩ := hS
    rw [← coarseBox_card (spatialCell R (vertex μ α q))]
    apply Finset.card_le_card
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hpΩ, hpy⟩ := (mem_preimage Ω μ α _ p).mp hp
    obtain ⟨hqΩ, hqy⟩ := (mem_preimage Ω μ α _ q).mp hq
    have hpbox := hparent p hpΩ
    have hqbox := hparent q hqΩ
    have hpμ := (coordinate_movement μ α hμ p).1
    have hqμ := (coordinate_movement μ α hμ q).1
    change 0 ≤ p 0 - μ * ((vertex μ α p).1 : ℝ) ∧
      p 0 - μ * ((vertex μ α p).1 : ℝ) < μ at hpμ
    change 0 ≤ q 0 - μ * ((vertex μ α q).1 : ℝ) ∧
      q 0 - μ * ((vertex μ α q).1 : ℝ) < μ at hqμ
    have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have ht : |((vertex μ α p).1 : ℝ) - ((vertex μ α q).1 : ℝ)| ≤ 256 * (R : ℝ) := by
      apply abs_le.mpr
      constructor <;> nlinarith [hpbox.1, hpbox.2, hqbox.1, hqbox.2]
    have ht' := nearby_integer_divisions hR (show |(vertex μ α p).1 - (vertex μ α q).1| ≤ 256 * (R : ℤ) by exact_mod_cast ht)
    apply Finset.mem_product.mpr
    constructor
    · change (vertex μ α p).1 / (R : ℤ) ∈ Finset.Icc ((vertex μ α q).1 / (R : ℤ) - 256) ((vertex μ α q).1 / (R : ℤ) + 256)
      exact Finset.mem_Icc.mpr ⟨by have := abs_le.mp ht'; omega, by have := abs_le.mp ht'; omega⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      have hpi := abs_le.mp (hpy i)
      have hqi := abs_le.mp (hqy i)
      have hn : |(vertex μ α p).2 i - (vertex μ α q).2 i| ≤ 256 * (R : ℤ) := by
        apply abs_le.mpr
        constructor <;> omega
      have hn' := nearby_integer_divisions hR hn
      change (vertex μ α p).2 i / (R : ℤ) ∈ Finset.Icc ((vertex μ α q).2 i / (R : ℤ) - 256) ((vertex μ α q).2 i / (R : ℤ) + 256)
      exact Finset.mem_Icc.mpr ⟨by have := abs_le.mp hn'; omega, by have := abs_le.mp hn'; omega⟩
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hz]


/-- Exact admission of both query pairs to the original stopped scale range.
Actual dyadic membership of these real scales remains an explicit caller check. -/
lemma profile_query_eligibility (μ ρ₀ τ₀ b : ℝ) {R : ℕ} (hR : 0 < R)
    (hμ : 0 < μ) (hρ : ρ₀ ≤ 64 * μ) (hab : 64 * μ ≤ b) (hb : b ≤ τ₀) :
    (64 * μ * (R : ℝ) ≤ b →
      ρ₀ ≤ 64 * μ * (R : ℝ) ∧ 64 * μ * (R : ℝ) ≤ b ∧ b ≤ τ₀) ∧
    (ρ₀ ≤ 64 * μ ∧ 64 * μ ≤ min (64 * μ * (R : ℝ)) b ∧
      min (64 * μ * (R : ℝ)) b ≤ τ₀) := by
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have haR : 64 * μ ≤ 64 * μ * (R : ℝ) := by nlinarith
  exact ⟨fun h => ⟨hρ.trans haR, h, hb⟩,
    hρ, le_min haR hab, (min_le_right _ _).trans hb⟩

/-- Full-strip hstrip with the honest raw-grid scale N=b/μ. Only the small
width case queries the common original profile. -/
theorem strip_card_le_power (E Ω : Finset Point) (μ α x₀ b H s : ℝ)
    (hΩ : Ω ⊆ E) (hμ : 0 < μ) (hα : |α| ≤ 1) {R : ℕ} (hR : 0 < R)
    (hRb : μ * (R : ℝ) ≤ b) (hH : 1 ≤ H) (hs : 0 ≤ s)
    (hparent : ∀ p ∈ Ω, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b)
    (hquery : 64 * μ * (R : ℝ) ≤ b →
      TraceBound E (64 * μ * (R : ℝ)) b (H * (b / (64 * μ * (R : ℝ))) ^ s))
    (y : Normal 1) :
    (((strip (Ω.image (vertex μ α)) R y).image (spatialCell R)).card : ℝ) ≤
      (513 ^ 2 * H) * (b / (μ * (R : ℝ))) ^ s := by
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hb : 0 < b := lt_of_lt_of_le (mul_pos hμ hRreal) hRb
  by_cases hc : 64 * μ * (R : ℝ) ≤ b
  · have hraw := strip_card_le_query E Ω μ α x₀ b _ hΩ hμ hα hR hparent (hquery hc) y
    have hratio : b / (64 * μ * (R : ℝ)) ≤ b / (μ * (R : ℝ)) := by
      apply div_le_div_of_nonneg_left hb.le (by positivity)
      nlinarith
    have hpower := Real.rpow_le_rpow (by positivity : 0 ≤ b / (64 * μ * (R : ℝ))) hratio hs
    have hHnonneg : 0 ≤ H := le_trans zero_le_one hH
    nlinarith
  · have hraw : (((strip (Ω.image (vertex μ α)) R y).image (spatialCell R)).card : ℝ) ≤ 513 ^ 2 := by
      exact_mod_cast strip_card_le_constant Ω μ α x₀ b hμ hR (le_of_not_ge hc) hparent y
    have hone : (1 : ℝ) ≤ b / (μ * (R : ℝ)) := (le_div_iff₀ (by positivity)).mpr (by simpa using hRb)
    have hpower : (1 : ℝ) ≤ (b / (μ * (R : ℝ))) ^ s := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hone hs
    nlinarith

/-- The narrow segment hsegment queries (64μ,min(64μR,b)) of the SAME source. -/
theorem segment_card_le_power (E Ω : Finset Point) (μ α x₀ b H s : ℝ)
    (hΩ : Ω ⊆ E) (hμ : 0 < μ) (hα : |α| ≤ 1) {R : ℕ} (hR : 0 < R)
    (hb : 0 ≤ b) (hH : 0 ≤ H) (hs : 0 ≤ s)
    (hparent : ∀ p ∈ Ω, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b)
    (hquery : TraceBound E (64 * μ) (min (64 * μ * (R : ℝ)) b)
      (H * (min (64 * μ * (R : ℝ)) b / (64 * μ)) ^ s)) (k : Vertex) :
    ((fiberBall (Ω.image (vertex μ α)) R k).card : ℝ) ≤ (513 ^ 2 * H) * (R : ℝ) ^ s := by
  have hraw := segment_card_le_query E Ω μ α x₀ b _ hΩ hμ hα hR hparent hquery k
  have hratio : min (64 * μ * (R : ℝ)) b / (64 * μ) ≤ (R : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [min_le_left (64 * μ * (R : ℝ)) b]
  have hnonneg : 0 ≤ min (64 * μ * (R : ℝ)) b / (64 * μ) := by positivity
  have hpower := Real.rpow_le_rpow hnonneg hratio hs
  nlinarith

lemma timeBins_card_le_strip_cells (P : Finset Vertex) (R : ℕ) (y : Normal 1) :
    (timeBins P R y).card ≤ ((strip P R y).image (spatialCell R)).card := by
  classical
  have hsub : timeBins P R y ⊆ ((strip P R y).image (spatialCell R)).image Prod.fst := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hkP, hky⟩ := Finset.mem_filter.mp hk
    apply Finset.mem_image.mpr
    refine ⟨spatialCell R k, Finset.mem_image_of_mem _ ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨hkP, ?_⟩
    intro i
    simp [hky]
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

/-- hbins is a projection of the one common full-strip cover. -/
theorem timeBins_card_le_power (E Ω : Finset Point) (μ α x₀ b H s : ℝ)
    (hΩ : Ω ⊆ E) (hμ : 0 < μ) (hα : |α| ≤ 1) {R : ℕ} (hR : 0 < R)
    (hRb : μ * (R : ℝ) ≤ b) (hH : 1 ≤ H) (hs : 0 ≤ s)
    (hparent : ∀ p ∈ Ω, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b)
    (hquery : 64 * μ * (R : ℝ) ≤ b →
      TraceBound E (64 * μ * (R : ℝ)) b (H * (b / (64 * μ * (R : ℝ))) ^ s))
    (y : Normal 1) :
    ((timeBins (Ω.image (vertex μ α)) R y).card : ℝ) ≤
      (513 ^ 2 * H) * (b / (μ * (R : ℝ))) ^ s := by
  have hle : ((timeBins (Ω.image (vertex μ α)) R y).card : ℝ) ≤
      (((strip (Ω.image (vertex μ α)) R y).image (spatialCell R)).card : ℝ) := by
    exact_mod_cast timeBins_card_le_strip_cells (Ω.image (vertex μ α)) R y
  exact hle.trans (strip_card_le_power E Ω μ α x₀ b H s hΩ hμ hα hR hRb hH hs hparent hquery y)

/-- Exactly the three profile-derived fractional-alignment premises, for one
actual original subset, one quantizer, and one common genuine tube profile.
The two hypotheses below are the ONLY requested profile query pairs; a dyadic
caller must establish their membership rather than infer real-scale bounds. -/
theorem three_profile_reference_bounds (E Ω : Finset Point) (μ α x₀ b H s : ℝ)
    (N R : ℕ) (hΩ : Ω ⊆ E) (hμ : 0 < μ) (hα : |α| ≤ 1)
    (hR : 0 < R) (hRN : R ≤ N) (hNscale : μ * (N : ℝ) = b)
    (hH : 1 ≤ H) (hs : 0 ≤ s)
    (hparent : ∀ p ∈ Ω, x₀ ≤ p 0 ∧ p 0 ≤ x₀ + b)
    (hwide : 64 * μ * (R : ℝ) ≤ b →
      TraceBound E (64 * μ * (R : ℝ)) b (H * (b / (64 * μ * (R : ℝ))) ^ s))
    (hshort : TraceBound E (64 * μ) (min (64 * μ * (R : ℝ)) b)
      (H * (min (64 * μ * (R : ℝ)) b / (64 * μ)) ^ s)) :
    (∀ y, ((timeBins (Ω.image (vertex μ α)) R y).card : ℝ) ≤
      (513 ^ 2 * H) * ((N : ℝ) / (R : ℝ)) ^ s) ∧
    (∀ k, ((fiberBall (Ω.image (vertex μ α)) R k).card : ℝ) ≤
      (513 ^ 2 * H) * (R : ℝ) ^ s) ∧
    (∀ y, (((strip (Ω.image (vertex μ α)) R y).image (spatialCell R)).card : ℝ) ≤
      (513 ^ 2 * H) * ((N : ℝ) / (R : ℝ)) ^ s) := by
  have hRb : μ * (R : ℝ) ≤ b := by
    rw [← hNscale]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hRN) hμ.le
  have hb : 0 ≤ b := (mul_nonneg hμ.le (Nat.cast_nonneg R)).trans hRb
  have hratio : b / (μ * (R : ℝ)) = (N : ℝ) / (R : ℝ) := by
    rw [← hNscale]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · intro y
    simpa only [hratio] using timeBins_card_le_power E Ω μ α x₀ b H s hΩ hμ hα hR hRb hH hs hparent hwide y
  · exact segment_card_le_power E Ω μ α x₀ b H s hΩ hμ hα hR hb (zero_le_one.trans hH) hs hparent hshort
  · intro y
    simpa only [hratio] using strip_card_le_power E Ω μ α x₀ b H s hΩ hμ hα hR hRb hH hs hparent hwide y

end
end ShearedGridTubeReference
