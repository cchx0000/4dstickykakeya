import Theorems.Thm_StickyKakeya4_original_w_core_dynamics
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace OriginalScalarCollisionMass
open scoped BigOperators
open Classical OriginalWWitnessCounts OriginalWCoarseEscapeMenus TwoTubePathCollisionCount
/-- Actual scalar terminal label. No full-direction coincidence is asserted. -/
def scalarTerminalCell {T : Type*} (q : ℝ) (u : T → ℝ) (t : T) : ℤ := ⌊u t/q⌋
/-- Cover the literal scalar terminal-cell image using the common ORIGINAL
 Phi alphabet and the actual direction realization error. -/
theorem scalar_terminal_image_bound {T : Type*} (T0 : Finset T) (u : T → ℝ) (Phi : Finset ℝ)
    {q error : ℝ} (hq : 0 < q) (he : 0 ≤ error)
    (hcover : ∀ t ∈ T0, ∃ a ∈ Phi, |u t-a| ≤ error) :
    ((T0.image (scalarTerminalCell q u)).card:ℝ) ≤ (2*error/q+2)*(Phi.card:ℝ) := by
  let cells := fun a => (T0.filter (fun t => |u t-a| ≤ error)).image (scalarTerminalCell q u)
  have hsub : T0.image (scalarTerminalCell q u) ⊆ Phi.biUnion cells := by
    intro c hc
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨a,ha,hta⟩ := hcover t ht
    exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨ht,hta⟩)⟩
  have hcap : ∀ a ∈ Phi, ((cells a).card:ℝ) ≤ 2*error/q+2 := by
    intro a _ha
    apply NativeTangentGridCoarsening.scalar_interval_grid_card _ u (c := a-error) hq (show 0 ≤ 2*error by positivity)
    intro t ht
    have hh := abs_le.mp (Finset.mem_filter.mp ht).2
    exact ⟨by linarith only [hh.1],by linarith only [hh.2]⟩
  have hu := card_biUnion_le_real Phi cells (show 0 ≤ 2*error/q+2 by positivity) (le_refl _) hcap
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (by simpa only [mul_comm] using hu)
variable {P T H K : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq H] [DecidableEq K]
/-- The native graph vertices are exactly actual original height/tube
 incidences, including those represented by a repeated-point path. -/
theorem vertices_eq_original_incidence_image (I : Finset (P × T)) (height : P → H) :
    vertices I height=I.image (fun e => (height e.1,e.2)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image_of_mem _ ((mem_paths I a).mp ha).2.2.2
  · intro hv
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
    let a : TwoTubePathCollisionCount.Path P T := ⟨e.1,e.2,e.1,e.2,e.1⟩
    exact Finset.mem_image.mpr ⟨a,(mem_paths I a).mpr ⟨he,he,he,he⟩,rfl⟩
/-- The collision-label image is counted from the actual original point,
 height and terminal-cell images, not from a supplied collision certificate. -/
theorem original_collision_label_card (I : Finset (P × T)) (height : P → H) (cell : T → K) (Z : Finset H)
    (hheight : ∀ p ∈ points I, height p ∈ Z) :
    (((paths I).image (collisionLabel height cell)).card) ≤
      (points I).card*Z.card^2*((tubes I).image cell).card := by
  have hsub : (paths I).image (collisionLabel height cell) ⊆
      points I ×ˢ (Z ×ˢ (Z ×ˢ ((tubes I).image cell))) := by
    intro l hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    have hh := (mem_paths I a).mp ha
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst hh.1,
      Finset.mem_product.mpr ⟨hheight _ (Finset.mem_image_of_mem Prod.fst hh.2.1),
        Finset.mem_product.mpr ⟨hheight _ (Finset.mem_image_of_mem Prod.fst hh.2.2.2),
          Finset.mem_image_of_mem _ (Finset.mem_image_of_mem Prod.snd hh.2.2.2)⟩⟩⟩
  have hh := Finset.card_le_card hsub
  simp only [Finset.card_product] at hh
  convert hh using 1; ring
/-- The genuine original path collision count follows directly from the
 original incidence set. Scalar or full-direction labels can be used, but
 no relation between these different collision sets is asserted. -/
theorem original_eighth_power_count (I : Finset (P × T)) (height : P → H) (cell : T → K) (Z : Finset H)
    (hheight : ∀ p ∈ points I, height p ∈ Z) :
    (I.card:ℝ)^8 ≤ (points I).card^3*(tubes I).card^4*(Z.card:ℝ)^2*
      (((tubes I).image cell).card:ℝ)*(witnesses I height cell).card := by
  have hI : I ⊆ (points I).product (tubes I) := by
    intro e he
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst he,Finset.mem_image_of_mem Prod.snd he⟩
  exact_mod_cast eighth_power_collision_bound I (points I) (tubes I) Z (((tubes I).image cell).card)
    (collisionLabel height cell) hI (original_collision_label_card I height cell Z hheight)
/-- Eliminate the original W-mass premise using only original incidence
 populations and the actual terminal-cell image. The factor lambda is the
 original average tube-height incidence density from the source count. -/
theorem original_incidence_population_collision_mass
    (I : Finset (P × T)) (height : P → H) (cell : T → K) (Z : Finset H)
    (hI : I.Nonempty) (hheight : ∀ p ∈ points I, height p ∈ Z)
    {D lambda : ℝ} (hD : 0 ≤ D) (hlambda : 0 ≤ lambda)
    (hdegree : D*(points I).card ≤ (I.card:ℝ))
    (hheightMass : lambda*(Z.card:ℝ)*(tubes I).card ≤ (vertices I height).card) :
    D^3*lambda^4*(Z.card:ℝ)^2*(vertices I height).card ≤
      (((tubes I).image cell).card:ℝ)*(witnesses I height cell).card := by
  have hP : (0:ℝ)<(points I).card := Nat.cast_pos.mpr ((hI.image _).card_pos)
  have hT : (0:ℝ)<(tubes I).card := Nat.cast_pos.mpr ((hI.image _).card_pos)
  obtain ⟨e,he⟩ := hI
  have hZ : (0:ℝ)<Z.card := Nat.cast_pos.mpr (Finset.card_pos.mpr
    ⟨height e.1,hheight _ (Finset.mem_image_of_mem Prod.fst he)⟩)
  have hV : ((vertices I height).card:ℝ) ≤ (I.card:ℝ) := by
    rw [vertices_eq_original_incidence_image]
    exact Nat.cast_le.mpr Finset.card_image_le
  have hTube : lambda*(Z.card:ℝ)*(tubes I).card ≤ (I.card:ℝ) := hheightMass.trans hV
  have hd3 := pow_le_pow_left₀ (show 0 ≤ D*(points I).card by positivity) hdegree 3
  have ht4 := pow_le_pow_left₀ (show 0 ≤ lambda*(Z.card:ℝ)*(tubes I).card by positivity) hTube 4
  have hcombined : (D*(points I).card)^3*(lambda*(Z.card:ℝ)*(tubes I).card)^4*(vertices I height).card ≤ (I.card:ℝ)^8 := by
    calc
      _ ≤ (I.card:ℝ)^3*(I.card:ℝ)^4*(I.card:ℝ) := by gcongr
      _ = _ := by ring
  have hraw := hcombined.trans (original_eighth_power_count I height cell Z hheight)
  apply (mul_le_mul_iff_left₀ (show (0:ℝ)<(points I).card^3*(tubes I).card^4*(Z.card:ℝ)^2 by positivity)).mp
  convert hraw using 1 <;> ring
/-- A concrete original collision coefficient; its denominator consists
 only of original point/tube multiplicity and source angular populations. -/
def collisionAlpha (lambda C imageLoss D U N : ℝ) : ℝ :=
  lambda^4/(C^5*imageLoss*(U*N/D))
/-- Original incidence degree, original average height incidence, and the
 common source angle cover PRODUCE the scalar-collision W mass used by the
 core constructor. No W-count or graph-density certificate is a premise. -/
theorem scalar_original_collision_mass
    (I : Finset (P × T)) (height : P → H) (u : T → ℝ) (Z : Finset H) (Phi : Finset ℝ)
    (hI : I.Nonempty) (hPhi : Phi.Nonempty)
    {q error C D U lambda : ℝ} (hq : 0 < q) (he : 0 ≤ error)
    (hC : 0 < C) (hD : 0 < D) (hU : 0 < U) (hlambda : 0 ≤ lambda)
    (hheight : ∀ p ∈ points I, height p ∈ Z)
    (hdegree : D*(points I).card ≤ (I.card:ℝ))
    (hheightMass : lambda*(Z.card:ℝ)*(tubes I).card ≤ (vertices I height).card)
    (hcover : ∀ t ∈ tubes I, ∃ a ∈ Phi, |u t-a| ≤ error) :
    collisionAlpha lambda C (2*error/q+2) D U Phi.card *
      (C^5*D^2*U*(Z.card:ℝ)^2)*(vertices I height).card ≤
      ((witnesses I height (scalarTerminalCell q u)).card:ℝ) := by
  let W := (witnesses I height (scalarTerminalCell q u)).card
  let H0 := 2*error/q+2
  have hH : 0 < H0 := by dsimp [H0]; positivity
  have hN : (0:ℝ)<Phi.card := Nat.cast_pos.mpr hPhi.card_pos
  have hmass := original_incidence_population_collision_mass I height (scalarTerminalCell q u) Z
    hI hheight hD.le hlambda hdegree hheightMass
  have hlabels := scalar_terminal_image_bound (tubes I) u Phi hq he hcover
  have hh : D^3*lambda^4*(Z.card:ℝ)^2*(vertices I height).card ≤ H0*(Phi.card:ℝ)*(W:ℝ) :=
    hmass.trans (mul_le_mul_of_nonneg_right hlabels (Nat.cast_nonneg W))
  have hid : collisionAlpha lambda C H0 D U Phi.card *
      (C^5*D^2*U*(Z.card:ℝ)^2)*(vertices I height).card =
      (D^3*lambda^4*(Z.card:ℝ)^2*(vertices I height).card)/(H0*(Phi.card:ℝ)) := by
    unfold collisionAlpha
    field_simp
  rw [hid]
  exact (div_le_iff₀ (mul_pos hH hN)).mpr (by simpa only [mul_comm] using hh)
/-- Actual point degrees count the same original incidence fibers. -/
lemma original_point_degree_fiber_card (I : Finset (P × T)) (p : P) :
    (tubesAt I p).card=(I.filter (fun e => e.1=p)).card := by
  apply Finset.card_bij (fun t _ht => (p,t))
  · intro t ht
    exact Finset.mem_filter.mpr ⟨(mem_tubesAt I p t).mp ht,rfl⟩
  · intro s _hs t _ht he
    exact congrArg Prod.snd he
  · intro e he
    obtain ⟨heI,heP⟩ := Finset.mem_filter.mp he
    refine ⟨e.2,(mem_tubesAt I p e.2).mpr ?_,Prod.ext heP.symm rfl⟩
    simpa only [← heP] using heI
/-- The pointwise degree produced by the original fine-angle realization
 supplies the total incidence degree required by the collision count. -/
theorem original_point_degrees_total (I : Finset (P × T)) {D : ℝ}
    (hdegree : ∀ p ∈ points I, D ≤ ((tubesAt I p).card:ℝ)) :
    D*(points I).card ≤ (I.card:ℝ) := by
  have hsum : (I.card:ℝ)=∑ p ∈ points I, ((tubesAt I p).card:ℝ) := by
    rw [Finset.card_eq_sum_card_image Prod.fst I,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [original_point_degree_fiber_card]
  calc
    _ = ∑ _p ∈ points I, D := by simp [mul_comm]
    _ ≤ ∑ p ∈ points I, ((tubesAt I p).card:ℝ) := Finset.sum_le_sum (fun p hp => hdegree p hp)
    _ = _ := hsum.symm
end OriginalScalarCollisionMass
