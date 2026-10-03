import Theorems.Thm_StickyKakeya4_ad_grid_cover_menus
import Theorems.Thm_StickyKakeya4_separated_alignment_patches
import Theorems.Thm_StickyKakeya4_fractional_fiber_alignment

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace ShearedGridADReference

open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open SmallFiberAlignment
open scoped BigOperators

noncomputable section

abbrev Point := Fin 2 → ℝ
abbrev Vertex := Grid 1

/-- The exact frozen two-stage quantizer: round x, then the normal coordinate. -/
def vertex (μ α : ℝ) (p : Point) : Vertex :=
  SeparatedAlignmentPatches.quantizedIndex μ (fun _ : Fin 1 => α) (p 0, fun _ => p 1)

def realized (μ α : ℝ) (k : Vertex) : Point :=
  ![μ * (k.1 : ℝ), μ * (k.2 0 : ℝ) + α * (μ * (k.1 : ℝ))]

lemma coordinate_movement (μ α : ℝ) (hμ : 0 < μ) (p : Point) :
    (0 ≤ p 0 - realized μ α (vertex μ α p) 0 ∧ p 0 - realized μ α (vertex μ α p) 0 < μ) ∧
    (0 ≤ p 1 - realized μ α (vertex μ α p) 1 ∧ p 1 - realized μ α (vertex μ α p) 1 < μ) := by
  have h := SeparatedAlignmentPatches.quantization_coordinate_movement μ hμ (fun _ : Fin 1 => α)
    (p 0, fun _ => p 1)
  exact ⟨h.1, h.2 0⟩

lemma quantization_dist_lt (μ α : ℝ) (hμ : 0 < μ) (p : Point) :
    dist p (realized μ α (vertex μ α p)) < μ := by
  have h := coordinate_movement μ α hμ p
  apply (dist_pi_lt_iff hμ).mpr
  intro i
  fin_cases i
  · change |p 0 - realized μ α (vertex μ α p) 0| < μ
    rw [abs_of_nonneg h.1.1]
    exact h.1.2
  · change |p 1 - realized μ α (vertex μ α p) 1| < μ
    rw [abs_of_nonneg h.2.1]
    exact h.2.2

lemma realized_coordinate_bounds (μ α : ℝ) (hμ : 0 < μ) (hα : |α| ≤ 1)
    (k l : Vertex) (L : ℝ) (hd : dist (realized μ α k) (realized μ α l) ≤ L) :
    μ * (|k.1 - l.1| : ℤ) ≤ L ∧ μ * (|k.2 0 - l.2 0| : ℤ) ≤ 2 * L := by
  have h0 : |μ * (k.1 : ℝ) - μ * (l.1 : ℝ)| ≤ L := by
    simpa [realized, Real.dist_eq] using
      (dist_le_pi_dist (realized μ α k) (realized μ α l) 0).trans hd
  have h1 : |(μ * (k.2 0 : ℝ) + α * (μ * (k.1 : ℝ))) -
      (μ * (l.2 0 : ℝ) + α * (μ * (l.1 : ℝ)))| ≤ L := by
    simpa [realized, Real.dist_eq] using
      (dist_le_pi_dist (realized μ α k) (realized μ α l) 1).trans hd
  have hL : 0 ≤ L := dist_nonneg.trans hd
  have hshift : |α * (μ * (k.1 : ℝ) - μ * (l.1 : ℝ))| ≤ L := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hα h0 (abs_nonneg _) zero_le_one
  have hnormal : |μ * ((k.2 0 : ℝ) - (l.2 0 : ℝ))| ≤ 2 * L := by
    have hid : μ * ((k.2 0 : ℝ) - (l.2 0 : ℝ)) =
        ((μ * (k.2 0 : ℝ) + α * (μ * (k.1 : ℝ))) -
          (μ * (l.2 0 : ℝ) + α * (μ * (l.1 : ℝ)))) -
        α * (μ * (k.1 : ℝ) - μ * (l.1 : ℝ)) := by ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith)
  constructor
  · simpa only [← mul_sub, abs_mul, abs_of_pos hμ, ← Int.cast_sub, ← Int.cast_abs] using h0
  · simpa only [abs_mul, abs_of_pos hμ, ← Int.cast_sub, ← Int.cast_abs] using hnormal

lemma realized_dist_le (μ α : ℝ) (hμ : 0 < μ) (hα : |α| ≤ 1)
    (k l : Vertex) {R : ℕ}
    (hk : |k.1 - l.1| ≤ (R : ℤ) ∧ normalClose R k.2 l.2) :
    dist (realized μ α k) (realized μ α l) ≤ 2 * μ * (R : ℝ) := by
  have htime : |(k.1 : ℝ) - (l.1 : ℝ)| ≤ (R : ℝ) := by exact_mod_cast hk.1
  have hnormal : |(k.2 0 : ℝ) - (l.2 0 : ℝ)| ≤ (R : ℝ) := by exact_mod_cast hk.2 0
  have hx : |μ * ((k.1 : ℝ) - (l.1 : ℝ))| ≤ μ * (R : ℝ) := by
    rw [abs_mul, abs_of_pos hμ]
    exact mul_le_mul_of_nonneg_left htime hμ.le
  have hy : |μ * ((k.2 0 : ℝ) - (l.2 0 : ℝ))| ≤ μ * (R : ℝ) := by
    rw [abs_mul, abs_of_pos hμ]
    exact mul_le_mul_of_nonneg_left hnormal hμ.le
  have hs : |α * (μ * ((k.1 : ℝ) - (l.1 : ℝ)))| ≤ μ * (R : ℝ) := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hα hx (abs_nonneg _) zero_le_one
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 2 * μ * (R : ℝ))).mpr
  intro i
  fin_cases i
  · change |μ * (k.1 : ℝ) - μ * (l.1 : ℝ)| ≤ 2 * μ * (R : ℝ)
    rw [← mul_sub]
    have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    nlinarith [hx]
  · change |(μ * (k.2 0 : ℝ) + α * (μ * (k.1 : ℝ))) -
        (μ * (l.2 0 : ℝ) + α * (μ * (l.1 : ℝ)))| ≤ 2 * μ * (R : ℝ)
    have hid : (μ * (k.2 0 : ℝ) + α * (μ * (k.1 : ℝ))) -
        (μ * (l.2 0 : ℝ) + α * (μ * (l.1 : ℝ))) =
        μ * ((k.2 0 : ℝ) - (l.2 0 : ℝ)) + α * (μ * ((k.1 : ℝ) - (l.1 : ℝ))) := by ring
    rw [hid]
    exact (abs_add_le _ _).trans (by linarith)

/-- The public integer R-cell has physical scale μR. The bound below keeps
that scale explicit; a=64μ is used only as a source-AD comparison radius. -/
lemma same_spatialCell_source_dist (μ α : ℝ) (hμ : 0 < μ) (hα : |α| ≤ 1)
    {R : ℕ} (hR : 0 < R) {p q : Point}
    (hc : spatialCell R (vertex μ α p) = spatialCell R (vertex μ α q)) :
    dist p q ≤ 4 * μ * (R : ℝ) := by
  have hp := quantization_dist_lt μ α hμ p
  have hq := quantization_dist_lt μ α hμ q
  have hreal := realized_dist_le μ α hμ hα _ _ (same_spatialCell_close hR hc)
  have htri := dist_triangle p (realized μ α (vertex μ α p)) q
  have htri' := dist_triangle (realized μ α (vertex μ α p)) (realized μ α (vertex μ α q)) q
  rw [dist_comm (realized μ α (vertex μ α q)) q] at htri'
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  nlinarith

lemma nearby_integer_divisions {R : ℕ} (hR : 0 < R) {x y : ℤ}
    (hxy : |x - y| ≤ 256 * (R : ℤ)) : |x / (R : ℤ) - y / (R : ℤ)| ≤ 256 := by
  have hR' : (0 : ℤ) < R := by exact_mod_cast hR
  have h₁ : x ≤ y + 256 * R := by have := abs_le.mp hxy; omega
  have h₂ : y ≤ x + 256 * R := by have := abs_le.mp hxy; omega
  have hq₁ := Int.ediv_le_ediv hR' h₁
  have hq₂ := Int.ediv_le_ediv hR' h₂
  have hadd (z : ℤ) : (z + 256 * R) / (R : ℤ) = z / (R : ℤ) + 256 := by
    simpa using Int.add_mul_ediv_right z 256 hR'.ne'
  rw [hadd] at hq₁ hq₂
  exact abs_le.mpr ⟨by omega, by omega⟩

/-- An original physical cell of width 64μR meets only a fixed menu of
literal sheared integer R-cells, including negative labels. -/
lemma coarse_vertex_close (μ α : ℝ) (hμ : 0 < μ) (hα : |α| ≤ 1)
    {R : ℕ} (hR : 0 < R) {p q : Point}
    (hd : dist p q ≤ 64 * μ * (R : ℝ)) :
    |(spatialCell R (vertex μ α p)).1 - (spatialCell R (vertex μ α q)).1| ≤ 256 ∧
    ∀ i, |(spatialCell R (vertex μ α p)).2 i - (spatialCell R (vertex μ α q)).2 i| ≤ 256 := by
  have hp := quantization_dist_lt μ α hμ p
  have hq := quantization_dist_lt μ α hμ q
  have htri := dist_triangle (realized μ α (vertex μ α p)) p (realized μ α (vertex μ α q))
  have htri' := dist_triangle p q (realized μ α (vertex μ α q))
  rw [dist_comm (realized μ α (vertex μ α p)) p] at htri
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hr : dist (realized μ α (vertex μ α p)) (realized μ α (vertex μ α q)) ≤
      66 * μ * (R : ℝ) := by nlinarith
  have hcoords := realized_coordinate_bounds μ α hμ hα _ _ _ hr
  simp only [Int.cast_abs, Int.cast_sub] at hcoords
  have hxR : (|(vertex μ α p).1 - (vertex μ α q).1| : ℝ) ≤ 256 * (R : ℝ) := by
    apply (mul_le_mul_iff_left₀ hμ).mp
    nlinarith [hcoords.1]
  have hyR : (|(vertex μ α p).2 0 - (vertex μ α q).2 0| : ℝ) ≤ 256 * (R : ℝ) := by
    apply (mul_le_mul_iff_left₀ hμ).mp
    nlinarith [hcoords.2]
  constructor
  · exact nearby_integer_divisions hR (by exact_mod_cast hxR)
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact nearby_integer_divisions hR (by exact_mod_cast hyR)

def coarseBox (c : Vertex) : Finset Vertex :=
  (Finset.Icc (c.1 - 256) (c.1 + 256)).product
    (Fintype.piFinset fun i => Finset.Icc (c.2 i - 256) (c.2 i + 256))

lemma coarseBox_card (c : Vertex) : (coarseBox c).card = 513 ^ 2 := by
  have hicc (z : ℤ) : (Finset.Icc (z - 256) (z + 256)).card = 513 := by
    rw [Int.card_Icc]
    omega
  simp [coarseBox, hicc, Fintype.card_piFinset]

lemma coarse_image_card_le (μ α : ℝ) (hμ : 0 < μ) (hα : |α| ≤ 1)
    {R : ℕ} (hR : 0 < R) (S : Finset Point)
    (hdiam : ∀ p ∈ S, ∀ q ∈ S, dist p q ≤ 64 * μ * (R : ℝ)) :
    (S.image (fun p => spatialCell R (vertex μ α p))).card ≤ 513 ^ 2 := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨q, hq⟩ := hS
    rw [← coarseBox_card (spatialCell R (vertex μ α q))]
    apply Finset.card_le_card
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    have hclose := coarse_vertex_close μ α hμ hα hR (hdiam p hp q hq)
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨by have := abs_le.mp hclose.1; omega, by have := abs_le.mp hclose.1; omega⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_Icc.mpr ⟨by have := abs_le.mp (hclose.2 i); omega,
        by have := abs_le.mp (hclose.2 i); omega⟩
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hz]

lemma image_card_le_reference_mul {X B D : Type*} [DecidableEq B] [DecidableEq D]
    (S : Finset X) (f : X → B) (g : X → D) (C : ℕ)
    (hC : ∀ z, ((S.filter (fun p => g p = z)).image f).card ≤ C) :
    (S.image f).card ≤ (S.image g).card * C := by
  classical
  have hsub : S.image f ⊆ (S.image g).biUnion (fun z => (S.filter (fun p => g p = z)).image f) := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_biUnion.mpr ⟨g p, Finset.mem_image_of_mem g hp,
      Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩⟩
  calc
    (S.image f).card ≤ ((S.image g).biUnion (fun z => (S.filter (fun p => g p = z)).image f)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ z ∈ S.image g, ((S.filter (fun p => g p = z)).image f).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ S.image g, C := Finset.sum_le_sum (fun z _ => hC z)
    _ = (S.image g).card * C := by simp

/-- Counting actual quantizer labels through actual original-grid cells. -/
lemma coarse_menu_card_le_grid (μ α : ℝ) (hμ : 0 < μ) (hα : |α| ≤ 1)
    {R : ℕ} (hR : 0 < R) (S : Finset Point) :
    (S.image (fun p => spatialCell R (vertex μ α p))).card ≤
      (S.image (ADGridCoverMenus.gridLabel (64 * μ * (R : ℝ)))).card * 513 ^ 2 := by
  classical
  apply image_card_le_reference_mul
  intro c
  apply coarse_image_card_le μ α hμ hα hR
  intro p hp q hq
  have heq : ADGridCoverMenus.gridLabel (64 * μ * (R : ℝ)) p =
      ADGridCoverMenus.gridLabel (64 * μ * (R : ℝ)) q :=
    (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  exact (SeparatedAlignmentPatches.same_cell_dist_lt _ (by positivity) p q heq).le

lemma vertex_image_card_le_grid (μ α : ℝ) (hμ : 0 < μ) (hα : |α| ≤ 1)
    (S : Finset Point) :
    (S.image (vertex μ α)).card ≤
      (S.image (ADGridCoverMenus.gridLabel (64 * μ))).card * 513 ^ 2 := by
  have h := coarse_menu_card_le_grid μ α hμ hα (R := 1) (by decide) S
  simpa only [spatialCell, Nat.cast_one, Int.ediv_one, mul_one, Prod.eta] using h

/-- The exact source preimage of one output integer cell. -/
def cellPreimage (Ω : Finset Point) (μ α : ℝ) (R : ℕ) (c : Vertex) : Finset Point := by
  classical
  exact Ω.filter (fun p => spatialCell R (vertex μ α p) = c)

lemma cellPreimage_image (Ω : Finset Point) (μ α : ℝ) (R : ℕ) (c : Vertex) :
    (cellPreimage Ω μ α R c).image (vertex μ α) =
      (Ω.image (vertex μ α)).filter (fun k => spatialCell R k = c) := by
  classical
  ext k
  simp only [cellPreimage, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hc⟩, rfl⟩
    exact ⟨⟨p, hp, rfl⟩, hc⟩
  · rintro ⟨⟨p, hp, rfl⟩, hc⟩
    exact ⟨p, ⟨hp, hc⟩, rfl⟩

lemma cellPreimage_subset (Ω : Finset Point) (μ α : ℝ) (R : ℕ) (c : Vertex) :
    cellPreimage Ω μ α R c ⊆ Ω := by
  classical
  exact Finset.filter_subset _ _

lemma cellPreimage_diameter (Ω : Finset Point) (μ α : ℝ) (hμ : 0 < μ) (hα : |α| ≤ 1)
    {R : ℕ} (hR : 0 < R) (c : Vertex) :
    ∀ p ∈ cellPreimage Ω μ α R c, ∀ q ∈ cellPreimage Ω μ α R c,
      dist p q ≤ 64 * μ * (R : ℝ) := by
  classical
  intro p hp q hq
  have heq := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  have hd := same_spatialCell_source_dist μ α hμ hα hR heq
  have hRnonneg : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  nlinarith

/-- Original preimage mass is counted at a=64μ≥δ, never at the possibly
sub-δ quantization mesh μ. For unit source weights this is exactly hvertex. -/
theorem vertex_preimage_card_le (A Ω : Finset Point) (hΩ : Ω ⊆ A)
    {δ μ α K t : ℝ} (hδ : 0 < δ) (hμ : 0 < μ) (hδa : δ ≤ 64 * μ)
    (ha : 64 * μ ≤ 1) (hα : |α| ≤ 1) (hK : 1 ≤ K)
    (hAD : ADBounds A δ K t) (z : Vertex) :
    ((Ω.filter (fun p => vertex μ α p = z)).card : ℝ) ≤ K * ((64 * μ) / δ) ^ t := by
  classical
  let S := Ω.filter (fun p => vertex μ α p = z)
  by_cases hS : S.Nonempty
  · obtain ⟨q, hq⟩ := hS
    have hqA : q ∈ A := hΩ (Finset.mem_filter.mp hq).1
    have hsub : S ⊆ carrierBall A q (64 * μ) := by
      intro p hp
      apply (mem_carrierBall A p q (64 * μ)).mpr
      refine ⟨hΩ (Finset.mem_filter.mp hp).1, ?_⟩
      have heq : vertex μ α p = vertex μ α q :=
        (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
      have hd := same_spatialCell_source_dist μ α hμ hα (R := 1) (by decide)
        (congrArg (spatialCell 1) heq)
      simp only [Nat.cast_one, mul_one] at hd
      linarith
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hAD q hqA (64 * μ) hδa ha).2
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (S.card : ℝ) ≤ _
    rw [hz, Finset.card_empty, Nat.cast_zero]
    have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
    positivity

def referenceFactor (t : ℝ) : ℝ := (513 : ℝ) ^ 2 * (9 : ℝ) ^ 2 * (6 : ℝ) ^ t

def referenceConstant : ℝ := (513 : ℝ) ^ 2 * (9 : ℝ) ^ 2 * (6 : ℝ) ^ 2

lemma referenceFactor_le_constant {t : ℝ} (ht : t ≤ 2) : referenceFactor t ≤ referenceConstant := by
  have hp : (6 : ℝ) ^ t ≤ (6 : ℝ) ^ (2 : ℕ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6) ht
  exact mul_le_mul_of_nonneg_left hp (by norm_num)

/-- hspace in the exact raw-grid convention N=b/μ. The auxiliary original-grid
radius is 64μR≥δ, and the parent is enlarged to diameter 64b only inside the AD
cover argument. Both changes are proved finite-menu comparisons. -/
theorem spatial_menu_card_le (A Ω : Finset Point) (hΩ : Ω ⊆ A)
    {δ μ b α K t : ℝ} (hδ : 0 < δ) (hμ : 0 < μ) (hδa : δ ≤ 64 * μ)
    (hb : b ≤ 1 / 64) (hα : |α| ≤ 1) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t)
    (hparent : ∀ p ∈ Ω, ∀ q ∈ Ω, dist p q ≤ b)
    {R : ℕ} (hR : 0 < R) (hRtop : μ * (R : ℝ) ≤ b) :
    ((Ω.image (fun p => spatialCell R (vertex μ α p))).card : ℝ) ≤
      referenceFactor t * K ^ 2 * (b / (μ * (R : ℝ))) ^ t := by
  classical
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hbpos : 0 < b := (mul_pos hμ hRpos).trans_le hRtop
  have hscale : δ ≤ 64 * μ * (R : ℝ) := by nlinarith
  have hscaleone : 64 * μ * (R : ℝ) ≤ 1 := by nlinarith
  have hparentScale : 64 * μ * (R : ℝ) ≤ 64 * b := by nlinarith
  have hparent' : ∀ p ∈ Ω, ∀ q ∈ Ω, dist p q ≤ 64 * b := by
    intro p hp q hq
    have := hparent p hp q hq
    linarith
  have hgrid := ADGridCoverMenus.diameter_subset_occupied_grid_cells_le A Ω
    hδ hscale hscaleone hparentScale hK ht ht2 hdiam hAD hΩ hparent'
  have hquant := coarse_menu_card_le_grid μ α hμ hα hR Ω
  have hquantR : ((Ω.image (fun p => spatialCell R (vertex μ α p))).card : ℝ) ≤
      ((Ω.image (ADGridCoverMenus.gridLabel (64 * μ * (R : ℝ)))).card : ℝ) * (513 : ℝ) ^ 2 := by
    exact_mod_cast hquant
  have hratio : (64 * b) / (64 * μ * (R : ℝ)) = b / (μ * (R : ℝ)) := by
    field_simp
  calc
    ((Ω.image (fun p => spatialCell R (vertex μ α p))).card : ℝ) ≤
        ((Ω.image (ADGridCoverMenus.gridLabel (64 * μ * (R : ℝ)))).card : ℝ) * (513 : ℝ) ^ 2 := hquantR
    _ ≤ ((9 : ℝ) ^ 2 * (6 : ℝ) ^ t * K ^ 2 * ((64 * b) / (64 * μ * (R : ℝ))) ^ t) * (513 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hgrid (by norm_num)
    _ = referenceFactor t * K ^ 2 * (b / (μ * (R : ℝ))) ^ t := by rw [hratio]; dsimp [referenceFactor]; ring

/-- hcell counts distinct quantized vertices, rather than original source mass.
Its proof compares those vertices to actual a-grid cells with a=64μ≥δ. -/
theorem spatial_cell_card_le (A Ω : Finset Point) (hΩ : Ω ⊆ A)
    {δ μ α K t : ℝ} (hδ : 0 < δ) (hμ : 0 < μ) (hδa : δ ≤ 64 * μ)
    (ha : 64 * μ ≤ 1) (hα : |α| ≤ 1) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t)
    {R : ℕ} (hR : 0 < R) (c : Vertex) :
    (((Ω.image (vertex μ α)).filter (fun k => spatialCell R k = c)).card : ℝ) ≤
      referenceFactor t * K ^ 2 * (R : ℝ) ^ t := by
  classical
  let S := cellPreimage Ω μ α R c
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hSA : S ⊆ A := (cellPreimage_subset Ω μ α R c).trans hΩ
  have hSR : 64 * μ ≤ 64 * μ * (R : ℝ) := by nlinarith
  have hgrid := ADGridCoverMenus.diameter_subset_occupied_grid_cells_le A S
    hδ hδa ha hSR hK ht ht2 hdiam hAD hSA (cellPreimage_diameter Ω μ α hμ hα hR c)
  have hquant := vertex_image_card_le_grid μ α hμ hα S
  have hquantR : ((S.image (vertex μ α)).card : ℝ) ≤
      ((S.image (ADGridCoverMenus.gridLabel (64 * μ))).card : ℝ) * (513 : ℝ) ^ 2 := by
    exact_mod_cast hquant
  have hratio : (64 * μ * (R : ℝ)) / (64 * μ) = (R : ℝ) := by field_simp
  rw [← cellPreimage_image]
  change ((S.image (vertex μ α)).card : ℝ) ≤ _
  calc
    ((S.image (vertex μ α)).card : ℝ) ≤
        ((S.image (ADGridCoverMenus.gridLabel (64 * μ))).card : ℝ) * (513 : ℝ) ^ 2 := hquantR
    _ ≤ ((9 : ℝ) ^ 2 * (6 : ℝ) ^ t * K ^ 2 * ((64 * μ * (R : ℝ)) / (64 * μ)) ^ t) * (513 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hgrid (by norm_num)
    _ = referenceFactor t * K ^ 2 * (R : ℝ) ^ t := by rw [hratio]; dsimp [referenceFactor]; ring

/-- The integer preimage cap required by the weighted finite alignment theorem,
for honest unit weights on original points, is constructed by a single ceiling.
This ceiling is a vertex cap, not a repeated pruning charge. -/
theorem exists_integer_vertex_cap (A Ω : Finset Point) (hΩ : Ω ⊆ A)
    {δ μ α K t : ℝ} (hδ : 0 < δ) (hμ : 0 < μ) (hδa : δ ≤ 64 * μ)
    (ha : 64 * μ ≤ 1) (hα : |α| ≤ 1) (hK : 1 ≤ K) (ht : 0 ≤ t)
    (hAD : ADBounds A δ K t) :
    ∃ U : ℕ, 0 < U ∧ (U : ℝ) ≤ 2 * K * ((64 * μ) / δ) ^ t ∧
      ∀ z : Vertex, SelfUniform.mass (fun _ : Point => 1)
        (Ω.filter (fun p => vertex μ α p = z)) ≤ U := by
  classical
  let cap : ℝ := K * ((64 * μ) / δ) ^ t
  have hratio : 1 ≤ (64 * μ) / δ := (le_div_iff₀ hδ).mpr (by simpa using hδa)
  have hpow : (1 : ℝ) ≤ ((64 * μ) / δ) ^ t := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hratio ht
  have hcap : 1 ≤ cap := one_le_mul_of_one_le_of_one_le hK hpow
  refine ⟨⌈cap⌉₊, ?_, ?_, ?_⟩
  · have hle : (1 : ℝ) ≤ (⌈cap⌉₊ : ℝ) := hcap.trans (Nat.le_ceil cap)
    exact_mod_cast hle
  · have hc := Nat.ceil_lt_add_one (show 0 ≤ cap by linarith)
    have hmul : 2 * cap = 2 * K * ((64 * μ) / δ) ^ t := by dsimp [cap]; ring
    rw [← hmul]
    linarith
  · intro z
    have hb := vertex_preimage_card_le A Ω hΩ hδ hμ hδa ha hα hK hAD z
    have hc : (((Ω.filter (fun p => vertex μ α p = z)).card) : ℝ) ≤ (⌈cap⌉₊ : ℝ) :=
      hb.trans (Nat.le_ceil cap)
    have hn : (Ω.filter (fun p => vertex μ α p = z)).card ≤ ⌈cap⌉₊ := by exact_mod_cast hc
    simpa [SelfUniform.mass] using hn

end
end ShearedGridADReference
