import Theorems.Thm_StickyKakeya4_native_weighted_point_populations
import Theorems.Thm_StickyKakeya4_physical_rescaling_incidence_transfer
import Theorems.Thm_StickyKakeya4_native_source_size_bounds
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators
open Classical Finset SelfUniform IncidenceBinTransfer NativeWeightedPointPopulations
namespace NativeOriginalSlicePopulation
abbrev Cell := PhysicalRescalingIncidenceTransfer.Cell
abbrev PhaseCell := (Fin 3 → ℤ) × (Fin 3 → ℤ) × ℤ
variable {T : Type*}

def originalWeight (P : PhysicalRescalingIncidenceTransfer.Data T) (b : T × Cell) : ℕ :=
  (binFiber P.incidences P.cellBin b).card

def originalPullback (P : PhysicalRescalingIncidenceTransfer.Data T)
    (B : Finset (T × Cell)) : Finset (T × Cell) :=
  P.incidences.filter (fun a => binLabel P.cellBin a ∈ B)

def spatialLabel (R : ℕ) (c : Cell) : ℤ × (Fin 3 → ℤ) :=
  (c.2, fun i => c.1 i / (R : ℤ))

def phaseLabel (P : PhysicalRescalingIncidenceTransfer.Data T)
    (offsetMesh slopeMesh : ℝ) (timeDiv : ℕ) (b : T × Cell) : PhaseCell :=
  ((fun i => ⌊P.offset b.1 i / offsetMesh⌋),
    (fun i => ⌊P.slope b.1 i / slopeMesh⌋), b.2.2 / (timeDiv : ℤ))

def preparedLabel {d : ℕ} (P : PhysicalRescalingIncidenceTransfer.Data T)
    (radii timeDiv : Fin d → ℕ) (offsetMesh slopeMesh : Fin d → ℝ) :
    Fin ((1 + d) + d) → (T × Cell) → (Cell ⊕ (ℤ × (Fin 3 → ℤ)) ⊕ PhaseCell) :=
  Fin.addCases (Fin.addCases (fun _ b => Sum.inl b.2)
    (fun j b => Sum.inr (Sum.inl (spatialLabel (radii j) b.2))))
    (fun j b => Sum.inr (Sum.inr (phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) b)))

lemma originalPullback_subset (P : PhysicalRescalingIncidenceTransfer.Data T)
    (B : Finset (T × Cell)) : originalPullback P B ⊆ P.incidences :=
  filter_subset _ _

lemma originalPullback_fiber (P : PhysicalRescalingIncidenceTransfer.Data T)
    (B : Finset (T × Cell)) {b : T × Cell} (hb : b ∈ B) :
    binFiber (originalPullback P B) P.cellBin b = binFiber P.incidences P.cellBin b := by
  ext a
  simp only [binFiber, originalPullback, mem_filter]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨ha, he⟩
    exact ⟨⟨ha, he ▸ hb⟩, he⟩

lemma originalPullback_mass (P : PhysicalRescalingIncidenceTransfer.Data T)
    (B : Finset (T × Cell)) :
    (originalPullback P B).card = mass (originalWeight P) B := by
  have h := Finset.sum_fiberwise_of_maps_to (M := ℕ) (g := binLabel P.cellBin)
    (s := originalPullback P B) (t := B) (fun a ha => (mem_filter.mp ha).2) (fun _ => 1)
  have hsum : (∑ b ∈ B, (binFiber (originalPullback P B) P.cellBin b).card) =
      (originalPullback P B).card := by simpa [binFiber] using h
  rw [← hsum]
  unfold mass originalWeight
  apply sum_congr rfl
  intro b hb
  rw [originalPullback_fiber P B hb]

lemma originalPullback_bins (P : PhysicalRescalingIncidenceTransfer.Data T)
    (B : Finset (T × Cell)) (hB : B ⊆ P.newIncidences) :
    bins (originalPullback P B) P.cellBin = B := by
  ext b
  constructor
  · rintro hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    exact (mem_filter.mp ha).2
  · intro hb
    have hheavy := mem_heavyBins.mp (hB hb)
    obtain ⟨a, ha, he⟩ := mem_image.mp hheavy.1
    exact mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, he ▸ hb⟩, he⟩

lemma originalPullback_subset_kept (P : PhysicalRescalingIncidenceTransfer.Data T)
    (B : Finset (T × Cell)) (hB : B ⊆ P.newIncidences) :
    originalPullback P B ⊆ P.keptIncidences := by
  intro a ha
  exact mem_filter.mpr ⟨(mem_filter.mp ha).1, hB (mem_filter.mp ha).2⟩

lemma originalPullback_support (P : PhysicalRescalingIncidenceTransfer.Data T)
    (B : Finset (T × Cell)) (hB : B ⊆ P.newIncidences) :
    (originalPullback P B).image (fun a => P.cellBin a.2) = B.image Prod.snd := by
  conv_rhs => rw [← originalPullback_bins P B hB]
  simp only [bins, image_image, binLabel, Function.comp_def]

lemma originalPullback_sum (P : PhysicalRescalingIncidenceTransfer.Data T)
    (B : Finset (T × Cell)) (v : T × Cell → ℕ) :
    (∑ a ∈ originalPullback P B, v (binLabel P.cellBin a)) =
      ∑ b ∈ B, originalWeight P b * v b := by
  have h := Finset.sum_fiberwise_of_maps_to (M := ℕ) (g := binLabel P.cellBin)
    (s := originalPullback P B) (t := B) (fun a ha => (mem_filter.mp ha).2)
    (fun a => v (binLabel P.cellBin a))
  rw [← h]
  apply sum_congr rfl
  intro b hb
  change (∑ a ∈ binFiber (originalPullback P B) P.cellBin b, v (binLabel P.cellBin a)) = _
  rw [originalPullback_fiber P B hb]
  calc
    _ = ∑ _a ∈ binFiber P.incidences P.cellBin b, v b := by
      apply sum_congr rfl
      intro a ha
      rw [(mem_binFiber.mp ha).2]
    _ = _ := by simp [originalWeight]

/-- Coarse weighted degrees are exactly counts of ORIGINAL selected incidence
labels, with every original label in each selected tube/bin fiber retained. -/
lemma originalPullback_degree {Y : Type*}
    (P : PhysicalRescalingIncidenceTransfer.Data T)
    (B : Finset (T × Cell)) (f : T × Cell → Y) (a : T × Cell) :
    degree (fun _ => 1) (fun b c => f (binLabel P.cellBin b) = f (binLabel P.cellBin c))
        (originalPullback P B) a =
      degree (originalWeight P) (fun b c => f b = f c) B (binLabel P.cellBin a) := by
  classical
  unfold degree
  let v : T × Cell → ℕ := fun b => if f (binLabel P.cellBin a) = f b then 1 else 0
  calc
    _ = ∑ b ∈ originalPullback P B, v (binLabel P.cellBin b) := by
      apply sum_congr rfl
      intro b _hb
      by_cases hf : f (binLabel P.cellBin a) = f (binLabel P.cellBin b) <;> simp [v, hf]
    _ = ∑ b ∈ B, originalWeight P b * v b := originalPullback_sum P B v
    _ = _ := by
      apply sum_congr rfl
      intro b _hb
      by_cases hf : f (binLabel P.cellBin a) = f b <;> simp [v, hf]

lemma originalWeight_pos (P : PhysicalRescalingIncidenceTransfer.Data T)
    {b : T × Cell} (hb : b ∈ P.newIncidences) : 0 < originalWeight P b :=
  P.m_pos.trans_le (mem_heavyBins.mp hb).2

lemma originalWeight_total (P : PhysicalRescalingIncidenceTransfer.Data T) :
    mass (originalWeight P) P.newIncidences = P.keptIncidences.card := by
  simpa [mass, originalWeight] using (P.retained_weights (fun _ => (1 : ℕ))).symm

/-- A single refinement of actual heavy tube/bin pairs, weighted by their full
original incidence fibers. Every displayed population is measured on this same
selected set; the point population counts DISTINCT bins, not incidences. -/
theorem refine_original_incidence_labels
    (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (hne : P.incidences.Nonempty) {L d : ℕ} (hL : 0 < L)
    (radii timeDiv : Fin d → ℕ) (offsetMesh slopeMesh : Fin d → ℝ) :
    ∃ B ⊆ P.newIncidences, B.Nonempty ∧
      P.incidences.card ≤ 4 * (4 * ((1 + d) + d)) ^ (((1 + d) + d) * L) *
        (originalPullback P B).card ∧
      (∀ x ∈ B.image Prod.snd, ∀ y ∈ B.image Prod.snd,
        projectedWeight (originalWeight P) Prod.snd B x ≤
          NativeSourceSizeBounds.radix P.incidences.card L ^ 2 *
            projectedWeight (originalWeight P) Prod.snd B y) ∧
      (∀ j : Fin d, ∀ a ∈ B, ∀ b ∈ B,
        degree (originalWeight P) (fun c e =>
          spatialLabel (radii j) c.2 = spatialLabel (radii j) e.2) B a ≤
        NativeSourceSizeBounds.radix P.incidences.card L ^ 2 *
          degree (originalWeight P) (fun c e =>
            spatialLabel (radii j) c.2 = spatialLabel (radii j) e.2) B b) ∧
      (∀ j : Fin d, ∀ a ∈ B, ∀ b ∈ B,
        degree (originalWeight P) (fun c e =>
          phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) c =
          phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) e) B a ≤
        NativeSourceSizeBounds.radix P.incidences.card L ^ 2 *
          degree (originalWeight P) (fun c e =>
            phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) c =
            phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) e) B b) ∧
      (∀ j : Fin d, ∀ x ∈ B.image Prod.snd, ∀ y ∈ B.image Prod.snd,
        (classPoints (B.image Prod.snd) (spatialLabel (radii j)) x).card ≤
          NativeSourceSizeBounds.radix P.incidences.card L ^ 4 *
            (classPoints (B.image Prod.snd) (spatialLabel (radii j)) y).card) := by
  classical
  let Q := NativeSourceSizeBounds.radix P.incidences.card L
  let labels := preparedLabel P radii timeDiv offsetMesh slopeMesh
  let R := fun i a b => labels i a = labels i b
  have hmass : mass (originalWeight P) P.newIncidences ≤ P.incidences.card := by
    rw [originalWeight_total]
    exact card_le_card (kept_subset _ _ _)
  have hhalf := P.half_mass hP
  have hnew : P.newIncidences.Nonempty := by
    apply SelfUniform.nonempty_of_mass_pos (originalWeight P)
    rw [originalWeight_total]
    have hi := card_pos.mpr hne
    omega
  obtain ⟨B, hB, hneB, hret, hdeg⟩ := weighted_self_uniform_refinement
    (Q := Q) (L := L) (by omega : 0 < (1 + d) + d)
    (NativeSourceSizeBounds.radix_four_le _ _) (originalWeight P) R
    (fun _ _ => rfl) (fun _ _ _ h => h.symm) P.newIncidences hnew
    (fun _ hb => originalWeight_pos P hb)
    (hmass.trans (NativeSourceSizeBounds.card_le_radix_pow _ hL))
  have hpoint : ∀ x ∈ B.image Prod.snd, ∀ y ∈ B.image Prod.snd,
      projectedWeight (originalWeight P) Prod.snd B x ≤
        Q ^ 2 * projectedWeight (originalWeight P) Prod.snd B y := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    have h := hdeg (Fin.castAdd d (Fin.castAdd d (0 : Fin 1))) a b ha hb
    simpa [R, labels, preparedLabel, degree_eq_projectedWeight] using h
  have hspatial : ∀ j : Fin d, ∀ a ∈ B, ∀ b ∈ B,
      degree (originalWeight P) (fun c e =>
        spatialLabel (radii j) c.2 = spatialLabel (radii j) e.2) B a ≤
      Q ^ 2 * degree (originalWeight P) (fun c e =>
        spatialLabel (radii j) c.2 = spatialLabel (radii j) e.2) B b := by
    intro j a ha b hb
    have h := hdeg (Fin.castAdd d (Fin.natAdd 1 j)) a b ha hb
    simpa [R, labels, preparedLabel] using h
  refine ⟨B, hB, hneB, ?_, hpoint, hspatial, ?_, ?_⟩
  · rw [originalWeight_total] at hret
    rw [← originalPullback_mass] at hret
    calc
      P.incidences.card ≤ 2 * P.keptIncidences.card := hhalf
      _ ≤ 2 * (2 * (4 * ((1 + d) + d)) ^ (((1 + d) + d) * L) *
          (originalPullback P B).card) := Nat.mul_le_mul_left _ hret
      _ = _ := by ring
  · intro j a ha b hb
    have h := hdeg (Fin.natAdd (1 + d) j) a b ha hb
    simpa [R, labels, preparedLabel] using h
  · intro j
    exact cardinality_uniform_of_weighted_degrees (originalWeight P) Prod.snd B
      (spatialLabel (radii j)) Q hneB (fun _ hb => originalWeight_pos P (hB hb))
      hpoint (hspatial j)
end NativeOriginalSlicePopulation
