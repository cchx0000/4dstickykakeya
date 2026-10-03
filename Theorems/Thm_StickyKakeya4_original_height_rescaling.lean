import Theorems.Thm_StickyKakeya4_compatible_tuple_selection
import Theorems.Thm_StickyKakeya4_physical_rescaling_backbone_density

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

noncomputable section
open Classical SelfUniform CompatibleTupleSelection IncidenceBinTransfer

namespace OriginalHeightRescaling

/-! Incidence labels are genuine geometric pairs `(tube, oldCell)`. Optional
weights are original masses attached to those pairs; duplicate auxiliary marks
are not counted as distinct geometric incidences by the image-cardinality or
multiplicity theorems. The input grid mesh is understood after any prior
physical thickening. -/

abbrev Cell := ShearBinFibers.Index

variable {T : Type*}

def oldTime (e : T × Cell) : ℤ := e.2.2
def coarseTime (N : ℕ) (e : T × Cell) : ℤ := oldTime e / (N : ℤ)
def atHeight (I : Finset (T × Cell)) (z : ℤ) : Finset (T × Cell) := I.filter (fun e => oldTime e = z)
def inTimeBin (I : Finset (T × Cell)) (N : ℕ) (q : ℤ) : Finset (T × Cell) :=
  I.filter (fun e => coarseTime N e = q)
def heightMenu (I : Finset (T × Cell)) (N : ℕ) (q : ℤ) : Finset ℤ :=
  (inTimeBin I N q).image oldTime

def timeFiber (N : ℕ) (q : ℤ) : Finset ℤ :=
  Finset.Ico (q * (N : ℤ)) (q * (N : ℤ) + (N : ℤ))

lemma mem_timeFiber (N : ℕ) (hN : 0 < N) (q z : ℤ) :
    z ∈ timeFiber N q ↔ z / (N : ℤ) = q := by
  rw [timeFiber, Finset.mem_Ico]
  exact (Int.ediv_eq_iff_of_pos (by exact_mod_cast hN)).symm

lemma card_timeFiber (N : ℕ) (q : ℤ) : (timeFiber N q).card = N := by
  simp [timeFiber, Int.card_Ico]

/-- The number of ORIGINAL integer heights in one time bin is derived from
its literal Euclidean-division interval, including negative time indices. -/
lemma heightMenu_card_le (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N) (q : ℤ) :
    (heightMenu I N q).card ≤ N := by
  calc
    (heightMenu I N q).card ≤ (timeFiber N q).card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      exact (mem_timeFiber N hN q (oldTime e)).mpr (Finset.mem_filter.mp he).2
    _ = N := card_timeFiber N q

/-- One maximizing actual old height per occupied global time bin. Empty bins
use their left endpoint, so no new incidence is ever introduced. -/
def chosenHeight (I : Finset (T × Cell)) (N : ℕ) (w : T × Cell → ℕ) (q : ℤ) : ℤ :=
  if h : (heightMenu I N q).Nonempty then
    Classical.choose (Finset.exists_max_image (heightMenu I N q)
      (fun z => mass w (atHeight I z)) h)
  else q * (N : ℤ)

lemma chosenHeight_mem (I : Finset (T × Cell)) (N : ℕ) (w : T × Cell → ℕ)
    (q : ℤ) (hq : (heightMenu I N q).Nonempty) : chosenHeight I N w q ∈ heightMenu I N q := by
  rw [chosenHeight, dif_pos hq]
  exact (Classical.choose_spec (Finset.exists_max_image (heightMenu I N q)
    (fun z => mass w (atHeight I z)) hq)).1

lemma chosenHeight_max (I : Finset (T × Cell)) (N : ℕ) (w : T × Cell → ℕ)
    (q : ℤ) (hq : (heightMenu I N q).Nonempty) (z : ℤ) (hz : z ∈ heightMenu I N q) :
    mass w (atHeight I z) ≤ mass w (atHeight I (chosenHeight I N w q)) := by
  rw [chosenHeight, dif_pos hq]
  exact (Classical.choose_spec (Finset.exists_max_image (heightMenu I N q)
    (fun z => mass w (atHeight I z)) hq)).2 z hz

lemma chosenHeight_bin (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (w : T × Cell → ℕ) (q : ℤ) : chosenHeight I N w q / (N : ℤ) = q := by
  by_cases hq : (heightMenu I N q).Nonempty
  · obtain ⟨e, he, hz⟩ := Finset.mem_image.mp (chosenHeight_mem I N w q hq)
    rw [← hz]
    exact (Finset.mem_filter.mp he).2
  · rw [chosenHeight, dif_neg hq]
    exact Int.mul_ediv_cancel q (by exact_mod_cast Nat.ne_of_gt hN)

/-- Retain ALL original incidences at the globally chosen height. The height
function has no tube or point argument. Original tube and time labels persist. -/
def selected (I : Finset (T × Cell)) (N : ℕ) (w : T × Cell → ℕ) : Finset (T × Cell) :=
  I.filter (fun e => oldTime e = chosenHeight I N w (coarseTime N e))

@[simp] lemma mem_selected (I : Finset (T × Cell)) (N : ℕ) (w : T × Cell → ℕ) (e : T × Cell) :
    e ∈ selected I N w ↔ e ∈ I ∧ oldTime e = chosenHeight I N w (coarseTime N e) := Finset.mem_filter

lemma selected_subset (I : Finset (T × Cell)) (N : ℕ) (w : T × Cell → ℕ) : selected I N w ⊆ I :=
  Finset.filter_subset _ _

lemma selected_bin_fiber (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (w : T × Cell → ℕ) (q : ℤ) :
    inTimeBin (selected I N w) N q = atHeight I (chosenHeight I N w q) := by
  ext e
  constructor
  · intro he
    obtain ⟨heS, heq⟩ := Finset.mem_filter.mp he
    obtain ⟨heI, hheight⟩ := (mem_selected I N w e).mp heS
    exact Finset.mem_filter.mpr ⟨heI, by simpa only [heq] using hheight⟩
  · intro he
    obtain ⟨heI, hheight⟩ := Finset.mem_filter.mp he
    have heq : coarseTime N e = q := by
      dsimp [coarseTime]
      rw [hheight]
      exact chosenHeight_bin I N hN w q
    exact Finset.mem_filter.mpr ⟨(mem_selected I N w e).mpr ⟨heI, by rw [heq]; exact hheight⟩, heq⟩

lemma selected_bin_image (I : Finset (T × Cell)) (N : ℕ) (_hN : 0 < N)
    (w : T × Cell → ℕ) : (selected I N w).image (coarseTime N) = I.image (coarseTime N) := by
  apply Finset.Subset.antisymm (Finset.image_subset_image (selected_subset I N w))
  intro q hq
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hq
  have hmenu : (heightMenu I N q).Nonempty :=
    ⟨oldTime e, Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, heq⟩, rfl⟩⟩
  obtain ⟨f, hf, hfheight⟩ := Finset.mem_image.mp (chosenHeight_mem I N w q hmenu)
  have hfq := (Finset.mem_filter.mp hf).2
  refine Finset.mem_image.mpr ⟨f, ?_, hfq⟩
  exact (mem_selected I N w f).mpr ⟨(Finset.mem_filter.mp hf).1, by rw [hfq]; exact hfheight⟩

/-- Existing weighted fiber selection gives the loss estimate; the chosen
maximizer can only improve its retained mass. -/
lemma bin_mass_le_selected_height (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (w : T × Cell → ℕ) (q : ℤ) :
    mass w (inTimeBin I N q) ≤ N * mass w (atHeight I (chosenHeight I N w q)) := by
  obtain ⟨G, hG, hmass, hsame⟩ := weighted_fiber_selection w (inTimeBin I N q) oldTime N
    (heightMenu_card_le I N hN q)
  have hGM : mass w G ≤ mass w (atHeight I (chosenHeight I N w q)) := by
    by_cases hne : G.Nonempty
    · obtain ⟨e, he⟩ := hne
      have hz : oldTime e ∈ heightMenu I N q := Finset.mem_image.mpr ⟨e, hG he, rfl⟩
      apply (mass_mono w ?_).trans (chosenHeight_max I N w q ⟨oldTime e, hz⟩ (oldTime e) hz)
      intro f hf
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (hG hf)).1, hsame f e hf he⟩
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne, mass]
  exact hmass.trans (Nat.mul_le_mul_left _ hGM)

/-- At most N loss of original additive mass, with empty incidence sets and
zero weights allowed. All chosen-height fibers are kept in full. -/
theorem weighted_height_retention (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (w : T × Cell → ℕ) : mass w I ≤ N * mass w (selected I N w) := by
  have hsum : mass w (selected I N w) =
      ∑ q ∈ I.image (coarseTime N), mass w (atHeight I (chosenHeight I N w q)) := by
    rw [mass_eq_sum_partition w (selected I N w) (coarseTime N), selected_bin_image I N hN w]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [← selected_bin_fiber I N hN w q]
    rfl
  calc
    mass w I = ∑ q ∈ I.image (coarseTime N), mass w (inTimeBin I N q) :=
      mass_eq_sum_partition w I (coarseTime N)
    _ ≤ ∑ q ∈ I.image (coarseTime N), N * mass w (atHeight I (chosenHeight I N w q)) :=
      Finset.sum_le_sum (fun q _hq => bin_mass_le_selected_height I N hN w q)
    _ = N * mass w (selected I N w) := by rw [hsum, Finset.mul_sum]

lemma height_card_retention (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N) :
    I.card ≤ N * (selected I N (fun _ => 1)).card := by
  simpa only [mass, Finset.sum_const, smul_eq_mul, Nat.mul_one] using
    weighted_height_retention I N hN (fun _ => 1)

/-- Every retained spatial point keeps its whole original point-incidence fiber,
across every original tube row. -/
lemma selected_point_fiber (I : Finset (T × Cell)) (N : ℕ) (w : T × Cell → ℕ)
    (c : Cell) (hc : c ∈ oldCells (selected I N w)) :
    (selected I N w).filter (fun e => e.2 = c) = I.filter (fun e => e.2 = c) := by
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
  have htime := ((mem_selected I N w e).mp he).2
  ext f
  constructor
  · intro hf
    obtain ⟨hfS, hfc⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨selected_subset I N w hfS, hfc⟩
  · intro hf
    obtain ⟨hfI, hfc⟩ := Finset.mem_filter.mp hf
    refine Finset.mem_filter.mpr ⟨(mem_selected I N w f).mpr ⟨hfI, ?_⟩, hfc⟩
    simpa only [oldTime, coarseTime, hfc] using htime

/-- This is PURE rescaling of the input δ-grid to σ=Nδ. At a fixed old height,
the existing actual shear-bin map is an integer translation in space, hence
injective. No larger independent thickening width is included. -/
lemma actualBin_fixed_height_injective (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (a b : Fin 3 → ℝ) {c d : Cell} (ht : c.2 = d.2)
    (hbin : ShearBinFibers.actualBin δ N a b c = ShearBinFibers.actualBin δ N a b d) : c = d := by
  apply Prod.ext
  · funext j
    have h := congrFun (congrArg Prod.fst hbin) j
    rw [ShearBinFibers.actualBin_space δ hδ N hN a b c j,
      ShearBinFibers.actualBin_space δ hδ N hN a b d j, ht] at h
    omega
  · exact ht

lemma actualBin_injective_on_selected (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (w : T × Cell → ℕ) (δ : ℝ) (hδ : 0 < δ) (a b : Fin 3 → ℝ) :
    Set.InjOn (ShearBinFibers.actualBin δ N a b) (↑(oldCells (selected I N w)) : Set Cell) := by
  intro c hc d hd hbin
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hd
  have hq : coarseTime N e = coarseTime N f := by
    have h := congrArg Prod.snd hbin
    simpa only [ShearBinFibers.actualBin_time δ hδ N hN, coarseTime, oldTime] using h
  have heq := ((mem_selected I N w e).mp he).2
  have hfq := ((mem_selected I N w f).mp hf).2
  have ht : e.2.2 = f.2.2 := heq.trans ((congrArg (chosenHeight I N w) hq).trans hfq.symm)
  exact actualBin_fixed_height_injective δ hδ N hN a b ht hbin

/-- Every occupied new time layer has one recoverable genuine original height,
common to all of its points and tubes. -/
lemma selected_original_height (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (w : T × Cell → ℕ) (δ : ℝ) (hδ : 0 < δ) (a b : Fin 3 → ℝ)
    (e : T × Cell) (he : e ∈ selected I N w) :
    oldTime e = chosenHeight I N w (ShearBinFibers.actualBin δ N a b e.2).2 := by
  rw [ShearBinFibers.actualBin_time δ hδ N hN]
  exact ((mem_selected I N w e).mp he).2

lemma bins_support_eq (I : Finset (T × Cell)) (f : Cell → Cell) :
    oldCells (bins I f) = (oldCells I).image f := by
  simp only [oldCells, bins, Finset.image_image]
  rfl

/-- Both incidence and spatial image counts are exact after the single global
old-height choice. There is no second N-sized fiber loss. -/
theorem selected_image_cardinalities (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (w : T × Cell → ℕ) (δ : ℝ) (hδ : 0 < δ) (a b : Fin 3 → ℝ) :
    (bins (selected I N w) (ShearBinFibers.actualBin δ N a b)).card = (selected I N w).card ∧
      (oldCells (bins (selected I N w) (ShearBinFibers.actualBin δ N a b))).card =
        (oldCells (selected I N w)).card := by
  have hinj := actualBin_injective_on_selected I N hN w δ hδ a b
  constructor
  · apply Finset.card_image_of_injOn
    intro e he f hf hlabel
    apply Prod.ext
    · simpa only [binLabel] using congrArg (fun q : T × Cell => q.1) hlabel
    · exact hinj (Finset.mem_image_of_mem Prod.snd he) (Finset.mem_image_of_mem Prod.snd hf)
        (congrArg Prod.snd hlabel)
  · rw [bins_support_eq]
    exact Finset.card_image_of_injOn hinj

def multiplicity (I : Finset (T × Cell)) : ℝ := (I.card : ℝ) / (oldCells I).card

lemma usedTubes_bins_eq (I : Finset (T × Cell)) (f : Cell → Cell) :
    usedTubes (bins I f) = usedTubes I := by
  simp only [usedTubes, bins, Finset.image_image]
  rfl

lemma selected_multiplicity_eq (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (w : T × Cell → ℕ) (δ : ℝ) (hδ : 0 < δ) (a b : Fin 3 → ℝ) :
    multiplicity (bins (selected I N w) (ShearBinFibers.actualBin δ N a b)) =
      multiplicity (selected I N w) := by
  obtain ⟨hI, hP⟩ := selected_image_cardinalities I N hN w δ hδ a b
  simp only [multiplicity, hI, hP]

/-- The N loss is canceled by σ=Nδ for TOTAL shading density, on the entire
original backbone, including empty rows. This alone makes no multiplicity claim. -/
theorem density_original_backbone (I : Finset (T × Cell)) (B : Finset T)
    (hused : usedTubes I ⊆ B) (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ)
    (a b : Fin 3 → ℝ) (lam : ℝ) (hdensity : lam * B.card ≤ δ * I.card) :
    usedTubes (bins (selected I N (fun _ => 1)) (ShearBinFibers.actualBin δ N a b)) ⊆ B ∧
      lam * B.card ≤ ((N : ℝ) * δ) *
        (bins (selected I N (fun _ => 1)) (ShearBinFibers.actualBin δ N a b)).card := by
  constructor
  · rw [usedTubes_bins_eq]
    exact (Finset.image_subset_image (selected_subset I N (fun _ => 1))).trans hused
  · have hc := (selected_image_cardinalities I N hN (fun _ => 1) δ hδ a b).1
    rw [hc]
    have hr : (I.card : ℝ) ≤ (N : ℝ) * (selected I N (fun _ => 1)).card := by
      exact_mod_cast height_card_retention I N hN
    calc
      lam * B.card ≤ δ * I.card := hdensity
      _ ≤ δ * ((N : ℝ) * (selected I N (fun _ => 1)).card) := mul_le_mul_of_nonneg_left hr hδ.le
      _ = ((N : ℝ) * δ) * (selected I N (fun _ => 1)).card := by ring

lemma multiplicity_le_of_cross (I J : Finset (T × Cell)) (K : ℝ) (hK : 0 ≤ K)
    (hcross : (I.card : ℝ) * (oldCells J).card ≤ K * J.card * (oldCells I).card)
    (hne : I.Nonempty → J.Nonempty) : multiplicity I ≤ K * multiplicity J := by
  by_cases hI : I.Nonempty
  · have hJ := hne hI
    have hPI : (0 : ℝ) < (oldCells I).card := by exact_mod_cast Finset.card_pos.mpr (hI.image Prod.snd)
    have hPJ : (0 : ℝ) < (oldCells J).card := by exact_mod_cast Finset.card_pos.mpr (hJ.image Prod.snd)
    dsimp [multiplicity]
    rw [← mul_div_assoc]
    exact (div_le_div_iff₀ hPI hPJ).mpr hcross
  · have hIeq : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    rw [show multiplicity I = 0 by simp [multiplicity, hIeq, oldCells]]
    exact mul_nonneg hK (by unfold multiplicity; positivity)

/-- Whole-point-fiber retention transfers an ACTUAL old point-degree comparison.
This is the direct multiplicity mechanism; density normalization is not used. -/
theorem point_comparison_cross (I : Finset (T × Cell)) (N K : ℕ) (w : T × Cell → ℕ)
    (hpoint : ∀ c d, c ∈ oldCells I → d ∈ oldCells I →
      (I.filter (fun e => e.2 = c)).card ≤ K * (I.filter (fun e => e.2 = d)).card) :
    I.card * (oldCells (selected I N w)).card ≤
      K * (selected I N w).card * (oldCells I).card := by
  let S := selected I N w
  have hsub : oldCells S ⊆ oldCells I := Finset.image_subset_image (selected_subset I N w)
  have hsumI : I.card = ∑ c ∈ oldCells I, (I.filter (fun e => e.2 = c)).card :=
    Finset.card_eq_sum_card_image Prod.snd I
  have hsumS : S.card = ∑ c ∈ oldCells S, (I.filter (fun e => e.2 = c)).card := by
    calc
      S.card = ∑ c ∈ oldCells S, (S.filter (fun e => e.2 = c)).card :=
        Finset.card_eq_sum_card_image Prod.snd S
      _ = _ := Finset.sum_congr rfl (fun c hc => by rw [selected_point_fiber I N w c hc])
  have hrow : ∀ c ∈ oldCells S,
      I.card ≤ K * (I.filter (fun e => e.2 = c)).card * (oldCells I).card := by
    intro c hc
    calc
      I.card = ∑ d ∈ oldCells I, (I.filter (fun e => e.2 = d)).card := hsumI
      _ ≤ ∑ _d ∈ oldCells I, K * (I.filter (fun e => e.2 = c)).card :=
        Finset.sum_le_sum (fun d hd => hpoint d c hd (hsub hc))
      _ = _ := by simp [Nat.mul_comm]
  calc
    I.card * (oldCells S).card = ∑ _c ∈ oldCells S, I.card := by simp [Nat.mul_comm]
    _ ≤ ∑ c ∈ oldCells S, K * (I.filter (fun e => e.2 = c)).card * (oldCells I).card :=
      Finset.sum_le_sum hrow
    _ = K * (∑ c ∈ oldCells S, (I.filter (fun e => e.2 = c)).card) * (oldCells I).card := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = K * S.card * (oldCells I).card := by rw [← hsumS]

/-- N-free multiplicity transfer under actual point-degree comparison.
The incidence domain is genuine pairs (tube, old spatial cell), not duplicated marks. -/
theorem point_comparison_multiplicity (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (K : ℕ) (δ : ℝ) (hδ : 0 < δ) (a b : Fin 3 → ℝ)
    (hpoint : ∀ c d, c ∈ oldCells I → d ∈ oldCells I →
      (I.filter (fun e => e.2 = c)).card ≤ K * (I.filter (fun e => e.2 = d)).card) :
    multiplicity I ≤ (K : ℝ) *
      multiplicity (bins (selected I N (fun _ => 1)) (ShearBinFibers.actualBin δ N a b)) := by
  rw [selected_multiplicity_eq I N hN (fun _ => 1) δ hδ a b]
  apply multiplicity_le_of_cross I (selected I N (fun _ => 1)) K (by positivity)
  · exact_mod_cast point_comparison_cross I N K (fun _ => 1) hpoint
  · intro hI
    apply Finset.card_pos.mp
    have hret := height_card_retention I N hN
    have hpos := Finset.card_pos.mpr hI
    by_contra hn
    have hz : (selected I N (fun _ => 1)).card = 0 := by omega
    rw [hz, Nat.mul_zero] at hret
    omega

/-- Physical heavy-bin preparation followed by an optional final original-label
refinement of cost C and THEN one global old-height choice. This ordering allows
all old grain/height classes to be prepared before their whole chosen-height
fibers are retained. The ORIGINAL backbone B is unchanged, including empty rows.

Multiplicity uses the already proved heavy-support gain and density threshold.
It does not claim that σ=Nδ alone cancels N in raw multiplicity. The input grid
mesh is P.δ after any prior thickening; no additional spatial thickening fibers,
point movement, or native-shading reconstruction are asserted here. -/
theorem physical_original_height_transfer
    (P : PhysicalRescalingIncidenceTransfer.Data T) (h : P.Hypotheses)
    (J : Finset (T × Cell)) (C : ℕ) (hJ : J ⊆ P.keptIncidences)
    (hretain : P.keptIncidences.card ≤ C * J.card)
    (B : Finset T) (hused : usedTubes P.incidences ⊆ B)
    (hdensity : P.lam * B.card ≤ P.δ * P.incidences.card) :
    let S := selected J P.N (fun _ => 1)
    let New := bins S P.cellBin
    S ⊆ P.incidences ∧ usedTubes New ⊆ B ∧
      New.card = S.card ∧ (oldCells New).card = (oldCells S).card ∧
      P.lam * B.card ≤ 2 * (C : ℝ) * P.σ * New.card ∧
      P.oldMultiplicity ≤ (C : ℝ) * (P.transferConstant / P.lam) * multiplicity New := by
  classical
  let S := selected J P.N (fun _ => 1)
  let New := bins S P.cellBin
  have hSkept : S ⊆ P.keptIncidences := (selected_subset J P.N (fun _ => 1)).trans hJ
  have hSI : S ⊆ P.incidences := hSkept.trans (kept_subset _ _ _)
  have hcards : New.card = S.card ∧ (oldCells New).card = (oldCells S).card :=
    selected_image_cardinalities J P.N h.N_pos (fun _ => 1) P.δ h.delta_pos P.globalSlope P.globalOffset
  have hrows : usedTubes New ⊆ B := by
    rw [usedTubes_bins_eq]
    exact (Finset.image_subset_image hSI).trans hused
  have htotal : P.incidences.card ≤ 2 * C * P.N * New.card := by
    rw [hcards.1]
    calc
      P.incidences.card ≤ 2 * P.keptIncidences.card := P.half_mass h
      _ ≤ 2 * (C * J.card) := Nat.mul_le_mul_left 2 hretain
      _ ≤ 2 * (C * (P.N * S.card)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left C (height_card_retention J P.N h.N_pos))
      _ = 2 * C * P.N * S.card := by ring
  have hnewSub : oldCells New ⊆ P.newSupport := by
    have hb : bins S P.cellBin ⊆ P.newIncidences := by
      rw [← P.retained_bins_exact]
      exact Finset.image_subset_image hSkept
    exact Finset.image_subset_image hb
  have hgain : P.m * (oldCells New).card ≤ P.oldSupport.card := by
    calc
      P.m * (oldCells New).card ≤ P.m * P.newSupport.card := Nat.mul_le_mul_left _ (Finset.card_le_card hnewSub)
      _ ≤ (oldCells P.keptIncidences).card := P.support_gain
      _ ≤ P.oldSupport.card := Finset.card_le_card (Finset.image_subset_image (kept_subset _ _ _))
  have htotalR : (P.incidences.card : ℝ) ≤ 2 * (C : ℝ) * P.N * New.card := by exact_mod_cast htotal
  have hden : P.lam * B.card ≤ 2 * (C : ℝ) * P.σ * New.card := by
    calc
      P.lam * B.card ≤ P.δ * P.incidences.card := hdensity
      _ ≤ P.δ * (2 * (C : ℝ) * P.N * New.card) := mul_le_mul_of_nonneg_left htotalR h.delta_pos.le
      _ = 2 * (C : ℝ) * P.σ * New.card := by dsimp [PhysicalRescalingIncidenceTransfer.Data.σ]; ring
  have hcrossNat : P.m * P.incidences.card * (oldCells New).card ≤
      2 * C * P.N * New.card * P.oldSupport.card := by
    calc
      P.m * P.incidences.card * (oldCells New).card = P.incidences.card * (P.m * (oldCells New).card) := by ring
      _ ≤ (2 * C * P.N * New.card) * P.oldSupport.card := Nat.mul_le_mul htotal hgain
      _ = _ := rfl
  have hcrossR : (P.m : ℝ) * P.incidences.card * (oldCells New).card ≤
      2 * (C : ℝ) * P.N * New.card * P.oldSupport.card := by exact_mod_cast hcrossNat
  have hN : (0 : ℝ) < P.N := by exact_mod_cast h.N_pos
  have hcrossDensity : P.lam * P.incidences.card * (oldCells New).card ≤
      (C : ℝ) * P.transferConstant * New.card * P.oldSupport.card := by
    apply (mul_le_mul_iff_right₀ hN).mp
    calc
      (P.N : ℝ) * (P.lam * P.incidences.card * (oldCells New).card) =
          (P.lam * P.N) * ((P.incidences.card : ℝ) * (oldCells New).card) := by ring
      _ ≤ (2 * P.K * P.m) * ((P.incidences.card : ℝ) * (oldCells New).card) :=
        mul_le_mul_of_nonneg_right P.density_le_threshold (by positivity)
      _ = (2 * P.K) * ((P.m : ℝ) * P.incidences.card * (oldCells New).card) := by ring
      _ ≤ (2 * P.K) * (2 * (C : ℝ) * P.N * New.card * P.oldSupport.card) :=
        mul_le_mul_of_nonneg_left hcrossR (mul_nonneg (by norm_num) P.K_pos.le)
      _ = (P.N : ℝ) * ((C : ℝ) * P.transferConstant * New.card * P.oldSupport.card) := by
        dsimp [PhysicalRescalingIncidenceTransfer.Data.transferConstant]
        ring
  have hconstant : 0 ≤ (C : ℝ) * P.transferConstant / P.lam := by
    have ht : 0 ≤ P.transferConstant := by
      exact mul_nonneg (by norm_num) P.K_pos.le
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg C) ht) h.lambda_pos.le
  have hcross : (P.incidences.card : ℝ) * (oldCells New).card ≤
      ((C : ℝ) * P.transferConstant / P.lam) * New.card * P.oldSupport.card := by
    apply (mul_le_mul_iff_right₀ h.lambda_pos).mp
    calc
      P.lam * ((P.incidences.card : ℝ) * (oldCells New).card) =
          P.lam * P.incidences.card * (oldCells New).card := by ring
      _ ≤ (C : ℝ) * P.transferConstant * New.card * P.oldSupport.card := hcrossDensity
      _ = P.lam * (((C : ℝ) * P.transferConstant / P.lam) * New.card * P.oldSupport.card) := by
        field_simp [ne_of_gt h.lambda_pos]
  have hmu : multiplicity P.incidences ≤ ((C : ℝ) * P.transferConstant / P.lam) * multiplicity New := by
    apply multiplicity_le_of_cross P.incidences New _ hconstant hcross
    intro hI
    apply Finset.card_pos.mp
    have hIpos := Finset.card_pos.mpr hI
    by_contra hn
    have hz : New.card = 0 := by omega
    rw [hz, Nat.mul_zero] at htotal
    omega
  refine ⟨hSI, hrows, hcards.1, hcards.2, hden, ?_⟩
  change multiplicity P.incidences ≤ _
  convert hmu using 1
  ring

end OriginalHeightRescaling
