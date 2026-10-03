import Theorems.Thm_StickyKakeya4_original_height_rescaling
import Theorems.Thm_StickyKakeya4_padded_rescaling_cubical_source

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

noncomputable section
open Classical SelfUniform IncidenceBinTransfer

namespace ShiftedOriginalHeightRescaling

abbrev Cell := OriginalHeightRescaling.Cell
variable {T : Type*}

/-- A genuine bijection of fine grid indices. Spatial and tube labels stay fixed. -/
def timeShift (c : ℤ) : Cell ≃ Cell where
  toFun p := (p.1, p.2 + c)
  invFun p := (p.1, p.2 - c)
  left_inv p := by simp
  right_inv p := by simp

def labelShift (c : ℤ) : (T × Cell) ≃ (T × Cell) :=
  Equiv.prodCongr (Equiv.refl T) (timeShift c)

def translated (I : Finset (T × Cell)) (c : ℤ) : Finset (T × Cell) :=
  I.map (labelShift c).toEmbedding

def translatedWeight (w : T × Cell → ℕ) (c : ℤ) (e : T × Cell) : ℕ :=
  w ((labelShift c).symm e)

@[simp] theorem translated_card (I : Finset (T × Cell)) (c : ℤ) :
    (translated I c).card = I.card := Finset.card_map _

@[simp] theorem translated_mass (I : Finset (T × Cell)) (w : T × Cell → ℕ) (c : ℤ) :
    mass (translatedWeight w c) (translated I c) = mass w I := by
  simp [mass, translated, translatedWeight]

@[simp] theorem labelShift_tube (c : ℤ) (e : T × Cell) : (labelShift c e).1 = e.1 := rfl
@[simp] theorem labelShift_time (c : ℤ) (e : T × Cell) :
    OriginalHeightRescaling.oldTime (labelShift c e) = OriginalHeightRescaling.oldTime e + c := rfl

def timeBin (N : ℕ) (c : ℤ) (e : T × Cell) : ℤ :=
  (OriginalHeightRescaling.oldTime e + c) / (N : ℤ)

/-- The selected ORIGINAL height is recovered by subtracting the global shift. -/
def chosenHeight (I : Finset (T × Cell)) (N : ℕ) (c : ℤ) (w : T × Cell → ℕ) (q : ℤ) : ℤ :=
  OriginalHeightRescaling.chosenHeight (translated I c) N (translatedWeight w c) q - c

/-- Apply the existing selector once in translated coordinates, then pull every
selected incidence back through the exact inverse bijection. -/
def selected (I : Finset (T × Cell)) (N : ℕ) (c : ℤ) (w : T × Cell → ℕ) : Finset (T × Cell) :=
  (OriginalHeightRescaling.selected (translated I c) N (translatedWeight w c)).map
    (labelShift c).symm.toEmbedding

@[simp] theorem mem_selected (I : Finset (T × Cell)) (N : ℕ) (c : ℤ)
    (w : T × Cell → ℕ) (e : T × Cell) :
    e ∈ selected I N c w ↔ e ∈ I ∧
      OriginalHeightRescaling.oldTime e = chosenHeight I N c w (timeBin N c e) := by
  simp only [selected, Finset.mem_map_equiv, Equiv.symm_symm,
    OriginalHeightRescaling.mem_selected, translated, Finset.mem_map_equiv,
    Equiv.symm_apply_apply, labelShift_time]
  dsimp only [chosenHeight, timeBin, OriginalHeightRescaling.coarseTime]
  rw [labelShift_time]
  exact and_congr_right (fun _ => (eq_sub_iff_add_eq).symm)

theorem selected_subset (I : Finset (T × Cell)) (N : ℕ) (c : ℤ) (w : T × Cell → ℕ) :
    selected I N c w ⊆ I := fun _ he => ((mem_selected I N c w _).mp he).1

theorem selected_mass (I : Finset (T × Cell)) (N : ℕ) (c : ℤ) (w : T × Cell → ℕ) :
    mass w (selected I N c w) = mass (translatedWeight w c)
      (OriginalHeightRescaling.selected (translated I c) N (translatedWeight w c)) := by
  simp [mass, selected, translatedWeight]

/-- Translation costs no mass; the single height choice still loses at most N. -/
theorem weighted_height_retention (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (c : ℤ) (w : T × Cell → ℕ) : mass w I ≤ N * mass w (selected I N c w) := by
  rw [selected_mass]
  simpa only [translated_mass] using
    OriginalHeightRescaling.weighted_height_retention (translated I c) N hN (translatedWeight w c)

theorem height_card_retention (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N) (c : ℤ) :
    I.card ≤ N * (selected I N c (fun _ => 1)).card := by
  simpa only [mass, Finset.sum_const, smul_eq_mul, Nat.mul_one] using
    weighted_height_retention I N hN c (fun _ => 1)

theorem chosenHeight_bin (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (c : ℤ) (w : T × Cell → ℕ) (q : ℤ) :
    (chosenHeight I N c w q + c) / (N : ℤ) = q := by
  simpa only [chosenHeight, sub_add_cancel] using
    OriginalHeightRescaling.chosenHeight_bin (translated I c) N hN (translatedWeight w c) q

/-- The final bin keeps all original incidence labels at its chosen original height. -/
theorem selected_bin_fiber (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (c : ℤ) (w : T × Cell → ℕ) (q : ℤ) :
    (selected I N c w).filter (fun e => timeBin N c e = q) =
      OriginalHeightRescaling.atHeight I (chosenHeight I N c w q) := by
  ext e
  simp only [Finset.mem_filter, mem_selected, OriginalHeightRescaling.atHeight]
  constructor
  · rintro ⟨⟨he, hz⟩, hq⟩
    exact ⟨he, by simpa only [hq] using hz⟩
  · rintro ⟨he, hz⟩
    have hq : timeBin N c e = q := by
      dsimp only [timeBin]
      rw [hz]
      exact chosenHeight_bin I N hN c w q
    exact ⟨⟨he, by simpa only [hq] using hz⟩, hq⟩

/-- Whole point-incidence fibers survive, including every original tube row. -/
theorem selected_point_fiber (I : Finset (T × Cell)) (N : ℕ) (c : ℤ)
    (w : T × Cell → ℕ) (p : Cell) (hp : p ∈ oldCells (selected I N c w)) :
    (selected I N c w).filter (fun e => e.2 = p) = I.filter (fun e => e.2 = p) := by
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
  have hz := ((mem_selected I N c w e).mp he).2
  ext f
  constructor
  · intro hf
    obtain ⟨hfS, hfp⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨selected_subset I N c w hfS, hfp⟩
  · intro hf
    obtain ⟨hfI, hfp⟩ := Finset.mem_filter.mp hf
    refine Finset.mem_filter.mpr ⟨(mem_selected I N c w f).mpr ⟨hfI, ?_⟩, hfp⟩
    simpa only [OriginalHeightRescaling.oldTime, timeBin, hfp] using hz

/-- The original shear spatial index and the final translated time-bin index.
Only time is relabelled; its spatial shear uses the genuine original height. -/
def shiftedBin (δ : ℝ) (N : ℕ) (a b : Fin 3 → ℝ) (c : ℤ) (p : Cell) : Cell :=
  ((ShearBinFibers.actualBin δ N a b p).1, (p.2 + c) / (N : ℤ))

/-- Explicit conjugation by the fine-index bijection. -/
theorem shiftedBin_eq_translated_triangular (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (a b : Fin 3 → ℝ) (c : ℤ) (p : Cell) :
    shiftedBin δ N a b c p = ShearBinFibers.triangularBin N
      (fun z => ShearBinFibers.shearShift δ a b (z - c)) (timeShift c p) := by
  apply Prod.ext
  · funext j
    simp only [shiftedBin, ShearBinFibers.actualBin_space δ hδ N hN,
      ShearBinFibers.triangularBin, timeShift, Equiv.coe_fn_mk, add_sub_cancel_right]
  · rfl

theorem shiftedBin_injective_on_selected (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (c : ℤ) (w : T × Cell → ℕ) (δ : ℝ) (hδ : 0 < δ) (a b : Fin 3 → ℝ) :
    Set.InjOn (shiftedBin δ N a b c) (↑(oldCells (selected I N c w)) : Set Cell) := by
  intro p hp r hr hbin
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hr
  have hq : timeBin N c e = timeBin N c f := congrArg Prod.snd hbin
  have heq := ((mem_selected I N c w e).mp he).2
  have hfq := ((mem_selected I N c w f).mp hf).2
  have ht : e.2.2 = f.2.2 := heq.trans ((congrArg (chosenHeight I N c w) hq).trans hfq.symm)
  apply OriginalHeightRescaling.actualBin_fixed_height_injective δ hδ N hN a b ht
  apply Prod.ext
  · simpa only [shiftedBin] using congrArg (fun p : Cell => p.1) hbin
  · simp only [ShearBinFibers.actualBin_time δ hδ N hN, ht]

/-- Exact image counts for pure shifted rescaling. Native additional spatial
coarsening is separate and is not asserted to be injective. -/
theorem selected_image_cardinalities (I : Finset (T × Cell)) (N : ℕ) (hN : 0 < N)
    (c : ℤ) (w : T × Cell → ℕ) (δ : ℝ) (hδ : 0 < δ) (a b : Fin 3 → ℝ) :
    (bins (selected I N c w) (shiftedBin δ N a b c)).card = (selected I N c w).card ∧
      (oldCells (bins (selected I N c w) (shiftedBin δ N a b c))).card =
        (oldCells (selected I N c w)).card := by
  have hinj := shiftedBin_injective_on_selected I N hN c w δ hδ a b
  constructor
  · apply Finset.card_image_of_injOn
    intro e he f hf hlabel
    apply Prod.ext
    · simpa only [binLabel] using congrArg (fun p : T × Cell => p.1) hlabel
    · exact hinj (Finset.mem_image_of_mem Prod.snd he) (Finset.mem_image_of_mem Prod.snd hf)
        (congrArg Prod.snd hlabel)
  · rw [OriginalHeightRescaling.bins_support_eq]
    exact Finset.card_image_of_injOn hinj

/-- No additional N loss occurs when the shifted index is used at the outset. -/
theorem density_original_backbone (I : Finset (T × Cell)) (B : Finset T)
    (hused : usedTubes I ⊆ B) (N : ℕ) (hN : 0 < N) (c : ℤ) (δ : ℝ) (hδ : 0 < δ)
    (a b : Fin 3 → ℝ) (lam : ℝ) (hdensity : lam * B.card ≤ δ * I.card) :
    usedTubes (bins (selected I N c (fun _ => 1)) (shiftedBin δ N a b c)) ⊆ B ∧
      lam * B.card ≤ ((N : ℝ) * δ) *
        (bins (selected I N c (fun _ => 1)) (shiftedBin δ N a b c)).card := by
  constructor
  · rw [OriginalHeightRescaling.usedTubes_bins_eq]
    exact (Finset.image_subset_image (selected_subset I N c (fun _ => 1))).trans hused
  · rw [(selected_image_cardinalities I N hN c (fun _ => 1) δ hδ a b).1]
    have hr : (I.card : ℝ) ≤ (N : ℝ) * (selected I N c (fun _ => 1)).card := by
      exact_mod_cast height_card_retention I N hN c
    calc
      lam * B.card ≤ δ * I.card := hdensity
      _ ≤ δ * ((N : ℝ) * (selected I N c (fun _ => 1)).card) := mul_le_mul_of_nonneg_left hr hδ.le
      _ = ((N : ℝ) * δ) * (selected I N c (fun _ => 1)).card := by ring

/-- Nested floor maps combine exactly, including negative original times. -/
theorem shifted_nested_time (z q : ℤ) (N C : ℕ) (hN : 0 < N) :
    (z / (N : ℤ) + q) / (C : ℤ) = (z + (N : ℤ) * q) / ((N * C : ℕ) : ℤ) := by
  rw [Nat.cast_mul, ← Int.ediv_ediv_of_nonneg (show (0 : ℤ) ≤ N by omega)]
  rw [Int.add_mul_ediv_left _ _ (show (N : ℤ) ≠ 0 by omega)]

open StickyKakeya4

/-- Exact connection to the native padded cubical source: its fine map is the
encoded physical bin, and its final time map is a shifted ORIGINAL time floor. -/
theorem native_coarse_time {n : ℕ} (P : PhysicalRescalingIncidenceTransfer.Data (Fin n))
    (hδ : 0 < P.δ) (hN : 0 < P.N) (R q : ℕ) (p : Cell) :
    PaddedRescalingCubicalSource.coarse P R q p (Fin.last 3) =
      (p.2 + (P.N : ℤ) * (q : ℤ)) / ((P.N * (64 * R) : ℕ) : ℤ) := by
  simp only [PaddedRescalingCubicalSource.coarse, PaddedRescalingCubicalSource.fine,
    PaddedRescalingCubicalSource.encode, Fin.lastCases_last,
    PhysicalRescalingIncidenceTransfer.Data.cellBin, ShearBinFibers.actualBin_time P.δ hδ P.N hN]
  exact shifted_nested_time p.2 q P.N (64 * R) hN

/-- Choose padding first, then apply one global height choice to the FINAL time
bins. Original incidence labels and tube labels are retained unchanged. The
single loss is (64R)N; it is not a second N loss after an earlier height choice.
The input I can be the source's actual retained set after global padding. -/
theorem native_final_height_selection {n : ℕ}
    (P : PhysicalRescalingIncidenceTransfer.Data (Fin n)) (hδ : 0 < P.δ) (hN : 0 < P.N)
    (R q : ℕ) (hR : 0 < R) (I : Finset (Fin n × Cell)) (w : Fin n × Cell → ℕ) :
    let M := P.N * (64 * R)
    let c := (P.N : ℤ) * (q : ℤ)
    let S := selected I M c w
    S ⊆ I ∧ mass w I ≤ M * mass w S ∧
      ∀ k : ℤ, S.filter (fun e => PaddedRescalingCubicalSource.coarse P R q e.2 (Fin.last 3) = k) =
        OriginalHeightRescaling.atHeight I (chosenHeight I M c w k) := by
  dsimp only
  have hM : 0 < P.N * (64 * R) := Nat.mul_pos hN (Nat.mul_pos (by norm_num) hR)
  refine ⟨selected_subset I _ _ w, weighted_height_retention I _ hM _ w, ?_⟩
  intro k
  calc
    _ = (selected I (P.N * (64 * R)) ((P.N : ℤ) * (q : ℤ)) w).filter
        (fun e => timeBin (P.N * (64 * R)) ((P.N : ℤ) * (q : ℤ)) e = k) := by
      ext e
      simp only [Finset.mem_filter, native_coarse_time P hδ hN R q,
        timeBin, OriginalHeightRescaling.oldTime]
      constructor
      · intro he
        exact Finset.mem_filter.mpr he
      · intro he
        exact Finset.mem_filter.mp he
    _ = _ := selected_bin_fiber I (P.N * (64 * R)) hM ((P.N : ℤ) * (q : ℤ)) w k

/-- Every selected final native layer has one common genuine original-height
witness, recovered from the translated maximizer by subtracting P.N*q. -/
theorem native_selected_original_height {n : ℕ}
    (P : PhysicalRescalingIncidenceTransfer.Data (Fin n)) (hδ : 0 < P.δ) (hN : 0 < P.N)
    (R q : ℕ) (I : Finset (Fin n × Cell)) (w : Fin n × Cell → ℕ)
    (e : Fin n × Cell)
    (he : e ∈ selected I (P.N * (64 * R)) ((P.N : ℤ) * (q : ℤ)) w) :
    OriginalHeightRescaling.oldTime e =
      chosenHeight I (P.N * (64 * R)) ((P.N : ℤ) * (q : ℤ)) w
        (PaddedRescalingCubicalSource.coarse P R q e.2 (Fin.last 3)) := by
  rw [native_coarse_time P hδ hN R q]
  exact ((mem_selected I _ _ w e).mp he).2

end ShiftedOriginalHeightRescaling
